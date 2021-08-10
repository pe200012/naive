{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE OverloadedStrings #-}
module Main where

import           Control.Monad.Writer.Lazy      ( Writer
                                                , runWriter
                                                , tell
                                                )
import           Data.Char                      ( toLower )
import           Data.Fix                       ( Fix(Fix)
                                                , foldFixM
                                                )
import           Data.Functor.Foldable          ( cata
                                                , para
                                                , refix
                                                )
import           Data.Functor.Foldable.TH       ( MakeBaseFunctor(makeBaseFunctor) )
import           Data.List                      ( intercalate )
import           LLVM.AST.Operand               ( Operand(ConstantOperand) )
import           LLVM.AST.Type                  ( i32
                                                , i8
                                                , ptr
                                                )
import           LLVM.IRBuilder                 ( ModuleBuilder
                                                , call
                                                , function
                                                , globalStringPtr
                                                , int32
                                                , ret
                                                )
import qualified LLVM.IRBuilder                as LLVM
import           LLVM.IRBuilder.Module          ( externVarArgs )
import           System.Directory               ( removeFile
                                                , renameFile
                                                )
import           System.Process                 ( callProcess )

data DeBruijn = Here
              | Before DeBruijn
              deriving (Eq)

makeBaseFunctor ''DeBruijn

-- >>> show Here
-- "O"
--
-- >>> show (Before Here)
-- "S(O)"
--
-- >>> show (Before (Before Here))
-- "S(S(O))"
instance Show DeBruijn where
    show = cata go
      where
        go HereF       = "O"
        go (BeforeF i) = "S(" ++ i ++ ")"

instance Ord DeBruijn where
    Here     <= x        = True
    x        <= Here     = False
    Before a <= Before b = a <= b

naturalSize :: DeBruijn -> Int
naturalSize = cata phi
  where
    phi HereF       = 0
    phi (BeforeF i) = succ i

data Type = Int
          | Void
          | Type :-> Type
    deriving (Show, Eq)

data Exp = Lit Int
         | Unit
         | Add Exp Exp
         | Print Exp
         | Fun Type Exp
         | App Exp Exp
         | Var DeBruijn
    deriving (Show)

makeBaseFunctor ''Exp

lit = Lit
unit = Unit
add = Add
printing = Print
fun = Fun
app = App
var = Var
here = Here
before = Before

-- |
-- >>> typeof $ lit 1
-- Just Int
--
-- >>> typeof $ add (lit 1) (lit 2)
-- Just Int
--
-- >>> typeof $ printing (lit 1)
-- Just Void
--
-- >>> typeof $ fun Int (var here)
-- Just (Int :-> Int)
--
-- >>> typeof $ fun Int (fun Int (add (var here) (var $ before here)))
-- Just (Int :-> (Int :-> Int))
--
-- >>> typeof $ app (fun Int (var here)) (lit 42)
-- Just Int

typeof :: Exp -> Maybe Type
typeof = ($ []) . cata go
  where
    go (LitF _)   = const (Just Int)
    go UnitF      = const (Just Void)
    go (AddF a b) = \cxt -> do
        a' <- a cxt
        b' <- b cxt
        case (a', b') of
            (Int, Int) -> return Int
            _          -> Nothing
    go (PrintF a) = \cxt -> case a cxt of
        Just Int -> return Void
        _        -> Nothing
    go (FunF t a) = fmap (t :->) . a . (t :)
    go (AppF a b) = \cxt -> do
        a' <- a cxt
        b' <- b cxt
        case a' of
            ty :-> ty' | ty == b' -> return ty'
            _                     -> Nothing
    go (VarF i) = \cxt -> case drop (naturalSize i) cxt of
        []      -> Nothing
        (x : _) -> return x

-- >>> runWriter $ interpretPure $ lit 1
-- (Lit 1,[])
--
-- >>> runWriter $ interpretPure $ add (lit 1) (lit 2)
-- (Lit 3,[])
--
-- >>> runWriter $ interpretPure $ printing (add (lit 30) (lit 12))
-- (Unit,[42])
-- >>> runWriter $ interpretPure $ (fun Void (printing (lit 2)) )
-- (Fun Void (Print (Lit 2)),[])
--
-- >>> runWriter $ interpretPure $ app (fun Void (printing (lit 2)) ) (printing (lit 1))
-- (Unit,[1,2])
--
-- >>> runWriter $ interpretPure $ app (printing (lit 1)) (lit 2)
-- (App (Print (Lit 1)) (Lit 2),[])

interpretPure :: Exp -> Writer [Int] Exp
interpretPure = (maybe . return <*> (const . para interpret)) <*> typeof
  where
    interpret :: ExpF (Exp, Writer [Int] Exp) -> Writer [Int] Exp
    interpret (LitF x)             = return $ lit x
    interpret UnitF                = return unit
    interpret (AddF (l, a) (r, b)) = do
        a' <- a
        b' <- b
        case (a', b') of
            (Lit a'', Lit b'') -> return $ lit (a'' + b'')
            _                  -> return $ add l r
    interpret (PrintF (t, x1)) = do
        x <- x1
        case x of
            Lit x' -> tell [x'] >> return unit
            _      -> return $ printing t
    interpret (FunF ty      (t, _ )) = return $ fun ty t
    interpret (AppF (l, x1) (r, x2)) = do
        x <- x1
        y <- x2
        case x of
            Fun _ b -> interpretPure $ shift (-1) 0 (subst (0, shift 1 0 y) b)
            _       -> return $ app l r
    interpret (VarF db) = return $ var db

shift :: Int -> Int -> Exp -> Exp
shift i c t = cata shift' t i c
  where
    shift' (LitF x)   = \_ _ -> lit x
    shift' UnitF      = \_ _ -> unit
    shift' (AddF a b) = \i c -> add (a i c) (b i c)
    shift' (PrintF a) = (.) printing . a
    shift' (FunF t a) = \i c -> fun t (a i (succ c))
    shift' (AppF a b) = \i c -> app (a i c) (b i c)
    shift' (VarF x  ) = \i c -> if naturalSize x < c then var x else var (inc i x)
    inc 0 x = x
    inc n x = inc (n - 1) (Before x)

subst :: (Int, Exp) -> Exp -> Exp
subst p t = cata subst' t p
  where
    subst' (LitF x)   = const $ lit x
    subst' UnitF      = const unit
    subst' (AddF a b) = add . a <*> b
    subst' (PrintF a) = printing . a
    subst' (FunF t a) = \(i, e) -> fun t (a (succ i, shift 1 0 e))
    subst' (AppF a b) = app . a <*> b
    subst' (VarF x  ) = \(i, e) -> if i == naturalSize x then e else var x


data Register = RAX
              | RBX
              | RCX
              | RDX
              | RSP
              | RBP
              | RSI
              | RDI
              | R8
              | R9
              | R10
              | R11
              | R12
              | R13
              | R14
              | R15
              deriving (Show)

data Instruction = Reg Register
                 | Imm Int
                 | Mov Instruction Instruction
                 | Xor Instruction Instruction
                 | DivI Instruction
                 | AddI Instruction Instruction
                 | Cmp Instruction Instruction
                 | Test Instruction Instruction
                 | Push Instruction
                 | Pop  Instruction
                 | Jmp  Instruction
                 | Jnz  Instruction
                 | Jg   Instruction
                 | CurrentInstruction
                 | RelativeOffset Instruction Instruction
                 | Peek Instruction
                 | Syscall
                 | Label String
                 | LabelRef String
                 | Global String
                 | Section SectionName
                 deriving (Show)

data SectionName = Text | Data | Bss deriving (Show)

makeBaseFunctor ''Instruction

singleInstruction :: Instruction -> String
singleInstruction = cata go
  where
    go (RegF r) = toLower <$> show r
    go (ImmF i) | i >= 0    = show i
                | otherwise = "(" ++ show i ++ ")"
    go (MovF a b )           = "        mov " ++ a ++ ", " ++ b
    go (XorF a b )           = "        xor " ++ a ++ ", " ++ b
    go (DivIF a  )           = "        div " ++ a
    go (AddIF a b)           = "        add " ++ a ++ ", " ++ b
    go (CmpF  a b)           = "        cmp " ++ a ++ ", " ++ b
    go (TestF a b)           = "        test " ++ a ++ ", " ++ b
    go (PushF a  )           = "        push " ++ a
    go (PopF  a  )           = "        pop " ++ a
    go (JmpF  a  )           = "        jmp " ++ a
    go (JnzF  a  )           = "        jnz " ++ a
    go (JgF   a  )           = "        jg " ++ a
    go SyscallF              = "        syscall"
    go (LabelF    s )        = s ++ ":"
    go (LabelRefF s )        = s
    go (GlobalF   s )        = "        global " ++ s
    go (SectionF  sn)        = "        section ." ++ (toLower <$> show sn)
    go CurrentInstructionF   = "$"
    go (RelativeOffsetF a b) = a ++ "+" ++ b
    go (PeekF a            ) = "[" ++ a ++ "]"

outputInstruction :: [Instruction] -> String
outputInstruction = intercalate "\n" . fmap singleInstruction

imm = Imm
mov = Mov
xor = Xor
divi = DivI
rax = Reg RAX
rbx = Reg RBX
rcx = Reg RCX
rdx = Reg RDX
rsi = Reg RSI
rsp = Reg RSP
rdi = Reg RDI
pop = Pop
push = Push
addi = AddI
label = Label
global = Global
test = Test
jmp = Jmp
jnz = Jnz
jg = Jg
labelRef = LabelRef
cmp = Cmp
syscall = Syscall
section = Section
offset = RelativeOffset
currentPos = CurrentInstruction
peek = Peek

header = [global "_start", section Text, label "_start"]

exiting = [mov rax (imm 60), xor rdi rdi, syscall]

convertNumberToString = [xor rdx rdx, mov rbx (imm 10), divi rbx, addi rdx (Imm (fromEnum '0')), push rdx, test rax rax, jnz (offset currentPos (imm (-19)))]

printingNumber =
    [ cmp rsp rbx
    , jg (offset currentPos (imm 25))
    , mov rax (imm 1)
    , mov rdi (imm 1)
    , mov rsi rsp
    , mov rdx (imm 1)
    , syscall
    , pop rax
    , jmp (offset currentPos (imm (-26)))
    ]

-- codegen :: Exp -> [Instruction]
-- codegen = (++ exiting) . (header ++) . cata go
--   where
--     go :: ExpF [Instruction] -> [Instruction]
--     go (LitF i  ) = [mov rax (imm i)]
--     go (AddF a b) = a ++ [push rax] ++ b ++ [mov rbx rax, pop rax, addi rax rbx]
--     go (PrintF ins) =
--         [mov rsi rsp] -- record stack bottom
--             ++ ins
--             ++ convertNumberToString
--             ++ [mov rbx rsi]
--             ++ printingNumber

-- codegenLLIR :: Exp -> ModuleBuilder Operand
-- codegenLLIR exp = mdo
--     fmt      <- globalStringPtr "%d\n" "fmt"
--     printf   <- externVarArgs "printf" [ptr i8] i32
--     addition <- function "add" [(i32, "a"), (i32, "b")] i32 $ \[a, b] -> mdo
--         c <- LLVM.add a b
--         ret c
--     function "main" [] i32 $ \_ -> mdo
--         foldFixM (go (addition, printf, ConstantOperand fmt)) (refix exp)
--         ret (int32 0)
--   where
--     go p                   (LitF i  ) = return $ int32 (fromIntegral i)
--     go p@(ad, _     , _  ) (AddF a b) = call ad [(a, []), (b, [])]
--     go (  _ , printf, fmt) (PrintF i) = call printf [(fmt, []), (i, [])]

-- >>> codegen (printing @Exp (add (lit 1) (lit 2)))
-- [Global "_start",Section Text,Label "_start",Mov (Reg RSI) (Reg RSP),Mov (Reg RAX) (Imm 1),Push (Reg RAX),Mov (Reg RAX) (Imm 2),Mov (Reg RBX) (Reg RAX),Pop (Reg RAX),AddI (Reg RAX) (Reg RBX),Mov (Reg RBX) (Reg RSI),Label "convert",Xor (Reg RDX) (Reg RDX),Mov (Reg RBX) (Imm 10),DivI (Reg RBX),AddI (Reg RDX) (Imm 48),Push (Reg RDX),Test (Reg RAX) (Reg RAX),Jnz (LabelRef "convert"),Mov (Reg RBX) (Reg RSI),Label "printLoop",Cmp (Reg RSP) (Reg RBX),Jg (LabelRef "printLoopEnd"),Mov (Reg RAX) (Imm 1),Mov (Reg RDI) (Imm 1),Mov (Reg RSI) (Reg RSP),Mov (Reg RDX) (Imm 1),Syscall,Pop (Reg RAX),Jmp (LabelRef "printLoop"),Label "printLoopEnd",Pop (Reg RAX),Mov (Reg RAX) (Imm 60),Xor (Reg RDI) (Reg RDI),Syscall]

-- >>> error $ outputInstruction $ codegen (printing @Exp (add (add (add (lit 7) (lit 8)) (lit 4)) (add (lit 5) (lit 6))))


-- main :: IO ()
-- main = do
    -- writeFile "gen.asm" (outputInstruction (codegen (printing @Exp (add (add (add (lit 7) (lit 8)) (lit 4)) (add (lit 5) (lit 6))))))
    -- T.writeFile "test.ll" $ ppllvm $ buildModule
        -- "exampleModule"
        -- (codegenLLIR (printing @Exp (add (lit 12) (add (add (add (lit 7) (lit 8)) (lit 4)) (add (lit 5) (lit 6))))))
    -- callProcess "env" ["opt", "-O2", "test.ll", "-o", "test.bc"]
    -- callProcess "env" ["clang", "test.bc"]
    -- removeFile "test.ll"
    -- removeFile "test.bc"
    -- renameFile "a.out" "./test-exe"

main :: IO ()
main = pure ()
