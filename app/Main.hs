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

import           Data.Char                      ( toLower )
import           Data.Fix                       ( foldFixM )
import           Data.Functor.Foldable          ( cata
                                                , refix
                                                )
import           Data.Functor.Foldable.TH       ( MakeBaseFunctor(makeBaseFunctor) )
import           Data.List                      ( intercalate )
import           Data.Text.Lazy.IO             as T
import           LLVM.AST.Operand               ( Operand(ConstantOperand) )
import           LLVM.AST.Type                  ( i32
                                                , i8
                                                , ptr
                                                )
import           LLVM.IRBuilder                 ( ModuleBuilder
                                                , buildModule
                                                , call
                                                , function
                                                , globalStringPtr
                                                , int32
                                                , ret
                                                )
import qualified LLVM.IRBuilder                as LLVM
import           LLVM.IRBuilder.Module          ( externVarArgs )
import           LLVM.Pretty                    ( ppllvm )
import           System.Directory               ( removeFile
                                                , renameFile
                                                )
import           System.Process                 ( callProcess )
data Type = Int | Void
    deriving (Show)

data Exp = Lit Int | Add Exp Exp | Print Exp
    deriving (Show)

makeBaseFunctor ''Exp

type family ExpPrint a :: b
type instance ExpPrint Exp = Exp
type instance ExpPrint Type = Type
type instance ExpPrint String = String
type instance ExpPrint Int = IO ()

class Eval a where
    lit :: Int -> a
    add :: a -> a -> a
    printing :: a -> ExpPrint a

instance Eval Int where
    lit      = id
    add      = (+)
    printing = print

instance Eval String where
    lit = show
    add a b = "(" ++ a ++ "+" ++ b ++ ")"
    printing = id

instance Eval Exp where
    lit      = Lit
    add      = Add
    printing = Print

instance Eval Type where
    lit = const Int
    add Int Int = Int
    add _   _   = error "add: not a integer"
    printing Int = Void
    printing _   = error "printing: not a integer"


-- >>> printing @Exp (add (lit 1) (lit 2))
-- Print (Add (Lit 1) (Lit 2))

-- >>> printing @Type (add (lit 1) (lit 2))
-- Void

-- >>> printing @Int (add (lit 1) (lit 2))
-- output 3

-- >>> printing @String (add (lit 1) (add (lit 3) (lit 4)))
-- "(1+(3+4))"

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

codegen :: Exp -> [Instruction]
codegen = (++ exiting) . (header ++) . cata go
  where
    go :: ExpF [Instruction] -> [Instruction]
    go (LitF i  ) = [mov rax (imm i)]
    go (AddF a b) = a ++ [push rax] ++ b ++ [mov rbx rax, pop rax, addi rax rbx]
    go (PrintF ins) =
        [mov rsi rsp] -- record stack bottom
            ++ ins
            ++ convertNumberToString
            ++ [mov rbx rsi]
            ++ printingNumber

codegenLLIR :: Exp -> ModuleBuilder Operand
codegenLLIR exp = mdo
    fmt      <- globalStringPtr "%d\n" "fmt"
    printf   <- externVarArgs "printf" [ptr i8] i32
    addition <- function "add" [(i32, "a"), (i32, "b")] i32 $ \[a, b] -> mdo
        c <- LLVM.add a b
        ret c
    function "main" [] i32 $ \_ -> mdo
        foldFixM (go (addition, printf, ConstantOperand fmt)) (refix exp)
        ret (int32 0)
  where
    go p                   (LitF i  ) = return $ int32 (fromIntegral i)
    go p@(ad, _     , _  ) (AddF a b) = call ad [(a, []), (b, [])]
    go (  _ , printf, fmt) (PrintF i) = call printf [(fmt, []), (i, [])]

-- >>> codegen (printing @Exp (add (lit 1) (lit 2)))
-- [Global "_start",Section Text,Label "_start",Mov (Reg RSI) (Reg RSP),Mov (Reg RAX) (Imm 1),Push (Reg RAX),Mov (Reg RAX) (Imm 2),Mov (Reg RBX) (Reg RAX),Pop (Reg RAX),AddI (Reg RAX) (Reg RBX),Mov (Reg RBX) (Reg RSI),Label "convert",Xor (Reg RDX) (Reg RDX),Mov (Reg RBX) (Imm 10),DivI (Reg RBX),AddI (Reg RDX) (Imm 48),Push (Reg RDX),Test (Reg RAX) (Reg RAX),Jnz (LabelRef "convert"),Mov (Reg RBX) (Reg RSI),Label "printLoop",Cmp (Reg RSP) (Reg RBX),Jg (LabelRef "printLoopEnd"),Mov (Reg RAX) (Imm 1),Mov (Reg RDI) (Imm 1),Mov (Reg RSI) (Reg RSP),Mov (Reg RDX) (Imm 1),Syscall,Pop (Reg RAX),Jmp (LabelRef "printLoop"),Label "printLoopEnd",Pop (Reg RAX),Mov (Reg RAX) (Imm 60),Xor (Reg RDI) (Reg RDI),Syscall]

-- >>> error $ outputInstruction $ codegen (printing @Exp (add (add (add (lit 7) (lit 8)) (lit 4)) (add (lit 5) (lit 6))))


main :: IO ()
main = do
    -- writeFile "gen.asm" (outputInstruction (codegen (printing @Exp (add (add (add (lit 7) (lit 8)) (lit 4)) (add (lit 5) (lit 6))))))
    T.writeFile "test.ll" $ ppllvm $ buildModule
        "exampleModule"
        (codegenLLIR (printing @Exp (add (lit 12) (add (add (add (lit 7) (lit 8)) (lit 4)) (add (lit 5) (lit 6))))))
    callProcess "env" ["opt", "-O2", "test.ll", "-o", "test.bc"]
    callProcess "env" ["clang", "test.bc"]
    removeFile "test.ll"
    removeFile "test.bc"
    renameFile "a.out" "./test-exe"
