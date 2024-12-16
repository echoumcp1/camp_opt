import Final.Basic
import Final.Infra

open Expr
open Ty
open Stmt

def program1 :=
  [
    label "entry",
    asgn "$0" (malloc i32 16),
    asgn "$1" (gep (pointer i32) "$0" 32),
    store i32 120 "$1",
    free "$0",
    asgn "$2" (gep (pointer i32) "$0" 1),
    store i32 121 "$2"
  ]

def program2 :=
  [
    label "entry",
    asgn "$0" (malloc (struct [i32, i32]) (sizeof (struct [i32, i32]))),
    asgn "$1" (gep (struct [pointer i32]) "$0" 0),
    store i32 1 "$1",
    asgn "$2" (gep (struct [pointer i32]) "$0" 4),
    store i32 2 "$2"
  ]

def program3 :=
  [
    label "entry",
    asgn "$0" (malloc (struct [pointer i32]) 100),
    asgn "$1" (gep (struct [pointer i32]) "$0" 0),
    asgn "$2" (gep (pointer i32) "$1" 100),
    store i32 120 "$2", -- ptr->mem[100] = 'x'
    asgn "$3" (alloca i1),
    store i1 1 "$3",
    br_cond "$3" "if.true" "end",
    label "if.true",
    asgn "$4" (gep (pointer i32) "$1" 30),
    store i32 121 "$4", -- ptr->mem[30] = 'y'
    asgn "$5" (gep (pointer i32) "$1" 1),
    store i32 121 "$5", -- ptr->mem[1] = 'y'
    br "end",
    label "end",
    asgn "$6" (gep (pointer i32) "$1" 1),
    store i32 122 "$6" -- ptr->mem[1] = 'z'
  ]

#eval (instrument program1)
#eval (instrument program2)
#eval (instrument program3)
