inductive Ty :=
| i32
| i1
| struct (fields : List Ty)
| pointer (typ : Ty)
| array (typ : Ty) (sz : Nat)
deriving Repr, BEq

inductive Expr :=
| num (n : Nat)
| malloc (ty : Ty) (sz : Nat)
| gep (ty : Ty) (base : String) (offset : Nat)
| load (ty : Ty) (ptr : String)
| alloca (ty : Ty)
deriving Repr, BEq

inductive Stmt :=
| label (lab : String)
| store (ty : Ty) (value : Nat) (var : String)
| asgn (e1 : String) (e2 : Expr)
| free (e : String)
| bitcast (e : String) (ty : Ty)
| check_range (base : String) (offset : String) (sz : Nat)
| escape (addr : Expr) (name : String)
| br (label : String)
| br_cond (cond : String) (t_branch : String) (f_branch : String)
deriving Repr, BEq

inductive Block
| BBlock (label : String) (code : List Stmt) (children : List String)
deriving Repr, BEq

abbrev CFG := List Block

open Expr
open Ty
open Stmt

def sizeof : Ty -> Nat
| i1 => 1
| i32 | pointer _ => 4
| struct fields => fold fields 0
| array ty sz => sizeof ty * sz
where fold : List Ty → Nat → Nat
  | [], n => n
  | (t :: ts), n => fold ts (sizeof t + n)

def replace_offset (ptr : Expr) (offset : Nat) : Expr :=
  match ptr with
  | gep ty base _ => gep ty base offset
  | _ => num 0 -- impossible case

def get_offset : Expr -> Nat
  | gep _ _ offset => offset
  | _ => 0 -- impossible case

def get_base : Expr -> String
  | gep _ base _ => base
  | _ => "impossible case"
