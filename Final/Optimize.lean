import Lean
import «Final».Infra

open Expr
open Stmt
open Ty
open Block

def get_new_ptr_set
  (prog : List Stmt)
  : List Expr :=

  let rec get_result_ptrs
    (e : Expr)
    : List Expr :=
    (match e with
    | gep ty base offset => [gep ty base offset]
    | _ => [])

  match prog with
  | [] => []
  | stmt::stmts =>
    let res_ptr :=
    match stmt with
    | asgn _ e => get_result_ptrs e
    | _ => []
    res_ptr ++ get_new_ptr_set stmts

def init_ptr_map
  (result_ptrs : List Expr)
  (assoc_list : Lean.AssocList String (List Expr))
  : List (String × (List Expr)) :=
  match result_ptrs with
  | [] => assoc_list.toList
  | ptr::ptrs =>
    let base := get_base ptr
    let assoc_list := match assoc_list.find? base with
    | none => assoc_list.insert base [ptr]
    | some v => assoc_list.replace base (if v.elem ptr then v else ptr::v)
    init_ptr_map ptrs assoc_list

def pred
  (cfg : CFG)
  (node : String)
  : List String :=
  cfg.foldr (fun (BBlock lab _ children) acc => if children.contains node then lab::acc else acc) []


def create_cfgs (prog : List Stmt) : CFG × CFG :=
  let rec init_pass
    (prog : List Stmt)
    (curr_block : List Stmt)
    : List Block :=
    match prog with
    | [] => [BBlock "" curr_block.reverse []]
    | stmt::stmts =>
      match stmt with
      | br lab => (BBlock "" (stmt::curr_block).reverse [lab])::init_pass stmts []
      | br_cond _ t_branch f_branch => (BBlock "" (stmt::curr_block).reverse [t_branch, f_branch])::init_pass stmts []
      | stmt => init_pass stmts (stmt::curr_block)

  let blocks := (init_pass prog [])

  let forward := List.map
    (fun (BBlock _ block children) =>
      match block with
      | (label lab)::_ => BBlock lab block children
      | _ => BBlock "" block children -- impossible case
    ) blocks
  let backward := (forward.map
    (fun (BBlock lab block _) =>
      BBlock lab block (pred forward lab)
    )).reverse

  (forward, backward)

def compute_doms (cfg : CFG) :=
  let node_set := cfg.map (fun (BBlock lab _ _) => lab)
  let work_list :=
    match node_set.head? with
    | none => []
    | some v => [v]
  let doms := (node_set.map (fun n => (n, node_set))).toAssocList'

  let succ
    (node : String)
    : List String :=
    match cfg.find? (fun (BBlock lab _ _) => lab = node) with
    | none => []
    | some (BBlock _ _ children) => children

  let rec fix
    (work_list : List String)
    (dominators : Lean.AssocList String (List String))
    (fuel : Nat)
    : Lean.AssocList String (List String) :=
    match work_list, fuel with
    | [], _ | _, 0 => dominators
    | node::nodes, Nat.succ n =>
      let pred_doms :=
        ((pred cfg node).foldr
          (fun pred acc =>
            match dominators.find? pred with
            | none => acc
            | some doms =>
              match acc with
              | [] => doms
              | _ => doms.filter (fun dom => List.elem dom acc)
          ) [])
      let new_doms := (if pred_doms.elem node then pred_doms else node::pred_doms)
      let dom_y :=
        match dominators.find? node with
        | none => []
        | some dom_y => dom_y
      match dom_y.removeAll new_doms with
      | [] => fix nodes dominators n
      | _ => let new_dominators := dominators.replace node new_doms
             let new_work_list := ((succ node).foldr (fun succ acc => if List.elem succ acc then acc else succ::acc) nodes).reverse
             fix new_work_list new_dominators n
  (fix work_list doms node_set.length).mapVal (fun labs => labs.map (fun lab => cfg.find? (fun (BBlock lab' _ _) => lab == lab')))

def remove_redundant (prog : List Stmt) : List Expr :=
  let to_pairs
    (ptr_map : List (String × (List Expr)))
    : List (String × Expr) :=
    (ptr_map.map (fun (k, v) => v.map (fun e => (k, e)))).join

  let in_map := init_ptr_map (get_new_ptr_set prog) Lean.AssocList.nil
  let out_map : Lean.AssocList String (List Expr) := Lean.AssocList.nil
  let change_set := to_pairs in_map
  let (forward, backward) := create_cfgs prog
  let (dom, postdom) := (compute_doms forward, compute_doms backward)
  let num_ptrs := in_map.foldr (fun (_, v) acc => acc + v.length) 0

  let is_redundant_pair
    (ptr1 : Expr)
    (ptr2 : Expr)
    : Bool :=
    let rec contains_ptr (ptr : Expr) (block : List Stmt) :=
      match block with
      | [] => false
      | stmt::stmts =>
          match stmt with
          | asgn _ e => if e == ptr then true else contains_ptr ptr stmts
          | _ => contains_ptr ptr stmts
    let rec find_first_occur (ptr : Expr) (cfg : CFG) :=
      match cfg with
      | [] => none
      | (BBlock lab code _)::nodes => if contains_ptr ptr code then some lab else find_first_occur ptr nodes

    let rec dominate
      (ptr1 : Expr)
      (ptr2 : Expr)
      (cfg : CFG)
      (dom_tree : Lean.AssocList String (List (Option Block)))
      : Bool :=
      match (find_first_occur ptr2 cfg) with
      | none => false
      | some node =>
          match (dom_tree.find? node) with
          | none => false
          | some dom_nodes =>
              (dom_nodes.map
                (fun node_opt =>
                  match node_opt with
                  | none => false
                  | some (BBlock _ code _) => contains_ptr ptr1 code
                )).any id
    (dominate ptr1 ptr2 forward dom || dominate ptr2 ptr1 forward dom ||
    dominate ptr1 ptr2 backward postdom || dominate ptr2 ptr1 backward postdom)

  let rec exists_redundant
    (ptrs : List Expr)
    : Option (Expr × Expr) :=
    match ptrs with
    | [] => none
    | ptr::ptrs =>
      let rec find_redundant : List Expr → Option Expr
      | [] => none
      | ptr'::ptrs => if is_redundant_pair ptr ptr' then some (ptr') else find_redundant ptrs
      match find_redundant ptrs with
      | none => exists_redundant ptrs
      | some other_ptr => some (ptr, other_ptr)

  let rec fix
    (in_map : List (String × List Expr))
    (out_map : Lean.AssocList String (List Expr))
    (change_set : List (String × Expr))
    (fuel : Nat)
    : Lean.AssocList String (List Expr) :=
    match change_set, fuel with
    | [], _  | _, 0 => out_map
    | _, Nat.succ n =>
      let new_out_map :=
        (in_map.foldr
          (fun (k, v) (acc : Lean.AssocList String (List Expr)) =>
            let out_val :=
              (match exists_redundant v with
              | none => v
              | some (ptr1, ptr2) =>
                let v' := v.removeAll [ptr1, ptr2]
                let new_ptr := replace_offset ptr1 (max (get_offset ptr1) (get_offset ptr2))
                new_ptr::v')
            match acc.find? k with
            | none => acc.insert k out_val
            | some _ => acc.replace k out_val
          )
        out_map).toList
      let change_set := (to_pairs in_map).removeAll (to_pairs new_out_map)
      fix new_out_map new_out_map.toAssocList' change_set n

  (to_pairs (fix in_map out_map change_set num_ptrs).toList).map (fun (_, v) => v)

def instrument
  (prog : List Stmt)
  : List Stmt :=
  let ptrs :=
    (remove_redundant prog).filter
      (fun e =>
        match e with
        | gep (struct _) _ _ => false
        | _ => true
      )
  let (cfg, _) := create_cfgs prog

  let rec go
    (prog : List Stmt)
    (instrumented : List Stmt)
    (seen : List Expr)
    : List Stmt :=
    match prog with
    | [] => instrumented.reverse
    | stmt::stmts =>
        match stmt with
        | asgn s (gep ty base offset) =>
            let ptr := (gep ty base offset)
            if ptrs.contains ptr && !seen.contains ptr then
              go stmts ((check_range base s (sizeof ty))::asgn s ptr::instrumented) (ptr::seen)
            else
              go stmts (asgn s ptr::instrumented) (ptr::seen)
        | asgn s (malloc ty sz) =>
            go stmts ((check_range s s (sizeof ty))::(asgn s (malloc ty sz))::instrumented) seen
        | stmt => go stmts (stmt::instrumented) seen
  let instrumented := cfg.map (fun (BBlock lab code children) => (BBlock lab (go code [] []) children))
  (instrumented.map (fun (BBlock _ code _) => code)).join
