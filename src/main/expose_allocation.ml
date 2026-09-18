open Support
open Lfun_ref_alloc
module L = Lfun_ref

let fresh = Utils.make_gensym ()
let new_var () = fresh ~base:"$ea" ~sep:"."
let new_void_var () = fresh ~base:"_" ~sep:"."

let is_atom (e : exp) : bool =
  match e with
  | Bool _-> true
  | Int _ -> true
  | Var _ -> true 
  | Void -> true
  | _ -> false

type exp_or_arg = [
  | `Atom of exp
  | `VarExp of string * exp
]

let rec convert_exp (e : L.exp) =
  match e with 
  | L.Void -> Void
  | L.Bool bool -> Bool bool
  | L.Int int -> Int int
  | L.Var var -> Var var
  | L.FunRef (lbl, int) -> FunRef (lbl, int)
  | L.VecLen atm -> VecLen (convert_exp atm)
  | L.Vec (exps, t) -> 
    let e' = List.map convert_exp exps in
    expose_vec e' t
  | L.Let (v, e1, e2) ->
    let e1_recurse = convert_exp e1  in
    let e2_recurse = convert_exp e2 in
   Let (v, e1_recurse, e2_recurse)
  | L.While (e1, e2) -> 
    let new_e1 = convert_exp e1 in 
    let new_e2 = convert_exp e2 in
     While (new_e1, new_e2)
  | L.VecRef (exp, int) -> VecRef(convert_exp exp, int)
  | L.VecSet (vec, idx, exp) ->
    let vec_1 = convert_exp vec in
    let exp_1 = convert_exp exp in
    VecSet(vec_1,idx, exp_1)
  | L.Prim(op, exps) -> Prim (op, List.map convert_exp exps)
  | L.SetBang(v, exp) -> 
      SetBang (v, convert_exp exp)
  | L.Begin (exps, exp) -> 
    let mapped_exps = List.map convert_exp exps in
    Begin (mapped_exps, convert_exp exp)
  | L.If (e1, e2, e3) -> 
      let new_e1 = convert_exp e1 in 
      let new_e2 = convert_exp e2 in
      let new_e3 = convert_exp e3 in
      If (new_e1, new_e2, new_e3)
  |L.Apply (e1, exps) -> 
    Apply (convert_exp e1, List.map convert_exp exps)
and expose_vec exps t : exp = 
  let convert_to_poly (e: exp) : exp_or_arg = 
      if is_atom e then
        `Atom e
      else
        `VarExp (new_var (), e)
      in
  let seperated_exps = List.map convert_to_poly exps in
  let len = List.length exps in
  let nbytes = 8 * (len + 1) in
  let add = Prim (`Add, [(GlobalVal "free_ptr"); (Int nbytes)]) in
  let first_exp = Prim (`Lt, [add ; (GlobalVal "fromspace_end")]) in
  let if_statement = If (first_exp, Void, Collect nbytes) in
  let vector_name = new_var () in
  let new_sets = 
    List.mapi (fun i exp ->
      match exp with 
      |`VarExp (x, _) -> VecSet ((Var vector_name), i, Var x)
      |`Atom e -> VecSet((Var vector_name), i, e)
    ) seperated_exps
  in
  let vector_sets = 
    List.fold_right (fun set acc ->
      Let (new_void_var () , set, acc)
      ) new_sets (Var vector_name)
  in
  let final_sets = 
    (match t with 
    | Some a -> Let(vector_name, Allocate (len ,a),vector_sets)
    | None -> failwith "Error: No type found") 
  in
    List.fold_right(fun exp acc ->
      match exp with 
      |`VarExp (var, exp) -> Let (var, exp, acc)
      |`Atom _ -> acc
    ) seperated_exps (Let (new_void_var (), if_statement, final_sets))
let expose_allocation_exp (e : L.exp) : exp =
  convert_exp e

let expose_allocation_def (ldef : L.def) =
  let (Def (name, { args; ret; body })) = ldef in
  let body'  = expose_allocation_exp body in
  let fcont' = { args; ret; body = body' } in
    Def (name, fcont')

let expose_allocation (L.Program ds) =
  Program (List.map expose_allocation_def ds)
