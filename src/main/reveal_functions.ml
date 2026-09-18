open Types
open Lfun_ref

module L = Lfun_shrink

let rec reveal_functions_exp (fmap: int VarMap.t) (e : L.exp) : exp =
  match e with
  | Void -> Void
  | Bool b -> Bool b
  | Int n -> Int n 
  | VecLen atm -> VecLen (reveal_functions_exp fmap atm)
  | Var v -> 
    (match VarMap.find_opt v fmap with
      | Some a -> FunRef ((Label v), a)
      | None -> Var v)
  | Prim(op, exps) -> Prim (op, List.map (reveal_functions_exp fmap) exps)
  | SetBang(v, exp) -> 
    SetBang (v, reveal_functions_exp fmap exp)
  | Begin (exps, exp) -> Begin (List.map (reveal_functions_exp fmap) exps, reveal_functions_exp fmap exp)
  | If (e1, e2, e3) -> 
    let new_e1 = reveal_functions_exp fmap e1 in 
    let new_e2 = reveal_functions_exp fmap e2 in
    let new_e3 = reveal_functions_exp fmap e3 in
    If (new_e1, new_e2, new_e3)
  | Let (v, init, eval) ->
    let new_init = reveal_functions_exp fmap init in
    let new_eval = reveal_functions_exp fmap eval in
    Let ( v, new_init, new_eval)
  | While (e1, e2) -> 
      let new_e1 = reveal_functions_exp fmap e1 in 
      let new_e2 = reveal_functions_exp fmap e2 in
      While (new_e1, new_e2)
  | Vec (exps, ty) -> Vec(List.map (reveal_functions_exp fmap) exps, ty)
  | VecRef (exp, int) -> VecRef(reveal_functions_exp fmap exp, int)
  | VecSet (vec, idx, exp) -> VecSet(reveal_functions_exp fmap vec,idx, reveal_functions_exp fmap exp)
  | Apply (exp, exps) -> Apply (reveal_functions_exp fmap exp, List.map (reveal_functions_exp fmap) exps)

let reveal_functions_def (fmap : int VarMap.t) (ldef : L.def) : def =
  let (L.Def (name, { args; ret; body } )) = ldef in
  let body'  = reveal_functions_exp fmap body in
  let fcont' = { args; ret; body = body' } in
    Def (Label name, fcont')

let get_name_arity (ldef : L.def) : var * int =
  let (L.Def (name, fcont)) = ldef in
  let args = fcont.args in
    (name, List.length args)

let reveal_functions (L.Program ds) =
  (* Extract all the function names and arities,
   * compute a map, and call `reveal_functions_def`
   * on the body of each definition. *)
  let fmap =
    VarMap.of_list (List.map get_name_arity ds)
  in
    Program (List.map (reveal_functions_def fmap) ds)
