open Types
open Lfun_ref_alloc_get
module L = Lfun_ref_alloc
module S = VarSet

let rec collect_set_vars (e : L.exp) : S.t =
  let fold_exps exps : S.t = 
    List.fold_left ( fun acc exp ->
        S.union acc (collect_set_vars exp)
    ) S.empty exps
  in
  match e with
    | SetBang(v, exp) -> 
      S.add v (collect_set_vars exp)
    | Prim(_, exps) -> fold_exps exps
    | Begin (exps, exp) -> 
      let set_from_list = fold_exps exps
      in 
        S.union set_from_list (collect_set_vars exp)
    | If (_, e1, e2) -> 
      S.union (collect_set_vars e1) (collect_set_vars e2)
    | Let (_, e1, e2) ->
      S.union (collect_set_vars e1) (collect_set_vars e2)  
    | While (e1, e2) -> 
      S.union (collect_set_vars e1) (collect_set_vars e2)
    | _ -> S.empty 

let rec uncover_get_exp (s : S.t) (e : L.exp) : exp =
  match e with
  | Void -> Void
  | Bool b -> Bool b
  | Int n -> Int n 
    | Collect int -> Collect int
  | Allocate (int, ty) ->  Allocate (int, ty)
  | Var v -> 
    if S.mem v s then 
      GetBang (S.find v s)
    else 
      Var v
  | Prim(op, exps) -> Prim (op, List.map (uncover_get_exp s) exps)
  | SetBang(v, exp) -> SetBang (v, uncover_get_exp s exp)
  | Begin (exps, exp) -> Begin (List.map (uncover_get_exp s) exps, uncover_get_exp s exp)
  | If (e1, e2, e3) -> 
    let new_e1 = uncover_get_exp s e1 in 
    let new_e2 = uncover_get_exp s e2 in
    let new_e3 = uncover_get_exp s e3 in
    If (new_e1, new_e2, new_e3)
  | Let (v, init, eval) ->
    let new_init = uncover_get_exp s init in
    let new_eval = uncover_get_exp s eval in
    Let ( v, new_init, new_eval)
  | While (e1, e2) -> 
    let new_e1 = uncover_get_exp s e1 in 
    let new_e2 = uncover_get_exp s e2 in
    While (new_e1, new_e2)
  | GlobalVal v -> GlobalVal v 
  | VecLen exp -> VecLen (uncover_get_exp s exp)
  | VecRef (exp, int) -> VecRef ((uncover_get_exp s exp), int)
  | VecSet (vec, int, exp) -> VecSet ((uncover_get_exp s vec), int, (uncover_get_exp s exp))
  | FunRef (lbl, int) -> FunRef (lbl, int)
  | Apply (exp, exps ) -> Apply (uncover_get_exp s exp, List.map (uncover_get_exp s) exps)


let uncover_get_def (s : S.t) (ldef : L.def) : def =
  let (L.Def (name, { args; ret; body })) = ldef in
  let body' = uncover_get_exp s body in
    Def (name, { args; ret; body = body' })

let uncover_get (L.Program ds) =
  let (set_vars : S.t) =
    List.fold_left
      (fun (s : S.t) (d : L.def) ->
         let (L.Def (_, fc)) = d in
           S.union s (collect_set_vars fc.body))
      S.empty
      ds
  in
    Program (List.map (uncover_get_def set_vars) ds)
