open Support
open Support.Utils
open Types
open Lfun_shrink

let fresh = Utils.make_gensym ()

let uniquify_exp (env : var VarMap.t) (e : exp) : exp =
    let rec helper (m: var VarMap.t) (e: exp) : exp =
    match e with
    | Void -> Void
    | Bool b -> Bool b
    | Int n -> Int n 
    | VecLen atm -> VecLen (helper m atm)
    | Var v -> 
      (match VarMap.find_opt v m with
        | Some a -> Var a
        | _ -> Var v)
    | Prim(op, exps) -> Prim (op, List.map (helper m) exps)
    | SetBang(v, exp) -> 
      let v_mapping = VarMap.find v m in
      SetBang (v_mapping, helper m exp)
    | Begin (exps, exp) -> Begin (List.map (helper m) exps, helper m exp)
    | If (e1, e2, e3) -> 
      let new_e1 = helper m e1 in 
      let new_e2 = helper m e2 in
      let new_e3 = helper m e3 in
      If (new_e1, new_e2, new_e3)
    | Let (v, init, eval) ->
      let new_init = helper m init in
      let new_v = (fresh ~base:v ~sep:".") in
      let new_m = VarMap.add v new_v m in
      let new_eval = helper new_m eval in
      Let ( new_v, new_init, new_eval)
    | While (e1, e2) -> 
        let new_e1 = helper m e1 in 
        let new_e2 = helper m e2 in
        While (new_e1, new_e2)
    | Vec (exps, ty) -> Vec(List.map (helper m) exps, ty)
    | VecRef (exp, int) -> VecRef(helper m exp, int)
    | VecSet (vec, idx, exp) -> VecSet(helper m vec,idx, helper m exp)
    | Apply (exp, exps) -> Apply (helper m exp, List.map (helper m) exps)

  in
    helper env e 

let uniquify_def (Def (name, fcont)) =
  let {args; ret; body} = fcont in
  let names, tys = List.split args in
  (* We set up the name->name mapping environment here,
     which includes the function argument names. *)
  let names' = List.map (fun n -> fresh ~base:n ~sep:".") names in
  let env = VarMap.of_list (List.combine names names') in
  let args' = List.combine names' tys in
  let body' = uniquify_exp env body in
  Def (name, {args = args'; ret; body = body'})

let def_name (Def (name, _)) = name

(* Validation function.
   Make sure that each name is bound only once.
   Also check that all `set!` variables are bound. *)
let validate_exp (s : VarSet.t) (e : exp) : unit =
  let rec aux (s : VarSet.t) (e : exp) : VarSet.t =
    match e with
    | Void | Bool _ | Int _ | Var _ ->
        s
    | Prim (_, es) ->
        List.fold_left aux s es
    | SetBang (v, e) ->
        if not (VarSet.mem v s) then
          failwithf "uniquify: validate: unbound variable %s in set! form" v
        else aux s e
    | Begin (es, e) ->
        List.fold_left aux s (es @ [e])
    | If (e1, e2, e3) ->
        List.fold_left aux s [e1; e2; e3]
    | While (e1, e2) ->
        List.fold_left aux s [e1; e2]
    | Let (v, e1, e2) ->
        if VarSet.mem v s then
          failwithf "uniquify: validate: variable %s bound more than once" v
        else
          let s1 = VarSet.add v s in
          List.fold_left aux s1 [e1; e2]
    | Vec (es, _) ->
        List.fold_left aux s es
    | VecLen e | VecRef (e, _) ->
        aux s e
    | VecSet (e1, _, e2) ->
        List.fold_left aux s [e1; e2]
    | Apply (e, es) ->
        List.fold_left aux s (e :: es)
  in
  let _ = aux s e in
  ()

let validate_def (d : def) : unit =
  let (Def (name, fcont)) = d in
  let {args; body; _} = fcont in
  let names, _ = List.split args in
  let s = VarSet.of_list names in
  if VarSet.cardinal s <> List.length names then
    failwithf
      "uniquify: validate: argument names are not unique for function %s" name
  else validate_exp s body

let uniquify (Program ds) =
  let names = List.map def_name ds in
  (* We check that there are no repeated function names,
   * including `main`.  We could have done this check before,
   * but it's convenient to do it here, since all function names
   * (including `main`) are at the same level.
   * We do _not_ change these names. *)
  if no_string_repeats names then
    let ds' = List.map uniquify_def ds in
    begin
      List.iter validate_def ds' ; Program ds'
    end
  else failwith "uniquify: repeated function names at top level"
