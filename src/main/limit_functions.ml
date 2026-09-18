open Support.Utils
open Types
open Lfun_ref

let fresh = make_gensym ()

(* Function to create new names for the new tuple variables. *)
let new_tup_var () = fresh ~base:"$tup" ~sep:"."

(* Global set of function names whose argument counts have changed. *)
let limited_names = ref VarSet.empty

(* Record type containing information about extra arguments. *)
type extra_args = {
  tup_name : var;           (* name of extra argument tuple *)
  argc     : int;           (* number of extra arguments *)
  argnums  : int VarMap.t;  (* tuple index of extra arguments *)
}

(* An `extra_args` record returned when there are no extra arguments. *)
let no_extra_args = { tup_name = ""; argc = 0; argnums = VarMap.empty }

(* Convert types to new function type representation,
   with a maximum of 6 arguments. 
   This affects all types that are function types
   or can include function types (like vectors). *)
let rec limit_type (t : ty) : ty =
  match t with 
  | Unit -> Unit 
  | Boolean -> Boolean 
  | Integer -> Integer 
  | Vector lst -> Vector (Array.map limit_type lst)
  | Function (tys, t) -> 
    if (List.length tys) >= 5 then
      let first_five = take 5 tys in
      Function ((List.map limit_type first_five) @ [limit_type (Vector (Array.of_list (drop 5 tys)))], t)
    else 
      Function (tys, t)

(* Change the argument declaration of a function
   to take extra arguments into account. *)
let limit_args (ex : extra_args) (args : (var * ty) list) : (var * ty) list =
  let transform_args = List.map (fun (var, ty) ->
    let new_type = limit_type ty in
    (var, new_type)
    ) args 
  in
  let { tup_name ; argc ; _} = ex in
  if argc > 0 then
    let (_, t_list) = List.split transform_args
    in
      (take 5 args) @ [(tup_name, Vector (Array.of_list (drop 5 t_list)))]
  else 
    transform_args


(* Change the body of a function to account for the extra arguments
   of the function. Variable references for extra arguments
   must be changed to vector references. `Apply` expressions
   also must be changed if there are more than 6 arguments,
   which involves creating a new vector.
   Note: You don't need to specify the type of this vector here;
   that will be handled in the next type checking pass. *)
let limit_functions_exp (ex : extra_args) (e : exp) : exp =
  (* Need to account for Apply functions as well *)
  let { tup_name ; argc = _ ; argnums } = ex in
   let conv (e : exp) : exp =
    match e with
      | Var a ->
        (match VarMap.find_opt a argnums with
        | None -> Var a 
        | Some count -> VecRef (Var tup_name, count))
      | Apply (e1, exps) -> 
        if List.length exps > 6 then 
          Apply (e1, (take 5 exps) @ [ Vec (drop 5 exps, None)])
        else
          Apply (e1, exps)
      | _ -> e
  in
    convert_exp conv e
  

(* Create the `extra_args` record from the argument list. *)
let get_extra_args (args : (var * ty) list) : extra_args * bool =
  let (_, argnums) =
  List.fold_left (fun (count, map) (var, _) ->
    if count >= 5 then 
      let extra_args = VarMap.add var (count - 5) map in
      (count + 1, extra_args)
    else
      (count + 1, map)
    ) (0, (VarMap.empty : int VarMap.t)) args 
  in
    if VarMap.cardinal argnums > 0 then
      ({ tup_name = new_tup_var (); argc = VarMap.cardinal argnums; argnums }, true)
    else 
      (no_extra_args, false)

let limit_function_def (d : def) : def =
  let (Def (name, fcont)) = d in
  let { args; ret; body } = fcont in
  let (ex, has_extra_args) = get_extra_args args in
  let _ =
    if has_extra_args then
      limited_names :=
        VarSet.add (string_of_label name) !limited_names
  in
  let body' = limit_functions_exp ex body in
  let args' = limit_args ex args in
  let ret'  = limit_type ret in
  let fcont' = { args = args'; ret = ret'; body = body' } in
    Def (name, fcont')

(* Update all `FunRef` arities for functions that have been limited. *)
let fix_fun_refs (d : def) : def =
  let (Def (a , fcont)) = d in
  let { args; body; ret } = fcont in
  let conv (e : exp) : exp =
    (* Replace function *)
    (match e with
      | FunRef ((Label lbl), arities) -> 
          if VarSet.mem lbl !limited_names then 
            FunRef((Label lbl), 6)
          else
            FunRef((Label lbl), arities)
      | _ -> e)
  in 
  let updates_functions = convert_exp conv body in
  Def(a, {args ; body = updates_functions ; ret } )

(* Validation function.
   - Check that no function definition has more than 6 arguments.
   - Check that FunRef arities are <= 6.
   - Check that Apply expressions have no more than 6 arguments. *)
let validate_def (d : def) : unit =
  let (Def (_, fcont)) = d in
  let { args; body; _ } = fcont in
  let conv (e : exp) : exp =
    match e with
      | FunRef (_, i) ->
          if i < 0 || i > 6 then
            failwithf "validate_def: invalid FunRef arity: %d" i
          else
            e
      | Apply (_, es) ->
          if List.length es > 6 then
            failwithf "validate_def: too many arguments to Apply: %d"
              (List.length es)
          else
            e
      | _ -> e
  in
    begin
      assert (List.length args <= 6);
      ignore (convert_exp conv body)
    end

let limit_functions (Program defs) =
  let _ = limited_names := VarSet.empty in
  let defs'  = List.map limit_function_def defs in
  let defs'' = List.map fix_fun_refs defs' in
  let _ = List.iter validate_def defs'' in
    Program defs''

