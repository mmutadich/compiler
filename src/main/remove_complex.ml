open Support
open Types
open Lfun_ref_mon

module L = Lfun_ref_alloc_get

let fresh = Utils.make_gensym ()
let gen_temp_name () = fresh ~base:"$tmp" ~sep:"."
(* A special name for binding to forms that return `Void`. *)
let temp_void_name = "$_"


(* Nest let-bindings 
 * take in list of var exp pairs and expressions
 * returns a let-binding expression *)
let rec nest_let (bindings : (var * exp) list) (body : exp) : exp =
  match bindings with
  | [] -> body
  | (v, e) :: rest -> 
      Let (v, e, nest_let rest body)

(* Flatten let-bindings 
 * take in an expression
 * returns a list of var exp pairs and an atomic expression *)
let rec flatten_let (exp : exp) : (var * exp) list * atm =
  match exp with
  | Let (v, e1, body) ->
      let rest, atm = flatten_let body in
      ((v, e1) :: rest, atm)
  | Atm atm -> ([], atm)
  | _ ->
      let tmp = gen_temp_name () in
      ([(tmp, exp)], Var tmp)

(* Convert an expression which needs to become atomic.
 * Return the atomic expression as well as a list of
 * names bound to complex operands. *)
let rec rco_atom (e : L.exp) : ((var * exp) list) * atm =
  match e with
  | L.Int n -> ([], Int n)
  | L.Bool b -> ([], Bool b)
  | L.Var x -> ([], Var x)
  | L.GetBang x ->
    let tmp = gen_temp_name () in
    ([(tmp, Atm (Var x))], Var tmp)
  | L.Void ->
    ([], Void)
  | L.SetBang (v, e1) ->
    let e1' = rco_exp e1 in
    let binds, atm = flatten_let e1' in
    ([(temp_void_name, nest_let binds (SetBang (v, Atm atm)))], Void)
  | L.While (cond, body) ->
    let cond_binds, cond_atm = rco_atom cond in
    let body' = rco_exp body in
    let while_e = nest_let cond_binds (While (Atm cond_atm, body')) in
    ([(temp_void_name, while_e)], Void)
  | L.Begin (exps, last) ->
    let be = Begin (List.map rco_exp exps, rco_exp last) in
    let tmp = gen_temp_name () in
    ([(tmp, be)], Var tmp)
  | L.Collect n ->
    ([(temp_void_name, Collect n)], Void)
  | L.Allocate (i, ty) ->
    let tmp = gen_temp_name () in
    ([(tmp, Allocate (i, ty))], Var tmp)
  | L.GlobalVal v ->
    let tmp = gen_temp_name () in
    ([(tmp, GlobalVal v)], Var tmp)
  | L.VecLen e1 ->
    let binds, atm = rco_atom e1 in
    let tmp = gen_temp_name () in
    (binds @ [(tmp, VecLen atm)], Var tmp)
  | L.VecRef (e1, i) ->
    let binds, atm = rco_atom e1 in
    let tmp = gen_temp_name () in
    (binds @ [(tmp, VecRef (atm, i))], Var tmp)
  | L.VecSet (e1, i, e2) ->
    let b1, a1 = rco_atom e1 in
    let b2, a2 = rco_atom e2 in
    ([(temp_void_name, nest_let (b1 @ b2) (VecSet (a1, i, a2)))], Void)
  | L.FunRef (lbl, i) ->
    let tmp = gen_temp_name () in
    ([(tmp, FunRef (lbl, i))], Var tmp)
  | L.Apply (f, args) ->
    let arg_pair = List.map rco_atom args in
    let arg_bind = List.concat (List.map fst arg_pair) in
    let arg_atms = List.map snd arg_pair in
    let f_bind, f_atm = rco_atom f in
    let tmp = gen_temp_name () in
    (f_bind @ arg_bind @ [(tmp, Apply (f_atm, arg_atms))], Var tmp)
  | _ ->
      flatten_let (rco_exp e)

and rco_exp (e : L.exp) : exp =
  match e with
  | L.Int n -> Atm (Int n)
  | L.Var x -> Atm (Var x)
  | L.Bool b -> Atm (Bool b)
  | L.GetBang x -> Atm (Var x)
  | L.Void -> Atm Void
  | L.SetBang (v, e1) ->
    let e1' = rco_exp e1 in
    SetBang (v, e1')
  | L.While (cond, body) ->
    let cond' = rco_exp cond in
    let body' = rco_exp body in
    While (cond', body')
  | L.Begin (exps, last) ->
    let exps' = List.map rco_exp exps in
    let last' = rco_exp last in
    Begin (exps', last')
  | L.If (cond, expthen, expelse) -> 
    let cond' = rco_exp cond in
    let expthen' = rco_exp expthen in
    let expelse' = rco_exp expelse in
    If (cond', expthen', expelse')
  | L.Let (x, e1, e2) ->
    let e1' = rco_exp e1 in
    let e2' = rco_exp e2 in
    Let (x, e1', e2')
  | L.Prim (op, exps) -> 
    let binds, atms = List.split (List.map rco_atom exps) in
    nest_let (List.concat binds) (Prim (op, atms))
  | L.Collect n -> Collect n
  | L.Allocate (i, ty) -> Allocate (i, ty)
  | L.GlobalVal v -> GlobalVal v
  | L.VecLen e1 ->
    let binds, atm = rco_atom e1 in
    nest_let binds (VecLen atm)
  | L.VecRef (e1, i) ->
    let binds, atm = rco_atom e1 in
    nest_let binds (VecRef (atm, i))
  | L.VecSet (e1, i, e2) ->
    let b1, a1 = rco_atom e1 in
    let b2, a2 = rco_atom e2 in
    nest_let (b1 @ b2) (VecSet (a1, i, a2))
  | L.FunRef (lbl, i) -> FunRef (lbl, i)
  | L.Apply (f, args) ->
    let arg_pair = List.map rco_atom args in
    let arg_bind = List.concat (List.map fst arg_pair) in
    let arg_atms = List.map snd arg_pair in
    let f_bind, f_atm = rco_atom f in
    nest_let (f_bind @ arg_bind) (Apply (f_atm, arg_atms))

let rco_def (d : L.def) : def =
  let L.Def (name, { args; ret; body }) = d in
  let body' = rco_exp body in
    Def (name, { args; ret; body = body' })

let remove_complex_operands (L.Program defs) =
  let defs' = List.map rco_def defs in
    Program defs'

