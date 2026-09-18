open Types
open Lfun_shrink
module L = Lfun

let rec shrink_exp (e : L.exp) : exp =
  match e with
  | L.Void -> Void
  | L.Bool b -> Bool b
  | L.Int n -> Int n
  | L.Var v -> Var v
  | L.Prim (op, exps) -> 
    Prim(op, List.map shrink_exp exps)
  | L.SetBang (v, e1) ->
    SetBang (v, shrink_exp e1)
  | L.Begin (exps, elast) ->
    Begin (List.map shrink_exp exps, shrink_exp elast)
  | L.If (e1, e2, e3) -> 
    If (shrink_exp e1, shrink_exp e2, shrink_exp e3)
  | L.And (e1, e2) -> 
    If (shrink_exp e1, shrink_exp e2, Bool false)
  | L.Or (e1, e2) ->
    If (shrink_exp e1, Bool true, shrink_exp e2)
  | L.While (cond, body) ->
    While (shrink_exp cond, shrink_exp body)
  | L.Let (v, e1, e2) ->
    Let (v, shrink_exp e1, shrink_exp e2)
  | L.Vec (exps, tyopt) ->
    Vec (List.map shrink_exp exps, tyopt)
  | L.VecLen e1 ->
    VecLen (shrink_exp e1)
  | L.VecRef (e1, i) ->
    VecRef (shrink_exp e1, i)
  | L.VecSet (e1, i, e2) ->
    VecSet (shrink_exp e1, i, shrink_exp e2)
  | L.Apply (f, args) ->
    Apply (shrink_exp f, List.map shrink_exp args)

let shrink_def (d : L.def) : def =
  let (L.Def (name, f)) = d in
  let body' = shrink_exp f.body in
  let f' = { args = f.args; ret = f.ret; body = body' } in
    Def (name, f')

let shrink (L.Program (ds, e)) =
  let ds' = List.map shrink_def ds in
  let e'  = shrink_exp e in
  let d   = Def ("main", { args = []; ret = Integer; body = e' } ) in
    Program (d :: ds')
