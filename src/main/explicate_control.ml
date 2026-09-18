open Support.Utils
open Types
open Cfun

module L = Lfun_ref_mon

(* Variable to hold gensym function. *)
let fresh = ref (make_gensym ())

(* Variable to hold labeled blocks for a single function. *)
let basic_blocks : tail LabelMap.t ref = ref LabelMap.empty

(* Dummy variables should always have the prefix "_.". *)
let is_dummy_var v = (String.sub v 0 2) = "_."

let convert_atom (a : L.atm) : atm =
  match a with
  | L.Int i -> Int i
  | L.Var v -> Var v
  | L.Bool b -> Bool b
  | L.Void -> Void

let convert_exp (e : L.exp) : exp =
  match e with 
  | L.Atm a -> Atm (convert_atom a)
  | L.Prim (op, args) -> Prim(op, List.map convert_atom args)
  | L.Allocate (i, ty) -> Allocate (i, ty)
  | L.GlobalVal v -> GlobalVal v
  | L.VecLen a -> VecLen (convert_atom a)
  | L.VecRef (a, i) -> VecRef (convert_atom a, i)
  | L.VecSet (a1, i, a2) -> VecSet (convert_atom a1, i, convert_atom a2)
  | L.FunRef (lbl, i) -> FunRef (lbl, i)
  | L.Apply (f, args) -> Call (convert_atom f, List.map convert_atom args)
  | _ -> 
    failwith "Invalid expression"

(* Convert expressions which are the binding expression of a `let` expression
 * (i.e. in `(let (var <exp1>) <exp2>)` the binding expression is `<exp1>`).
 * These are ultimately converted to assignments.
 * The `tail` is the continuation (what to do after the binding). *)
let rec explicate_assign (e : L.exp) (v : var) (tl : tail) : tail =
  match e with 
  | L.Let (x, e1, e2) -> 
    let cont_tl = explicate_assign e2 v tl in
    explicate_assign e1 x cont_tl
  | L.If (c, t, f) ->
    let cont_lbl = create_block tl in
    let then_tl = explicate_assign t v (Goto cont_lbl) in
    let else_tl = explicate_assign f v (Goto cont_lbl) in
      explicate_pred c then_tl else_tl
  | L.SetBang (var, e1) ->
    let rhs_tl = explicate_assign e1 var tl in
    Seq (Assign (v, Atm Void), rhs_tl)
  | L.While (cond, body) ->
    let name = !fresh ~base:"loop" ~sep:"_" in
    let loop_lbl = Label name in
    let body_tl = explicate_effect body (Goto loop_lbl) in
    let cond_tl = explicate_pred cond body_tl tl in
    basic_blocks := LabelMap.add loop_lbl cond_tl !basic_blocks;
    Seq (Assign (v, Atm Void), Goto loop_lbl)
  | L.Begin (exps, last) ->
    let final = explicate_assign last v tl in
    List.fold_right ( fun e acc -> explicate_effect e acc ) exps final
  | L.Collect n ->
    if is_dummy_var v then
      Seq (Collect n, tl)
    else
      Seq (Assign (v, Atm Void), Seq (Collect n, tl))
  | L.Atm _ | L.Prim _ | L.VecRef _ | L.VecSet _ | L.VecLen _ | L.Allocate _ |L.GlobalVal _ 
  | L.FunRef _  | L.Apply _ -> 
    let stmt = Assign(v, convert_exp e)
    in Seq(stmt, tl)

(* Convert `if` expressions.
 * `e` is the condition part of the expression (evaluating to boolean).
 * The `then_tl` and `else_tl` are the two possible continuations. *)
and explicate_pred (e : L.exp) (then_tl : tail) (else_tl : tail) : tail =
  match e with
  | L.Prim (`Not, [L.Bool b]) ->
    if b then else_tl else then_tl
  | L.Prim (`Not, [L.Var v]) ->
    let eq_exp = L.Prim (`Eq, [L.Var v; L.Bool false]) in
      explicate_pred eq_exp then_tl else_tl
  | L.Prim (#cmp_op as op, [a1; a2]) ->
    let a1' = convert_atom a1 in
    let a2' = convert_atom a2 in
    let then_lbl = create_block then_tl in
    let else_lbl = create_block else_tl in
    IfStmt { op; arg1 = a1'; arg2 = a2'; jump_then = then_lbl; jump_else = else_lbl }
  | L.Atm (L.Bool b) ->
    if b then then_tl else else_tl
  | L.Atm (L.Var v) ->
    let eq_exp = L.Prim (`Eq, [L.Var v; L.Bool true]) in
    explicate_pred eq_exp then_tl else_tl
  | L.Let (x, e1, e2) ->
    let cont_tl = explicate_pred e2 then_tl else_tl in
    explicate_assign e1 x cont_tl
  | L.If (c, t, f) ->
    let then_lbl = create_block then_tl in
    let else_lbl = create_block else_tl in
    let then_cont = explicate_pred t (Goto then_lbl) (Goto else_lbl) in
    let else_cont = explicate_pred f (Goto then_lbl) (Goto else_lbl) in
    explicate_pred c then_cont else_cont
  | L.Begin(exps, last) ->
    let final = explicate_pred last then_tl else_tl in
    List.fold_right ( fun e acc -> explicate_effect e acc ) exps final
  | L.VecRef (a, i) ->
    let tmp = !fresh ~base:"$vecref" ~sep:"." in
    let cont = explicate_pred (L.Atm (L.Var tmp)) then_tl else_tl in
    explicate_assign (L.VecRef (a, i)) tmp cont
  | L.Apply (f, args) ->
    let tmp = !fresh ~base:"apply" ~sep:"_" in
    let cont = explicate_pred (L.Atm (L.Var tmp)) then_tl else_tl in
    explicate_assign (L.Apply (f, args)) tmp cont
  | _ ->
    failwith "Invalid predicate expression"

(* Convert expressions in effect position.
 * Effect position includes:
 * - the expressions before the last expression in a `begin` expression
 * - the body expressions in a `while` loop
 * These are expressions that are only evaluated for their side effects.
 * Pure expressions in effect position are discarded,
 * since they can't have any effect. *)
and explicate_effect (e : L.exp) (tl : tail) : tail =
  match e with
  | L.Prim (op, args) ->
    (match op with
      | `Read ->
        Seq (PrimS (`Read, List.map convert_atom args), tl)
      | `Print ->
        Seq (PrimS (`Print, List.map convert_atom args), tl)
      | _ ->
        tl)
  | L.SetBang (v, e1) ->
    explicate_assign e1 v tl
  | L.Let (x, e1, e2) ->
    let cont_tl = explicate_effect e2 tl in
    explicate_assign e1 x cont_tl
  | L.If (c, t, f) ->
    let cont_lbl = create_block tl in
    let then_tl = explicate_effect t (Goto cont_lbl) in
    let else_tl = explicate_effect f (Goto cont_lbl) in
    explicate_pred c then_tl else_tl
  | L.While (cond, body) ->
    let name = !fresh ~base:"loop" ~sep:"_" in
    let loop_lbl = Label name in
    let body_tl = explicate_effect body (Goto loop_lbl) in
    let cond_tl = explicate_pred cond body_tl tl in
    basic_blocks := LabelMap.add loop_lbl cond_tl !basic_blocks;
    Goto loop_lbl
  | L.Begin (exps, last) ->
    let acc = explicate_effect last tl in
    List.fold_right ( fun e acc -> explicate_effect e acc ) exps acc
  | L.Collect n ->
    Seq (Collect n, tl)
  | L.VecSet (a1, i, a2) ->
    Seq (VecSetS (convert_atom a1, i, convert_atom a2), tl)
  | L.Apply (f, args) ->
    Seq (CallS (convert_atom f, List.map convert_atom args), tl)
  | _ ->
    tl

(* Convert expressions in tail position.
 * This includes:
 * 1) any top-level expression
 * 2) any expression at the end of a larger expression
 *    that will be evaluated to give the result of the entire expression
 * Examples of (2):
 * - the body of a `let`
 * - the then/else clauses of an `if`
 * - the last expression of a `begin` *)
and explicate_tail (e : L.exp) : tail =
  match e with
  | L.Let (x, e1, e2) -> 
    explicate_assign e1 x (explicate_tail e2)
  | L.If (c, t, f) ->
    let then_tl = explicate_tail t in
    let else_tl = explicate_tail f in
    explicate_pred c then_tl else_tl
  | L.While (cond, body) ->
    let name = !fresh ~base:"loop" ~sep:"_" in
    let loop_lbl = Label name in
    let body_tl = explicate_effect body (Goto loop_lbl) in
    let cond_tl = explicate_pred cond body_tl (Return (Atm Void)) in
    basic_blocks := LabelMap.add loop_lbl cond_tl !basic_blocks;
    Goto loop_lbl
  | L.SetBang (v, e1) ->
    explicate_assign e1 v (Return (Atm Void))
  | L.Begin (exps, last) ->
    let final = explicate_tail last in
    List.fold_right ( fun e acc -> explicate_effect e acc ) exps final
  | L.Apply (f, args) ->
    TailCall (convert_atom f, List.map convert_atom args)
  | _ -> 
    Return (convert_exp e)

(* Create a block from a tail.
 * Return a "goto" label to the block. *)
and create_block (tl : tail) : label =
  match tl with
    | Goto lbl -> lbl
    | Return _
    | Seq _
    | TailCall _
    | IfStmt _ ->
        let name = !fresh ~base:"block" ~sep:"_" in
        let lbl = Label name in
          begin
            basic_blocks := LabelMap.add lbl tl !basic_blocks;
            lbl
          end

let explicate_defs (d : L.def) : def  =
  (* Initialize variable to hold labeled blocks to an empty map. *)
  let _ = basic_blocks := LabelMap.empty in
  let L.Def (lbl, f) = d in
  let L.{ args; ret; body } = f in
  let t = explicate_tail body in
  (* The `locals` field is empty here;
   * it will be filled in by the type checker. *)
  let locals = [] in
  (* Collect the labeled blocks to make the function body. *)
  let lts = [(Label "start", t)] @ LabelMap.bindings !basic_blocks in
  let fc = { args; ret; locals; body=lts } in
    Def (lbl, fc)

let explicate_control (prog : L.program) : program =
  let (L.Program ds) = prog in
  let _ = fresh := make_gensym () in
    CProgram (List.map explicate_defs ds)
