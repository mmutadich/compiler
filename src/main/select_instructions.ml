open Support
open Types
open Utils
module C = Cfun
open X86_var_def


let arg_regs = [ Rdi; Rsi; Rdx; Rcx; R8; R9 ]

let select_atm (a : C.atm) : X86_var_def.arg = 
  match a with
  | C.Void -> Imm 0
  | C.Int n -> Imm n
  | C.Var x -> Var x
  | C.Bool b -> Imm (if b then 1 else 0)

(* NOTE: `fix_label` is needed for global variables as well as functions.
   MacOS, for instance, puts `_` before the names of both in assembly code. *)
let make_tuple_tag (len : int) (vec : ty array) : int = 
  if len < 0 || len > 50 then
    failwith "invalid vector length";
  let is_ptr_ty ty =
    match ty with
    | Vector _ -> true
    | _      -> false
  in
  let rec build_mask i acc =
    if i = len then
      acc
    else
      let bit = if is_ptr_ty vec.(i) then 1 lsl (len - 1 - i) else 0 in
      build_mask (i + 1) (acc lor bit)
  in
  let ptr_mask = build_mask 0 0 in
  (ptr_mask lsl 7) lor (len lsl 1) lor 1

(* Convert statement instructions to x86 instructions *)
let stmt_instructions (s: C.stmt) : instr list =
  match s with 
  | C.PrimS (op, _) -> 
    (match op with 
    | `Read -> [Callq (Label (fix_label "read_int"), 0);]
    | `Print -> [Callq (Label (fix_label "print_int"), 0);])
  | C.Assign (v, C.Atm a) ->
      [ Movq (select_atm a, Var v)]
  | C.Assign (v, C.Prim (`Read, _)) ->
      [ Callq (Label (fix_label "read_int"), 0);
        Movq (Reg Rax, Var v) ]
  | C.Assign (v, C.Prim (`Negate, [a])) ->
      [ Movq (select_atm a, Var v);
        Negq (Var v) ]
  | C.Assign (v, C.Prim (`Not, [a])) ->
      [ Movq (select_atm a, Var v);
        Xorq (Imm 1, Var v) ]
  | C.Assign (v, C.Prim (`Add, [a1; a2])) ->
      [ Movq (select_atm a1, Var v);
        Addq (select_atm a2, Var v) ]
  | C.Assign (v, C.Prim (`Sub, [a1; a2])) ->
      [ Movq (select_atm a1, Var v);
        Subq (select_atm a2, Var v) ]
  | C.Assign (v, C.Prim (#cmp_op as op, [a1; a2])) ->
    let cc = cc_of_op op in
      [ Cmpq (select_atm a2, select_atm a1);
        Set (cc, ByteReg Al);
        Movzbq (ByteReg Al, Var v) ]  
  | C.Assign (v, C.Allocate (i, ty)) ->
    let tag = 
      match ty with
      | Vector vec -> make_tuple_tag i vec
      | _ -> failwith "Allocate called with non-vector type"
    in
    let delta = 8 * (i + 1) in
      [ Movq (GlobalArg (Label (fix_label "free_ptr")), Reg R11);
        Addq (Imm delta, GlobalArg (Label (fix_label "free_ptr")));
        Movq (Imm tag, Deref (R11, 0));
        Movq (Reg R11, Var v) ]
  | C.Assign (v, C.GlobalVal g) ->
      [ Movq (GlobalArg (Label (fix_label g)), Var v) ]
  | C.Assign (v, C.VecLen a) ->
      [ Movq (select_atm a, Reg R11);
        Movq (Deref (R11, 0), Reg Rax);
        Andq (Imm 0x7E, Reg Rax);
        Sarq (Imm 1, Reg Rax);
        Movq (Reg Rax, Var v) ]
  | C.Assign (v, C.VecRef (a, i)) ->
    let offset = 8 * (i + 1) in
      [ Movq (select_atm a, Reg R11);
        Movq (Deref (R11, offset), Var v)]
  | C.Assign (v, C.VecSet (a1, i, a2)) ->
    let offset = 8 * (i + 1) in
      [ Movq (select_atm a1, Reg R11);
        Movq (select_atm a2, Deref (R11, offset));
        Movq (Imm 0, Var v) ]
  | C.Assign (v, C.FunRef (Label lbl, _)) ->
      [ Leaq (GlobalArg (Label (fix_label lbl)), Var v) ]
  | C.Assign (v, C.Call (f, args)) ->
    let moves = List.mapi (fun i a ->
      if i >= List.length arg_regs then
        failwith "Too many arguments in call"
      else
        Movq (select_atm a, Reg (List.nth arg_regs i))
    ) args in
    moves @ [ IndirectCallq (select_atm f, List.length args);
              Movq (Reg Rax, Var v) ]
  | C.Collect n ->
      [ Movq (Reg R15, Reg Rdi);
        Movq (Imm n, Reg Rsi);
        Callq (Label (fix_label "collect"), 2) ]
  | C.VecSetS (a1, i, a2) ->
    let offset = 8 * (i + 1) in
      [ Movq (select_atm a1, Reg R11);
        Movq (select_atm a2, Deref (R11, offset)) ]
  | C.CallS (f, args) ->
    let moves = List.mapi (fun i a ->
      if i >= List.length arg_regs then
        failwith "Too many arguments in call"
      else
        Movq (select_atm a, Reg (List.nth arg_regs i))
    ) args in
    moves @ [ IndirectCallq (select_atm f, List.length args) ]
  | C.Assign (_, C.Prim (_, _)) ->
      failwith ("Invalid number of arguments to primitive")

(* Put return value in rax*)
let exp_to_rax (e : C.exp) : instr list =
  match e with
  | C.Atm a -> 
      [ Movq (select_atm a, Reg Rax) ]
  | C.Prim (`Read, _) ->
      [ Callq (Label (fix_label "read_int"), 0) ]
  | C.Prim (`Negate, [a]) ->
      [ Movq (select_atm a, Reg Rax);
        Negq (Reg Rax) ]
  | C.Prim (`Not, [a]) ->
      [ Movq (select_atm a, Reg Rax);
        Xorq (Imm 1, Reg Rax) ]
  | C.Prim (`Add, [a1; a2]) ->
      [ Movq (select_atm a1, Reg Rax);
        Addq (select_atm a2, Reg Rax) ]
  | C.Prim (`Sub, [a1; a2]) ->
      [ Movq (select_atm a1, Reg Rax);
        Subq (select_atm a2, Reg Rax) ]
  | C.Prim (#cmp_op as op, [a1; a2]) ->
      let cc = cc_of_op op in
      [ Cmpq (select_atm a2, select_atm a1);
        Set (cc, ByteReg Al);
        Movzbq (ByteReg Al, Reg Rax) ]
  | C.Allocate (i, ty) ->
    let tag = 
      match ty with
      | Vector vec -> make_tuple_tag i vec
      | _ -> failwith "Allocate called with non-vector type"
    in
    let delta = 8 * (i + 1) in
      [ Movq (GlobalArg (Label (fix_label "free_ptr")), Reg R11);
        Addq (Imm delta, GlobalArg (Label (fix_label "free_ptr")));
        Movq (Imm tag, Deref (R11, 0));
        Movq (Reg R11, Reg Rax) ]
  | C.GlobalVal g ->
      [ Movq (GlobalArg (Label (fix_label g)), Reg Rax) ]
  | C.VecLen a ->
      [ Movq (select_atm a, Reg R11);
        Movq (Deref (R11, 0), Reg Rax);
        Andq (Imm 0x7E, Reg Rax);
        Sarq (Imm 1, Reg Rax); ]
  | C.VecRef (a, i) ->
    let offset = 8 * (i + 1) in
      [ Movq (select_atm a, Reg R11);
        Movq (Deref (R11, offset), Reg Rax) ]
  | C.VecSet (a1, i, a2) ->
    let offset = 8 * (i + 1) in
      [ Movq (select_atm a1, Reg R11);
        Movq (select_atm a2, Deref (R11, offset));
        Movq (Imm 0, Reg Rax) ]
  | C.FunRef (Label f, _) ->
      [ Leaq (GlobalArg (Label (fix_label f)), Reg Rax) ]
  | C.Call (f, args) ->
    let moves = List.mapi (fun i a ->
      if i >= List.length arg_regs then
        failwith "Too many arguments in call"
      else
        Movq (select_atm a, Reg (List.nth arg_regs i))
    ) args in
    moves @ [ IndirectCallq (select_atm f, List.length args) ]
  | C.Prim (_, _) ->
      failwith ("Invalid number of arguments to primitive")

let rec tail_instructions (f_lbl : label) (i : C.tail) : instr list =
  match i with
  | C.Seq (stmt, tail) ->
    stmt_instructions stmt @ tail_instructions f_lbl tail
  | C.Return e ->
    let (Label f) = f_lbl in
    exp_to_rax e @ [ Jmp (Label (f ^ "_conclusion")) ]
  | C.Goto lbl ->
      [ Jmp lbl ]
  | C.IfStmt { op; arg1; arg2; jump_then; jump_else } ->
    let cc = cc_of_op op in
      [ Cmpq (select_atm arg2, select_atm arg1);
        JmpIf (cc, jump_then);
        Jmp (jump_else) ]
  | C.TailCall (f, args) ->
    let moves = List.mapi (fun i a ->
      if i >= List.length arg_regs then
        failwith "Too many arguments in call"
      else
        Movq (select_atm a, Reg (List.nth arg_regs i))
    ) args in
    moves @ [ TailJmp (select_atm f, List.length args) ]

let convert_lt (f_lbl : label) (lt : (label * C.tail))
      : label * binfo1 block =
  let (lbl, tail) = lt in
  let block = Block (Binfo1, tail_instructions f_lbl tail) in
    (lbl, block)

(*** New for chapter 7 ***)
(* Add argument passing instructions to the front of `start` blocks only.
   All other blocks are unchanged.
   See section 7.8 (p. 139) in the book.
   Also change the `start` block label to `FNAME_start`,
   where FNAME is `f_lbl`.
   `nparams` is the length of the `args` list.
   *)
let add_arg_instrs
      (f_lbl : label)
      (nparams : int)
      (args : (var * ty) list)
      (body : (label * binfo1 block) list)
        : (label * binfo1 block) list =
  let (Label f) = f_lbl in
  let start' = Label (f ^ "_start") in
  let concl' = Label (f ^ "_conclusion") in
  if nparams <> List.length args then
    failwith "Number of parameters doesn't match number of args";
  let arg_moves =
    List.mapi (fun i (v, _) ->
      if i >= List.length arg_regs then
        failwith "Too many args in function"
      else
        Movq (Reg (List.nth arg_regs i), Var v)
    ) args
  in
  List.map (fun (lbl, Block (binfo, instrs)) ->
    match lbl with
    | Label "start" ->
        (start', Block (binfo, arg_moves @ instrs))
    | Label "conclusion" ->
        (concl', Block (binfo, instrs))
    | _ ->
        (lbl, Block (binfo, instrs))
  ) body

let select_instructions_def (d : C.def) : (finfo1, binfo1) def =
  let (C.Def (f_lbl, fcont)) = d in
  let C.{ args; locals; body; _ } = fcont in
  let body'   = List.map (convert_lt f_lbl) body in
  let nparams = List.length args in
  let body''  = add_arg_instrs f_lbl nparams args body' in
  (* Make the argument variables into local variables. *)
  let locals' = args @ locals in
  let fcont'  = { nparams; locals = locals'; body = body'' } in
  (* We don't change `f_lbl` here because we will use it in
     `prelude_conclusion.ml` to generate
     the `FNAME_main` and `FNAME_conclusion` labels,
     as well as fixing the `FNAME_main` label. *)
    Def (f_lbl, Finfo1, fcont')

let select_instructions (prog : C.program) : (finfo1, binfo1) program =
  let (C.CProgram defs) = prog in
    X86Program (List.map select_instructions_def defs)
