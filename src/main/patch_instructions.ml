open Types
open X86_def
module X = X86_var_def


let convert_arg (arg : X.arg) : arg =
  match arg with
  | X.Imm n -> Imm n
  | X.Reg r -> Reg r
  | X.Deref (reg, ofs) -> Deref (reg, ofs)
  | X.ByteReg br -> ByteReg br
  | X.GlobalArg l -> GlobalArg l
  | X.Var _ -> failwith "Shouldn't have variables from assign homes pass"

let is_mem_or_global = function
  | X.Deref _ | X.GlobalArg _ -> true
  | _ -> false

let patch (instr : X.instr) : instr list =
  match instr with
  | X.Movq (src, dst) ->
    let src' = convert_arg src in
    let dst' = convert_arg dst in
      if src' = dst' then 
        []
      else 
        if is_mem_or_global src && is_mem_or_global dst then
          [ Movq (src', Reg Rax);
            Movq (Reg Rax, dst') ]
        else
          [ Movq (src', dst') ]
  | X.Addq (src, dst) ->
    if is_mem_or_global src && is_mem_or_global dst then
      [ Movq (convert_arg src, Reg Rax);
        Addq (Reg Rax, convert_arg dst) ]
    else
      [ Addq (convert_arg src, convert_arg dst) ]
  | X.Subq (src, dst) ->
    if is_mem_or_global src && is_mem_or_global dst then
      [ Movq (convert_arg src, Reg Rax);
        Subq (Reg Rax, convert_arg dst) ]
    else
      [ Subq (convert_arg src, convert_arg dst) ]
  | X.Xorq (src, dst) ->
    if is_mem_or_global src && is_mem_or_global dst then
      [ Movq (convert_arg src, Reg Rax);
        Xorq (Reg Rax, convert_arg dst) ]
    else
      [ Xorq (convert_arg src, convert_arg dst) ]
  | X.Cmpq (src, Imm n) ->
      [ Movq (Imm n, Reg Rax);
        Cmpq (convert_arg src, Reg Rax) ]
  | X.Cmpq (src, dst) ->
    if is_mem_or_global src && is_mem_or_global dst then
      [ Movq (convert_arg src, Reg Rax);
        Cmpq (Reg Rax, convert_arg dst) ]
    else
      [ Cmpq (convert_arg src, convert_arg dst) ]
  | X.Andq (src, dst) ->
    if is_mem_or_global src && is_mem_or_global dst then
      [ Movq (convert_arg src, Reg Rax);
        Andq (Reg Rax, convert_arg dst) ]
    else
      [ Andq (convert_arg src, convert_arg dst) ]
  | X.Sarq (src, dst) ->
    if is_mem_or_global src && is_mem_or_global dst then
      [ Movq (convert_arg src, Reg Rax);
        Sarq (Reg Rax, convert_arg dst) ]
    else
      [ Sarq (convert_arg src, convert_arg dst) ]
  | X.Set (cc, ByteReg br) ->
      [ Set (cc, ByteReg br) ]
  | X.Set (_, _) ->
      failwith "Set must have byte register as second argument"
  | X.Movzbq (ByteReg br, dst) ->
    if is_mem_or_global dst then
      [ Movzbq (ByteReg br, Reg Rax);
        Movq (Reg Rax, convert_arg dst) ]
    else
      [ Movzbq (ByteReg br, convert_arg dst) ]
  | X.Movzbq (_, _) ->
      failwith "Movzbq source must be byte register"
  | X.Negq arg ->
      [ Negq (convert_arg arg) ]
  | X.Pushq arg ->
      [ Pushq (convert_arg arg) ]
  | X.Popq arg ->
      [ Popq (convert_arg arg) ]
  | X.Leaq (src, dst) ->
    if is_mem_or_global src && is_mem_or_global dst then
      [ Leaq (convert_arg src, Reg Rax);
        Movq (Reg Rax, convert_arg dst) ]
    else
      [ Leaq (convert_arg src, convert_arg dst) ]
  | X.Callq (lbl, n) ->
      [ Callq (lbl, n) ]
  | X.IndirectCallq (arg, n) ->
      [ IndirectCallq (convert_arg arg, n) ]
  | X.Jmp lbl ->
      [ Jmp (lbl) ]
  | X.JmpIf (cc, lbl) ->
      [ JmpIf (cc, lbl) ]
  | X.TailJmp (f, n) ->
    let f' = convert_arg f in
    if f' = Reg Rax then
      [ TailJmp (Reg Rax, n) ]
    else
      [ Movq (f', Reg Rax);
        TailJmp (Reg Rax, n) ]
  | X.Retq ->
      [ Retq ]

let convert_block (b : X.binfo1 X.block) : block =
  let X.Block (_, instrs) = b in
  let patched = List.flatten (List.map patch instrs) in
    Block (patched)

let convert_info (i : X.finfo3) : finfo =
  let (X.Finfo3 finfo) = i in
    Finfo
      { num_spilled      = finfo.num_spilled;
        num_spilled_root = finfo.num_spilled_root;
        used_callee      = finfo.used_callee }

let patch_instructions_def (def : (X.finfo3, X.binfo1) X.def) : def =
  (* Unpack the labeled block list (`lbs`) from a definition. *)
  let X.(Def (lbl, finfo, fcont)) = def in
  let X.{ nparams; locals; body = lbs } = fcont in

  (* Patch the instructions. *)
  let lbs' = List.map (fun (lbl, block) -> (lbl, convert_block block)) lbs in

  (* Put the definition back together. *)
  let fcont' = { nparams; locals; body = lbs' } in
  let finfo' = convert_info finfo in
    Def (lbl, finfo', fcont')

let patch_instructions
    (prog : (X.finfo3, X.binfo1) X.program) : program =
  let (X86Program defs) = prog in
    X86Program (List.map patch_instructions_def defs)
