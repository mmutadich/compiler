open Support
open Utils
open Types
open Alloc_utils
module X = X86_def
open X86_asm

let resize_initial_heap_size (n : int) : unit =
  begin
    if n < min_heap_size || n mod 8 <> 0 then
      failwithf "heap size must be divisible by 8 and >= %d" min_heap_size;
    init_heap_size := n
  end

(* Conclusion code that is common to both
   function conclusions and tail calls.
   Non-tail calls will add `Retq` at the end.
   Tail calls will add `TailJmp <arg>` *)
let conclusion_code (conclusion_params : RegSet.t * int * int) : instr list =
  let (callee_saves, ss, rs) = conclusion_params in
  let callee_save_list = RegSet.elements callee_saves in
  let reset_rootstack_ptr =
    [Subq (Imm (8 * rs), Reg R15)]
  in
  let reclaim_stack_space =
    [Addq (Imm ss, Reg Rsp)]
  in 
  let callee_save_pops =
    List.map (fun r -> Popq (Reg r)) (List.rev callee_save_list)
  in
    reset_rootstack_ptr @
    reclaim_stack_space @
    callee_save_pops @
    [Popq (Reg Rbp)]

(* Code that has to be added to each program at the end. 
   It's parameterized on the set of callee-save registers (`callee_saves`),
   the stack space (`ss`), and on the number of rootstack items (`rs`).
   We bundle these into the `conclusion_params` tuple
   because they are also used for computing code for tail calls elsewhere.
 *)
let epilog 
      (f_lbl : label)
      (conclusion_params : RegSet.t * int * int)
        : instr list = 
  let (callee_saves, ss, rs) = conclusion_params in
  let f_name  = string_of_label f_lbl in
  let is_main = f_name = "main" in
  let save_previous = [(Global(Label (fix_label f_name))); (Align 8) ; (Label (fix_label f_name)); (Pushq (Reg Rbp)); (Movq ((Reg Rsp), (Reg Rbp)))] in 
  let push_callee = RegSet.fold( fun reg acc -> acc @ [(Pushq (Reg reg))] ) callee_saves [] in
  let reserve_stack = [(Subq ((Imm ss), (Reg Rsp)))] in
  let garbage_init = 
    if is_main then
    [(Movq ((Imm !init_heap_size), (Reg Rdi))) ; (Movq ((Imm !init_heap_size), (Reg Rsi))); (Callq (Label (fix_label "initialize")));  (Movq ((GlobalArg (Rip, (Label (fix_label "rootstack_begin"))), (Reg R15))))] 
    else 
    [] in
  let rec allocate_stack curr = 
    if curr = (rs * 8) then 
      []
    else
      (Movq ((Imm 0), (Deref (R15, curr)))) :: allocate_stack (curr + 8)
    in
  let root_stack = [(Addq ((Imm (rs * 8)), (Reg R15)))] in
  let jump_start = [(Jmp (Label (f_name ^ "_start")))] in
  let prelude = save_previous @ push_callee @ reserve_stack @ garbage_init @ (allocate_stack 0) @ root_stack @ jump_start in
  let conc_label = [(Label (f_name ^ "_conclusion"))] in
  let conclusion = conc_label @ (conclusion_code conclusion_params) @ [Retq]
  in
    prelude @ conclusion


(* Convert a labeled block to a list of instructions. *)
let asm_of_lb
      (conclusion_params : RegSet.t * int * int)
      (deref_adjust : int)
      (lb : label * X.block)
        : instr list =
  let (lbl, wrapped_block) = lb in
  let (X.Block (block)) = wrapped_block in
  let (Label labl_str) = lbl in
  let rec convert_block (block: X.instr list) : instr list = 
    match block with 
    | [] -> []
    | h :: t -> 
    let convert_arg (old_arg : X.arg) : arg =
      match old_arg with 
        | Imm i -> Imm i
        | Reg reg -> Reg reg
        | Deref (reg, i) -> 
          if reg = R11 || reg = R15 then
            Deref (reg, i)
          else 
            Deref (reg, i - deref_adjust)
        | ByteReg breg -> ByteReg breg
        | GlobalArg lbl -> GlobalArg (Rip, lbl)

    in
      let convert_instruction (old_instr : X.instr) : instr list =
        match old_instr with 
        | Addq (a, b) -> [Addq (convert_arg a, convert_arg b)]
        | Subq (a, b) -> [Subq (convert_arg a, convert_arg b)]
        | Negq n -> [Negq (convert_arg n)]
        | Xorq (a, b) -> [Xorq (convert_arg a, convert_arg b)]
        | Cmpq (a, b) -> [Cmpq (convert_arg a, convert_arg b)]
        | Set  (cc, arg) -> [Set (cc, convert_arg arg)]
        | Movzbq (a, b) -> [Movzbq (convert_arg a, convert_arg b)]
        | Movq (a, b) -> [Movq (convert_arg a,convert_arg b)]
        | Pushq p -> [Pushq (convert_arg p)]
        | Popq p -> [Popq (convert_arg p)]
        | Callq (l, _) ->[Callq l]
        | Retq -> [Retq]
        | Jmp l -> [Jmp l]
        | JmpIf (cc, l)-> [JmpIf (cc, l)]
        | Andq (a, b) -> [Andq (convert_arg a, convert_arg b)]
        | Sarq (a, b) -> [Sarq (convert_arg a, convert_arg b)]
        | Leaq (a,b) -> [Leaq (convert_arg a, convert_arg b)]
        | IndirectCallq (arg, _) -> [IndirectCallq (convert_arg arg)]
        | TailJmp (arg, _) -> 
            conclusion_code conclusion_params @ [TailJmp (convert_arg arg)]

    in
      (convert_instruction h) @ convert_block t
  in 
    [(Label labl_str)] @ convert_block block

let prelude_conclusion_def (def : X.def) : instr list =
  (* Unpack the definition. *)
  let (Def (lbl, finfo, fcont)) = def in
  let X.{ body = lbs; _ } = fcont in
  let X.Finfo { num_spilled; num_spilled_root; used_callee } = finfo in
  let num_callees = RegSet.cardinal used_callee in

  (* Amount to shift all stack locations that are relative to %rbp: *)
  let deref_adjust = 8 * num_callees in
  let extra_stack_space =
    align_16 (8 * (num_spilled + num_callees)) - 8 * num_callees
  in
  let conclusion_params =
    (used_callee, extra_stack_space, num_spilled_root)
  in
  let ep = epilog lbl conclusion_params in
  let lbs' =
    List.concat_map
      (asm_of_lb conclusion_params deref_adjust)
      lbs
  in
    lbs' @ ep

let prelude_conclusion (prog : X.program) : program =
  let (X86Program defs) = prog in
    X86Program (List.concat_map prelude_conclusion_def defs)
