open Support
open Types
open Utils

module X = X86_var_def

(* Flag; when true, extra debugging information is printed. *)
let _debug = ref false

let rflags_reg = X.Reg Rflags

let convert_arg (arg : X.arg) : location option =
  match arg with 
  | Var v -> Some (VarL v)
  | Reg r -> Some (RegL r)
  | Deref (reg, _) -> Some (RegL reg)
  | ByteReg _ -> Some (RegL Rax)
  | Imm _ -> None
  | GlobalArg _ -> None

let set_operation (op : location -> LocSet.t -> LocSet.t) (arg : X.arg) (s : LocSet.t ) : LocSet.t =
  match convert_arg arg with
  | Some a -> op a s
  | None -> s

let handle_callq (locs : location list) (s : LocSet.t ) =
  let set_remove = set_operation LocSet.remove in
  List.fold_right( fun h s ->
    match h with 
    | RegL r when RegSet.mem r caller_save_regs  -> set_remove (Reg r) s
    | _ -> s
  ) locs s

  let rec get_n_args regs n count: location list = 
    match regs with
    | [] -> []
    | _ when count == n -> []
    | h :: t -> (RegL h) :: (get_n_args t n (count + 1))

let compute_liveness_after (instr: X.instr) (l_before : LocSet.t ) (live_before_map : LocSet.t LabelMap.t) : LocSet.t =
  let set_add = set_operation LocSet.add in
  let set_remove = set_operation LocSet.remove in
  match instr with
    | Addq  (a, b) -> set_add b (set_add a l_before)
    | Subq  (a, b) -> set_add b (set_add a l_before)
    | Andq (a, b) -> set_add b (set_add a l_before)
    | Sarq (_, d) -> set_add d l_before
    | Callq (lbl, int) -> 
      if lbl <> (Label (fix_label "collect")) then
      handle_callq (LocSet.to_list l_before) l_before
      else 
        let free_regs = LocSet.of_list (get_n_args arg_passing_regs int 0)  in
        LocSet.union free_regs l_before
    | Movq  (a, b) -> set_add a (set_remove b l_before)
    | Movzbq (a, b) -> set_add a (set_remove b l_before)
    | Cmpq (a, b) -> set_remove rflags_reg (set_add b (set_add a l_before))
    | Set (_, arg) -> set_add rflags_reg (set_remove arg l_before)
    | JmpIf (_, label) -> 
      let live_after_jump = LabelMap.find label live_before_map in
      set_add rflags_reg (LocSet.union live_after_jump l_before)
    | Jmp label -> 
      (match LabelMap.find_opt label live_before_map with 
      | Some a -> a 
      | None -> let (Label lbl) = label in failwith (Printf.sprintf "%s" lbl))
    | Retq -> LocSet.empty
    | Leaq (_, arg) -> set_remove arg l_before
    | IndirectCallq (arg, int) -> 
      let s1 = set_add arg l_before in
      let new_set = handle_callq (LocSet.to_list s1) s1 in
      let free_regs = LocSet.of_list (get_n_args arg_passing_regs int 0) in
        LocSet.union free_regs new_set
    | TailJmp (arg, int) ->  
      let add_arg = set_add arg l_before in
      let free_regs = LocSet.of_list (get_n_args arg_passing_regs int 0)  in
        LocSet.union free_regs add_arg
    | _ -> l_before
    

(* Compute the live sets for the instructions of a single labeled block.
 * The `live_before_map` is the live-before sets for each block named
 * by the given labels. *)
let uncover_live_in_block
      (live_before_map : LocSet.t LabelMap.t) (instrs : X.instr list)
        : X.live =
  let after = 
    List.fold_right (fun instr acc ->
      let l_after = compute_liveness_after instr (List.hd acc) live_before_map in
      l_after :: acc
    ) instrs [LocSet.empty]
  in 
    {initial = List.hd after; afters = List.tl after}


(* Get the next jump labels, if any.
 * The jump instructions should only be at the end of the block,
 * but we can accumulate all of them, since you can have two
 * jumps at the end (one conditional, one not). *)
let get_next_labels (block : 'a X.block) : LabelSet.t =
  let (X.Block (_, instrs)) = block in
  List.fold_left( fun setolabels instr -> 
    match instr with 
    | X.JmpIf (_, label) -> LabelSet.add label setolabels
    | X.Jmp label -> LabelSet.add label setolabels
    | _ -> setolabels
  ) LabelSet.empty instrs

(* Liveness algorithm (dataflow analysis, but not generic):
 * - Create an empty (imperative) queue.
 * - Create an initial liveness map from labels to empty locsets
 *   (except for the "NAME_conclusion" label (NAME = function name),
 *    which has a fixed set of registers).
 * - Add all the labels (except "NAME_conclusion") to a queue.
 * - Repeat until the queue is empty:
 *   - Pop a label off the queue.
 *   - Get the instructions corresponding to the label.
 *   - Use the liveness map to get the old live-before set for the instructions.
 *   - Compute the new live-before set for the instructions.
 *   - If the live-before set has changed:
 *     - Update the liveness map.
 *     - Find the labels of the blocks that project to the current label's
 *       block, and add them to the queue.
 * - Return the liveness map.
 * NOTE: Make sure to never add the label "NAME_conclusion" to the queue!
 * It has no corresponding instructions.
 *)
let compute_liveness
      (f_lbl : label)
      (g     : LabelDgraph.t)
      (imap  : (X.instr list) LabelMap.t)
        : LocSet.t LabelMap.t =
  let q  = ref (Queue.create ()) in
  let (Label f_var) = f_lbl in 
  let concset = LocSet.of_list [RegL Rax; RegL Rsp] in
  let init_live = 
    List.fold_left(fun new_map label->
        if label = (Label (f_var ^ "_conclusion")) 
          then new_map
        else
          let () = Queue.add label !q in
          LabelMap.add label LocSet.empty new_map
      ) LabelMap.empty (LabelMap.keys imap)
  in
  let rec resolve_queue (liveness_map : LocSet.t LabelMap.t) : LocSet.t LabelMap.t =
    if Queue.is_empty !q 
      then liveness_map
    else
      let label = Queue.pop !q in
      let instrs = LabelMap.find label imap in
      let old_liveness = LabelMap.find label liveness_map in
      let new_live = uncover_live_in_block liveness_map instrs in
      if LocSet.equal new_live.initial old_liveness 
        then
          resolve_queue liveness_map
      else
        let () = 
        if LabelDgraph.mem g label then
          List.iter(fun child ->
            Queue.add child !q
            ) (LabelDgraph.neighbors_in g label)
          in
        resolve_queue (LabelMap.add label new_live.initial liveness_map)
  in
    resolve_queue (LabelMap.add (Label (f_var^"_conclusion")) concset init_live)

let uncover_live_def
    (def : (X.finfo1, X.binfo1) X.def) : (X.finfo1, X.binfo2) X.def =
  (* Unpack the labeled block list (`lbs`) from a definition. *)
  let (X.Def (lbl, finfo, fcont)) = def in
  let X.{ nparams; locals; body = lbs } = fcont in

  (* Generate the control-flow graph from the (label, block) pairs. *)
  let cfg =
    LabelDgraph.of_alist lbs
      (fun bl -> LabelSet.elements (get_next_labels bl))
  in

  (* Create a label->instrs map. *)
  let (imap : (X.instr list) LabelMap.t) =
    lbs
      |> List.map (fun (lbl, X.Block (_, instrs)) -> (lbl, instrs))
      |> LabelMap.of_list
  in

  (* Compute all the live-before sets. *)
  let (live_before_sets : LocSet.t LabelMap.t) =
    compute_liveness lbl cfg imap
  in

  (* We run the liveness computation one last time after computing
   * all the live-before sets to get the full liveness information
   * for a block.  This is a little inefficient; we could generate it
   * in the `compute_liveness` function while computing the
   * live-before sets and return that directly.
   * IMO this is a bit cleaner and easier to debug. *)
  let get_live (lbl : label) : X.live =
    let instrs =
      LabelMap.find_or_fail lbl imap
        ~err_msg:
          (Printf.sprintf "uncover_live: no instructions for label (%s)"
             (string_of_label lbl))
    in
      uncover_live_in_block live_before_sets instrs
  in

  (* Rewrite the label/block information with new block info containing
   * the liveness information. *)
  let lbs' =
    List.map
      (fun (lbl, X.Block (_, instrs)) ->
         let b = X.Binfo2 (get_live lbl) in
           (lbl, X.Block (b, instrs)))
      lbs
  in

  (* Put the definition back together. *)
  let fcont' = X.{ nparams; locals; body = lbs' } in
    X.Def (lbl, finfo, fcont')

let uncover_live
    (prog : (X.finfo1, X.binfo1) X.program) : (X.finfo1, X.binfo2) X.program =
  let (X.X86Program defs) = prog in
    X86Program (List.map uncover_live_def defs)
