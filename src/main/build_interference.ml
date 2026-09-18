open Support.Utils
open Types
open X86_var_def


let arg_to_loc (arg : X86_var_def.arg) : Types.location option =
  match arg with
  | Var x -> Some (VarL x)
  | Reg r -> Some (RegL r)
  | ByteReg b -> Some (RegL (reg_of_bytereg b))
  | Deref (r, _) -> Some (RegL r)
  | Imm _ | GlobalArg _ -> None

(* Add edges to the interference graph. *)
let add_edges (g : LocUgraph.t) (locs1 : Types.location list) (locs2 : Types.location list) =
  List.fold_left (fun g l1 ->
    List.fold_left (fun g l2 ->
      if l1 <> l2 then LocUgraph.add_edge_new g l1 l2 else g
    ) g locs2
  ) g locs1

(* Get list of location nodes written to by an instruction *)
let write_locs (instr : X86_var_def.instr) : Types.location list =
  let opt_to_list = function
    | Some x -> [x]
    | None -> []
  in
  match instr with
  | Movq (_, dst) -> opt_to_list (arg_to_loc dst)
  | Movzbq (_, dst) -> opt_to_list (arg_to_loc dst)
  | Addq (_, dst) -> opt_to_list (arg_to_loc dst)
  | Subq (_, dst) -> opt_to_list (arg_to_loc dst)
  | Negq dst -> opt_to_list (arg_to_loc dst)
  | Xorq (_, dst) -> opt_to_list (arg_to_loc dst)
  | Andq (_, dst) -> opt_to_list (arg_to_loc dst)
  | Sarq (_, dst) -> opt_to_list (arg_to_loc dst)
  | Popq dst -> opt_to_list (arg_to_loc dst)
  | Leaq (_, dst) -> opt_to_list (arg_to_loc dst)
  | Set (_, dst) -> opt_to_list (arg_to_loc dst)
  | Callq _ -> List.map (fun r -> RegL r) (RegSet.elements caller_save_regs)
  | IndirectCallq _ -> List.map (fun r -> RegL r) (RegSet.elements caller_save_regs)
  | Cmpq (_, _) -> [RegL Rflags]
  | Pushq _ | Retq | Jmp _ | JmpIf _ | TailJmp _ -> []

(* helper function to recursively process instruction and set*)
let rec process_instrs (g : LocUgraph.t) (instrs : X86_var_def.instr list) (afters : LocSet.t list) (i : int) (vvs : VarSet.t) =
  if i >= List.length instrs then g
  else
    (* get curr instruction and live after locations*)
    let instr = List.nth instrs i in
    let live_after_locs = LocSet.elements (List.nth afters i) in
    match instr with
    | Movq (src, dst) | Movzbq (src, dst) ->
      (match arg_to_loc dst with
      | None ->
        let g' = g in
        process_instrs g' instrs afters (i + 1) vvs
      | Some dst_loc ->
        let filtered = 
          match src with
          | Imm _ -> List.filter (fun v -> v <> dst_loc) live_after_locs
          | GlobalArg _ -> List.filter (fun v -> v <> dst_loc) live_after_locs
          | _ ->
            (match arg_to_loc src with
            | Some src_loc ->
              List.filter (fun v -> v <> dst_loc && v <> src_loc) live_after_locs
            | None ->
              List.filter (fun v -> v <> dst_loc) live_after_locs)
        in
        let g' = add_edges g [dst_loc] filtered in
        process_instrs g' instrs afters (i + 1) vvs)
    | Callq (lbl, _) ->
      let written = write_locs instr in 
      let g' = List.fold_left (fun g d ->
        let filtered = List.filter (fun v -> v <> d) live_after_locs in
        add_edges g [d] filtered
      ) g written in
      let g'' = 
        (match lbl with
        | Label s when s = fix_label "collect" ->
          let vec_locs = List.filter (function VarL v -> VarSet.mem v vvs 
                                                  | _ -> false) live_after_locs in
          List.fold_left (fun g r -> add_edges g [RegL r] vec_locs) g' (RegSet.elements callee_save_regs)
        | _ -> g')
      in
      process_instrs g'' instrs afters (i + 1) vvs
    | IndirectCallq _ ->
      let written = write_locs instr in 
      let g' = List.fold_left (fun g d ->
        let filtered = List.filter (fun v -> v <> d) live_after_locs in
        add_edges g [d] filtered
      ) g written in
      let vec_locs = List.filter (function VarL v -> VarSet.mem v vvs 
                                              | _ -> false) live_after_locs in
      let g'' = List.fold_left (fun g r -> add_edges g [RegL r] vec_locs) g' (RegSet.elements callee_save_regs) in
      process_instrs g'' instrs afters (i + 1) vvs
    | _ ->
      let written = write_locs instr in (* for other instruction, get list of live after locations*)
      let g' = List.fold_left (fun g d ->
        let filtered = List.filter (fun v -> v <> d) live_after_locs in
        add_edges g [d] filtered
      ) g written in
      process_instrs g' instrs afters (i + 1) vvs

(* Build the interference graph.
   `vvs` are the vector-valued variables. *)
let make_graph
      (g : LocUgraph.t) (lbs : (label * binfo2 block) list) (vvs : VarSet.t)
         : LocUgraph.t =
  List.fold_left (fun g (_, Block (Binfo2 {afters; _}, instrs)) ->
    process_instrs g instrs afters 0 vvs
  ) g lbs

(* Replace the Binfo2 field in blocks with a placeholder Binfo1 field. *)
let replace_binfo (lbs : (label * binfo2 block) list)
      : (label * binfo1 block) list =
  List.map
    (fun (lbl, Block (_, instrs)) -> (lbl, Block (Binfo1, instrs)))
    lbs

(* Add extra edges between locals that aren't in the interference graph
   and the %rsp register. This is needed because there are cases
   (e.g. with TailJmp and IndirectCallq) where variables
   would otherwise disappear from the interference graph.
   This would create problems in the "allocate registers" pass. *)
let add_extra_rsp_edges (g : LocUgraph.t) (vs : VarSet.t) : LocUgraph.t =
  VarSet.fold (fun v g ->
    let vl = VarL v in
    if LocUgraph.mem g vl then 
      g
    else 
      LocUgraph.add_edge_new g vl (RegL Rsp)
  ) vs g

(* Collect the vector-typed vars. *)
let vector_vars (lts : (var * ty) list) : VarSet.t =
  let is_vector = function
    | Vector _ -> true
    | _ -> false
  in
    lts
     |> List.filter_map (fun (v, t) -> if is_vector t then Some v else None)
     |> VarSet.of_list

let build_interference_def
      (def : (finfo1, binfo2) def) : (finfo2, binfo1) def =
  (* Unpack the labeled block list (`lbs`) from a definition. *)
  let (Def (lbl, _, fcont)) = def in
  let { nparams; locals; body = lbs } = fcont in

  (* Compute the interference graph. *)
  let vvs = vector_vars locals in
  let conflicts_init = make_graph LocUgraph.empty lbs vvs in

  (* Patch the interference graph by adding %rsp edges
     to any variables which aren't in the graph. *)
  let locals_set = VarSet.of_list (List.map fst locals) in
  let conflicts = add_extra_rsp_edges conflicts_init locals_set in
  (* CHECKME: Uncomment this line to test what happens
     if extra %rsp edges are _not_ added: *)
  (* let conflicts = conflicts_init in *)

  (* Put the definition back together. *)
  let lbs' = replace_binfo lbs in
  let finfo = Finfo2 { conflicts } in
  let fcont' = { nparams; locals; body = lbs' } in
    Def (lbl, finfo, fcont')

let build_interference
    (prog : (finfo1, binfo2) program) : (finfo2, binfo1) program =
  let (X86Program defs) = prog in
    X86Program (List.map build_interference_def defs)

