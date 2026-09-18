
open Support
open Utils
open Types
open X86_var_def

module M = LabelMap
module G = LabelDgraph

(*

Algorithm:

- Convert the (label, block) list into a label graph
  (a directed graph, using the `LabelDgraph` module).
- Find all blocks which have only a single out edge.
- If the target of these out edges has only a single in edge,
    merge the two blocks.
- Repeat until there are no more mergeable blocks.

*)

(* Get a list of all the jump labels in a block.
   NOTE: This is not the same as the similarly-named function
   from the `Ctup` module. *)
let get_jump_labels (Block (_, instrs) : 'a block) : label list =
    List.fold_left( fun acc instr ->
    match instr with
    | Jmp label -> label :: acc
    | JmpIf (_, label) ->  label :: acc
    | _ -> acc
    ) [] instrs

let make_graph (lbs : (label * 'a block) list): LabelDgraph.t =
    let create_edges = 
    List.fold_left (fun lst (lbl, block) ->
      let next_labels = get_jump_labels block in 
      let edges = 
        List.fold_left( fun lst (Label next) ->
          if String.ends_with ~suffix:"_conclusion" next 
            then lst
          else (lbl, (Label next)) :: lst
        ) [] next_labels
      in
      lst @ edges
    ) [] lbs
  in
    LabelDgraph.of_list create_edges

(* Get a pair of mergeable labels from the graph if there are any. *)
let get_mergeable_labels (g : G.t) : (label * label) option =
    let rec find_label (vertices : label list) : (label * label) option =
    (match vertices with 
    | [] -> None
    | vertex :: rest -> 
      let child = LabelDgraph.neighbors_out g vertex in
      if List.length child == 1 && LabelDgraph.neighbors_in g (List.hd child) = [vertex]
        then Some (vertex, (List.hd child))
      else
        find_label rest)
  in
    find_label (LabelDgraph.vertices g)

(* Merge two blocks. *)
let merge_blocks (b1 : 'a block) (b2 : 'a block) : 'a block =
  let (Block (label , instrs1)) = b1 in 
  let (Block (_, instrs2)) = b2 in 
  let all_but_jump = butlast instrs1 in
  Block (label,  all_but_jump @ instrs2)

(* Merge two blocks A and B if block A only jumps to block B
   and block B is only jumped to from block A.
   The merged block will have the label of the original block A. *)
let process_blocks (lbs : (label * 'a block) list): ((label * 'a block) list) =
  if List.length lbs < 2 then
    lbs (* no blocks to merge! *)
  else
    let rec merge_blocks_rec ( lbs : 'a block LabelMap.t) (g : G.t):  ((label * 'a block) list) =
      match get_mergeable_labels g with
      | Some (b1_label, b2_label) -> 
        let b1 = LabelMap.find b1_label lbs in
        let b2 = LabelMap.find b2_label lbs in
        let new_block = merge_blocks b1 b2 in
        let remove_b2 = LabelMap.remove b2_label lbs in
        let replace_b1 = LabelMap.add b1_label new_block remove_b2
        in
          merge_blocks_rec replace_b1 (LabelDgraph.merge_vertices g b1_label b2_label)
      | None -> LabelMap.bindings lbs
    in
      merge_blocks_rec (LabelMap.of_list lbs) (make_graph lbs)

let remove_jumps_def (def : ('a, binfo1) def) : ('a, binfo1) def =
  (* Unpack the labeled block list (`lbs`) from a definition. *)
  let (Def (lbl, finfo, fcont)) = def in
  let { nparams; locals; body = lbs } = fcont in

  (* Remove the unnecessary jumps. *)
  let lbs' = process_blocks lbs in

  (* Put the definition back together. *)
  let fcont' = { nparams; locals; body = lbs' } in
    Def (lbl, finfo, fcont')

let remove_jumps
    (prog : ('a, binfo1) program) : ('a, binfo1) program =
  let (X86Program defs) = prog in
    X86Program (List.map remove_jumps_def defs)
