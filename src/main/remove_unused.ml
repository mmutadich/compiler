open Types
open Cfun


(* Return all the (label, tail) pairs that are reachable
   from the "start" label. *)
let process_blocks (lts : (label * tail) list) : (label * tail) list =
  let rec find_reachable (lbl : label) (tail_map : tail LabelMap.t) (reachable : tail LabelMap.t ) : tail LabelMap.t =
    let tail = LabelMap.find lbl tail_map in
    let rec add_blocks (lbls : label list) (tail_map : tail LabelMap.t) (reachable : tail LabelMap.t ) : tail LabelMap.t = 
      match lbls with
      | [] -> reachable
      | [next_label] -> 
            if LabelMap.mem next_label reachable
              then reachable
            else find_reachable next_label tail_map (LabelMap.add next_label tail reachable)
      | next_label :: rest -> 
         let next_label_map = find_reachable next_label tail_map (LabelMap.add next_label tail reachable) in
        add_blocks rest tail_map next_label_map
    in 

      add_blocks (get_jump_labels tail) tail_map (LabelMap.add lbl tail reachable)
  in 
  LabelMap.bindings (find_reachable (Label ("start")) (LabelMap.of_list lts) (LabelMap.empty))
let remove_unused_blocks_def (d : def) : def =
  let Def (lbl, fcont) = d in
  let { args; ret; locals; body } = fcont in
  let body' = process_blocks body in
    Def (lbl, { args; ret; locals; body = body' })

let remove_unused_blocks (prog : program) : program =
  let (CProgram defs) = prog in
    CProgram (List.map remove_unused_blocks_def defs)

