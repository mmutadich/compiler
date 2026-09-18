open X86_asm


let is_mem = function
  | Reg _ | Deref _ -> true
  | _ -> false

(* Return `false` if an instruction has no effect.
   This makes it easy to filter them out. *)
let has_effect instr =
  match instr with
  | Addq (Imm 0, dst) ->
    if is_mem dst then false else true
  | Addq (src, Imm 0) ->
    if is_mem src then false else true
  | Subq (Imm 0, dst) ->
    if is_mem dst then false else true
  | Subq (src, Imm 0) ->
    if is_mem src then false else true
  | Movq (src, dst) ->
    if src = dst then false else true
  | _ -> true

(* Remove the second of a pair of reciprocal moves
   i.e. `movq X Y` followed by `movq Y X`.
   Also remove the second `movq` if it's identical to the first. *)
let trim_reciprocal_moves (ins : instr list) : instr list =
  let rec trim (last_movq : (arg * arg) option) (instrs : instr list) (acc : instr list) : instr list =
    match instrs with
    | [] -> List.rev acc
    | (Movq (src, dst)) as curr_movq :: rest ->
      (match last_movq with
       | Some (last_src, last_dst) ->
         if (src = last_dst && dst = last_src) || (src = last_src && dst = last_dst) then
           trim last_movq rest acc
         else
           trim (Some (src, dst)) rest (curr_movq :: acc)
       | _ ->
         trim (Some (src, dst)) rest (curr_movq :: acc))
    | instr :: rest ->
      trim None rest (instr :: acc)
  in
  trim None ins []
    
    

let optimize (prog : program) : program =
  let (X86Program instrs) = prog in
    let instrs' =
      instrs
        |> List.filter has_effect
        |> trim_reciprocal_moves
    in
      X86Program instrs'
