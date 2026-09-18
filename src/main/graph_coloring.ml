open Sexplib.Std

open Support
open Functors
open Types
open Priority_queue

(* Use this to turn debugging code on or off. *)
let _debug_gc = ref false

module type GraphColor =
  sig
    type elt
    type graph
    type pqueue
    type 'a eltmap

    val color : graph -> int eltmap -> int eltmap
  end

module Make (Elt   : OrderedTypeS)
            (EMap  : MapS.S        with type key = Elt.t)
            (PQ    : PriorityQueue with type elt = Elt.t)
            (Graph : Ugraph.S      with type elt = Elt.t):
  GraphColor with type elt       = Elt.t
             and  type 'a eltmap = 'a EMap.t
             and  type pqueue    = PQ.t
             and  type graph     = Graph.t =
  struct
    type elt       = Elt.t
    type 'a eltmap = 'a EMap.t
    [@@deriving sexp]
    type graph     = Graph.t
    type pqueue    = PQ.t

    (* Where node information is stored. *)
    type node_data = {
      color      : int option;
      saturation : IntSet.t;
    }
    [@@deriving sexp]

    (* Map between graph elements and node_data records.
     * This is what gets updated as the algorithm unfolds. *)
    type nodemap = node_data eltmap
    [@@deriving sexp]

    (* ------------------------------------------------------------ *)

    (* Debugging. *)

    let _print_nodemap msg (map : nodemap) : unit =
      Printf.printf "\n%s:\n%s\n\n%!"
        msg (Utils.pretty_print (sexp_of_nodemap map))

    let _string_of_elt (e : elt) : string =
      Elt.sexp_of_t e |> Sexplib.Sexp.to_string

    (* ------------------------------------------------------------ *)

    (* Return `true` if an element's node in a nodemap is uncolored. *)
        let is_uncolored (e : elt) (map : nodemap) : bool =
      let {color ; _} = EMap.find_or_fail e map ~err_msg:"not found" in 
      match color with 
        | None -> true
        | _ -> false
    (* Starting from an initial partial mapping
     * between graph elements and colors (the precolored map),
     * compute an initial nodemap.
     * Also compute the initial saturation sets for all nodes.
     *)
    let initial_nodemap (g : graph) (precolored_map : int eltmap) : nodemap =
      List.fold_left(fun nd_map e -> 
        let neighbors = Graph.neighbors g e in
        let s_set = List.fold_left (fun s elt -> 
          match EMap.find_opt elt precolored_map with
          | Some c -> IntSet.add c s
          | None -> s
          ) IntSet.empty neighbors
        in
        let clr =  
          match EMap.find_opt e precolored_map with
          | Some s -> Some s
          | None -> None
        in
        EMap.add e {color = clr ; saturation = s_set} nd_map
      ) (EMap.empty : node_data EMap.t) (Graph.vertices g)


    (* Initialize the priority queue with uncolored nodes only. *)
    let initial_priority_queue (map : nodemap) : pqueue =
      (* Priority queue elements are (elt, int) pairs,
       * where the int is the priority. *)
      EMap.fold (fun elt {color; saturation} pq ->
        match color with
        | Some _ -> pq
        | None -> PQ.insert elt (IntSet.cardinal saturation) pq
      ) map PQ.empty 

    (* Pick the smallest non-negative integer not in the set. *)
    let pick_color (set : IntSet.t) : int =
      IntSet.fold(fun curr last ->
        if curr < 0 then last 
        else if curr = last then last + 1
        else last
      ) set 0

    (* Add a color to:
     * a) an element's node
     * b) the element's neighbors' saturation maps
     * Also, every time a saturation map increases in size,
     * adjust the element's position in the priority queue.
     *)
    let add_color (g : graph) (e : elt) (c : int)
        (map : node_data eltmap) (pq : PQ.t) : node_data eltmap * PQ.t =
      let msg = "Key not found" in
      let { color = _ ; saturation} = EMap.find_or_fail e map ~err_msg:msg in
      let color_node = EMap.add e {color = (Some c); saturation = saturation} map in
      let neighbors = Graph.neighbors g e in
      List.fold_left( fun (n_map, pq) neigh ->
        let {color; saturation} = EMap.find_or_fail neigh map ~err_msg:msg in
        let new_sat = IntSet.add c saturation in
        let new_map = EMap.add neigh {color = color ; saturation = new_sat} n_map in
        let new_pq = PQ.update neigh (IntSet.cardinal new_sat) pq in 
        (new_map, new_pq)
      ) (color_node, pq) neighbors 

    (* Generate the final int eltmap from the final nodemap. *)
    let make_final_color_map (map : node_data eltmap) : int eltmap =
      EMap.fold (fun elt _ new_map ->
      let {color; _} = EMap.find_or_fail elt map ~err_msg:"not found" in
        match color with
        | Some c -> EMap.add elt c new_map
        | None -> new_map
      ) map (EMap.empty : int EMap.t)

    let color (g : graph) (precolored_map : int eltmap) : int eltmap =
      (* Algorithm:
       * - find the uncolored location with the highest priority
       * - remove it from the queue
       * - pick a color for it based on its neighbor colors
       *   (the saturation set)
       * - add the color to all the neighbors' saturation sets
       *   (updating their places in the priority queue)
       * - continue until the queue is empty
       *)
      let init_map = initial_nodemap g precolored_map in
      let init_pq  = initial_priority_queue init_map in
      let rec iter (map : nodemap) (pq : PQ.t) : nodemap =
        if PQ.is_empty pq then
          map  (* all colors assigned *)
        else
          let (e, pq') = PQ.remove_top pq in
          if not (is_uncolored e map) then
            failwith "color: colored nodes are not allowed in priority queue"
          else
            let node =
              EMap.find_or_fail e map
                ~err_msg:"color: element not in map!"
            in
            let color = pick_color node.saturation in
            let (map', pq'') = add_color g e color map pq' in
              iter map' pq''
      in
        make_final_color_map (iter init_map init_pq)
  end

