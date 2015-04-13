(* liveness.sml *)

signature LIVENESS =
sig

  datatype igraph =
      IGRAPH of {graph : Graph.graph,
                 tnode : Graph.node Temp.Table.table,
                 gtemp : Temp.temp Graph.Table.table,
                 moves : (Graph.node * Graph.node) list}

  (*
   *  val interferenceGraph :
   *        Flow.flowgraph -> igraph * (Flow.Graph.node -> Temp.temp list)
   *
   *  val show : outstream * igraph -> unit
   *)
  val removeDuplicates : int list -> int list

end (* signature LIVENESS *)

structure Liveness : LIVENESS =
struct

  datatype igraph =
      IGRAPH of {graph : Graph.graph,
                 tnode : Graph.node Temp.Table.table,
                 gtemp : Temp.temp Graph.Table.table,
                 moves : (Graph.node * Graph.node) list}

  (* To construct the interference graph, it is convenient to
     construct a liveness map at each node in the FlowGraph first.
     For each node in the flowgraph, i.e., for each assembly
     instruction, we want to easily look up the set S of live
     temporaries. 
   *)

  type liveSet = unit Temp.Table.table * Temp.temp list
  type livenessMap = liveSet Flow.Graph.Table.table

  fun computeLiveness(fgraph as Flow.FGRAPH{control=c, def=defs, use=uses, ismove=i},
                      nodes,
                      index,
                      db) =
   if index = 0 then
    (
    let
      val node = List.nth(nodes, index);
      val entry = List.nth(db, index);
    
      val use = getOpt(Graph.Table.look(uses, node), []);
      val def = getOpt(Graph.Table.look(defs, node), []);

      val diff = subLists(entry, def);

      val new_in = removeDuplicates(use @ diff);
      val new_out = removeDuplicates(extractIns(Graph.succ(node), nodes, db));
      val new_db = updateDB(db, new_in, new_out, index, 0);
    in
      computeLiveness(fgraph, nodes, index-1, new_db)
    end
    )
   else 
        (db)

  and subLists((n, ins, outs): int*int list * int list, lst2: int list) =
    List.filter (fn x => List.all (fn y => x <> y) lst2) outs


  and updateDB(elt::db, ins, outs, index, curr) =
    if index = curr then (curr, ins, outs)::db
    else updateDB(db, ins, outs, index, curr+1)
  | updateDB(nil, ins, outs, index, curr) = []

  and extractIns(succ::succs, nodes, db) =
    let
      val index = findIndex(succ, nodes, 0);
      val (n, ins, outs) = List.nth(db, index);
    in
      ins @ extractIns(succs, nodes, db)
    end
  | extractIns(nil, nodes, db) = []

  and findIndex(succ, node::nodes, i) =
      if Graph.nodename(succ) = Graph.nodename(node) then i
      else findIndex(succ, nodes, i+1)
     | findIndex(succ, nil, i) =
       (print("Error: can't find node with name " ^ Graph.nodename(succ)); ~1)
    

  (* adapted from 
  * http://stackoverflow.com/questions/21077272/remove-duplicates-from-a-list-in-sml 
   *)
  and removeDuplicates [] = []
    | removeDuplicates (lst as elt::rest: int list) =
      let fun remove (elt, []) = []
            | remove (elt, l as y::ys: int list) = if elt = y then
                                       remove(elt, ys)
                                       else y::remove(elt, ys)
      in                                      
        elt::removeDuplicates(remove(elt,rest))
      end
 

  fun initializeDataStructure(length, index) = 
    if length = 0 then nil else
    (index, [], [])::initializeDataStructure(length-1, index+1)
    

  (* after constructing the livenessMap, it is quite easy to
     construct the interference graph, just scan each node in
     the Flow Graph, add interference edges properly ... 
   *)

 fun test() =
   let
     val(fg, nodes) = MakeGraph.instrs2graph(MakeGraph.instrs);
     val db = initializeDataStructure(List.length(nodes), 0);
   in
     ()
   end



end (* structure Liveness *)




