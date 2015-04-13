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
      val old_out = #3List.nth(db, index);
    
      val use = getOpt(Graph.Table.look(uses, node), []);
      val def = getOpt(Graph.Table.look(defs, node), []);

      val diff = subLists(old_out, def);

      val new_in = combine(use, diff);
      val new_out = combineMult(new_in, Graph.succ(node));
    in
      computeLiveness(fgraph, nodes, index-1, db)
    end
    )
   else (#2List.nth(db, index), #3List.nth(db, index))
     


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




