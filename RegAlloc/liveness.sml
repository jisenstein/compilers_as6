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
  val test : unit -> unit

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

  fun runAlgo(fgraph, nodes, old_db) =
    let
      val new_db = computeLiveness(fgraph, nodes, List.length(nodes)-1, old_db)
    in
      if testSame(old_db, new_db)
      then (new_db)
      else runAlgo(fgraph, nodes, new_db)
    end

  and testSame((_, old_in, old_out)::old_rest, (_, new_in, new_out)::new_rest) =
    if old_in = new_in andalso old_out = new_out then testSame(old_rest, new_rest)
    else false
 | testSame(nil, nil) = true
 | testSame(_, _) = false


  and computeLiveness(fgraph as Flow.FGRAPH{control=c, def=defs, use=uses, ismove=i},
                      nodes,
                      index,
                      db) =
   if index > ~1 then
    let
      val node = List.nth(nodes, index);
      val entry = List.nth(db, index);
    
      val use = getOpt(Graph.Table.look(uses, node), []);
      val def = getOpt(Graph.Table.look(defs, node), []);

      val diff = subLists(entry, def);

      val new_in = removeDuplicates(use @ diff);
      val new_out = removeDuplicates(extractIns(Graph.succ(node), nodes, db));
      val new_db = updateDB(db, new_in, new_out, Graph.nodename(node));
    in
      computeLiveness(fgraph, nodes, index-1, new_db)
    end
   else 
        (db)

  and subLists((n, ins, outs): string*int list * int list, lst2: int list) =
    List.filter (fn x => List.all (fn y => x <> y) lst2) outs


  and updateDB((c_name, old_in, old_out)::db, ins, outs, name) =
    if c_name = name then (c_name, ins, outs)::db
    else (c_name, old_in, old_out)::updateDB(db, ins, outs, name)
  | updateDB(nil, ins, outs, name) = []

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
  and printDB((n, ins, outs)::rest) =
   (
    print(n ^ ": ");
    print("live-in: ");
    print(printList(ins));
    print("  ------    ");
    print("live-out: ");
    print(printList(outs));
    print("\n");
    printDB(rest)
   )
  | printDB(nil) = ()

 and printList(x::xs) = 
    (Int.toString(x) ^ " " ^ printList(xs))
  | printList(nil) = "."

 

  fun initializeDataStructure(length, node::rest) = 
    if length = 0 then nil else
    (Graph.nodename(node), [], [])::initializeDataStructure(length-1, rest)
    | initializeDataStructure(_, _) = []
    

  (* after constructing the livenessMap, it is quite easy to
     construct the interference graph, just scan each node in
     the Flow Graph, add interference edges properly ... 
   *)
 
 fun test() =
   let
     val(fg, nodes) = MakeGraph.instrs2graph(MakeGraph.instrs);
     val empty_db = initializeDataStructure(List.length(nodes), nodes);
     val final_db = runAlgo(fg, nodes, empty_db);
   in
     (printDB(final_db); ())
   end



end (* structure Liveness *)




