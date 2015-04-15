(* liveness.sml *)

signature LIVENESS =
sig

  datatype igraph =
      IGRAPH of {graph : Graph.graph,
                 tnode : Graph.node Temp.Table.table,
                 gtemp : Temp.temp Graph.Table.table,
                 moves : (Graph.node * Graph.node) list}

  
     (*val interferenceGraph :
           Flow.flowgraph -> igraph * (Flow.Graph.node -> Temp.temp list)*)
   
   (* val show : outstream * igraph -> unit *)
  
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


  fun interferenceGraph(fgraph as Flow.FGRAPH{control, use, def, ismove}) =
    let
      val nodes = Graph.nodes(control);
      val empty_db = initializeDataStructure(List.length(nodes), nodes);
      val livenessInfo = runAlgo(fgraph, nodes, empty_db);

      val temps = removeDuplicates(allTemps(nodes, use, def));

      val (igraph, tnode, gtemp) = initIGraph(temps,
                                              Graph.newGraph(),
                                              Temp.Table.empty,
                                              Graph.Table.empty);
      val edge = makeEdges(nodes, def, livenessInfo, tnode);

      fun table_mapping (node : Flow.Graph.node) =
        let 
          fun findIndex(key : Graph.node, curr::rest : Graph.node list, i) =
            if Graph.nodename(key) = Graph.nodename(curr) then i
            else findIndex(key, rest, i+1)
          |  findIndex(key, nil, i) = (print("ERROR"); ~1)
        in
          let
            val index = findIndex(node, nodes, 0);
            val (name, ins, outs) = List.nth(livenessInfo, index);
          in
            outs
          end
        end

    in
      (IGRAPH{graph=igraph, tnode=tnode, gtemp=gtemp, moves=nil}, table_mapping)
      (*igraph*)
    end

  and findLivenessPerNode((name, ins, outs)::rest, node) =
    if Graph.nodename(node) = Graph.nodename(name) then 
      outs
    else findLivenessPerNode(rest, node)
  | findLivenessPerNode(nil, node) = []
  and makeEdges(node::rest, def,
               (n, ins, outs)::lrest, tnode) =
    let
      val current_defs = getOpt(Graph.Table.look(def, node), []);
    in
      (makeEdgesHelper(current_defs, tnode, outs);
       makeEdges(rest, def, lrest, tnode))
    end
 | makeEdges(nil, def, _, tnode) = ()
 | makeEdges(_, def, nil, tnode) = ()
      
  and makeEdgesHelper(def::nil, tnode, outs) = 
     executeEdges(def, tnode, outs)
    | makeEdgesHelper(nil, tnode, outs) = ()

    | makeEdgesHelper(def::rest, tnode, outs) = ()
      
 and executeEdges(def, tnode, out::rest) =
   let
     val from = getOpt(Temp.Table.look(tnode, def), Graph.newNode(Graph.newGraph()));
     val to = getOpt(Temp.Table.look(tnode, out), Graph.newNode(Graph.newGraph()));
   in
     (
       Graph.mk_edge({from=from, to=to});
       executeEdges(def, tnode, rest)
     )
   end
 | executeEdges(tnode, def_name, nil) = ()
    
  and initIGraph(temp::rest, igraph, tnode, gtemp) =
    let
      val node = Graph.newNode(igraph);
      val new_tnode = Temp.Table.enter(tnode, temp, node);
      val new_gtemp = Graph.Table.enter(gtemp, node, temp);
    in
      initIGraph(rest, igraph, new_tnode, new_gtemp)
    end
   | initIGraph(nil, igraph, tnode, gtemp) = (igraph, tnode, gtemp)

  and allTemps(node::rest, use, def) =
    let
      val useList = getOpt(Graph.Table.look(use, node), []);
      val defList = getOpt(Graph.Table.look(def, node), []);
      val comb = useList @ defList;
    in
      comb @ allTemps(rest, use, def)
    end

   | allTemps(nil, use, def) = []


  and runAlgo(fgraph, nodes, old_db) =
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

 

  and initializeDataStructure(length, node::rest) = 
    if length = 0 then nil else
    (Graph.nodename(node), [], [])::initializeDataStructure(length-1, rest)
    | initializeDataStructure(_, _) = []
    

  (* after constructing the livenessMap, it is quite easy to
     construct the interference graph, just scan each node in
     the Flow Graph, add interference edges properly ... 
   *)

 fun printTemps(temp::rest) = (Int.toString(temp) ^ "," ^ printTemps(rest))
    | printTemps(nil) = "\n"

 
 fun test() =
   let
     val(fg, nodes) = MakeGraph.instrs2graph(MakeGraph.instrs);
     val (igraph, function) = interferenceGraph(fg);
     (*val empty_db = initializeDataStructure(List.length(nodes), nodes);
     val final_db = runAlgo(fg, nodes, empty_db);*)
   in
     ()
     (* (MakeGraph.printNodes(Graph.nodes(result)); ()) *)
     (*(printDB(final_db); ()) *)
   end



end (* structure Liveness *)
