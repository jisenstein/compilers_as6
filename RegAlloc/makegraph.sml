(* makegraph.sml *)

signature MAKEGRAPH = 
sig
  val instrs2graph : Assem.instr list -> Flow.flowgraph * Flow.Graph.node list
  val instrs : Assem.instr list
  val test : unit -> unit
  val test_generic : Assem.instr list -> unit
  val printNodes : Graph.node list -> unit
end

structure MakeGraph : MAKEGRAPH =
struct

(* The "instrs2graph" function takes a list of assembly instructions,
   and constructs its flowgraph and also returns the list of nodes in 
   the flowgraph. The instructions exactly correspond to the nodes in 
   the graph. If instruction m can be followed by instruction n (either
   by a jump or by falling through), there should be an edge from m to n
   in the graph.

   The flowgraph also maintains several attributes for each node in the 
   graph, i.e., the "def" set, the "use" set, and the "ismove" flag

 *)

  fun instr2graph(Assem.OPER({assem=a, dst=d, src=s, jump=NONE})::rest,
                  fgraph as Flow.FGRAPH({control=control, def=defs, use=uses, ismove=im}),
                  nodes,
                  labels_master,
                  index) =
      let
        val node = List.nth(nodes, index);
        val new_defs = Graph.Table.enter(defs, node, d);
        val new_uses = Graph.Table.enter(uses, node, s);
        val new_ismove = Graph.Table.enter(im, node, false);
      in
        (if (rest = nil)
         then ()
         else Graph.mk_edge{from=node, to=List.nth(nodes, index + 1)};
         instr2graph(rest, Flow.FGRAPH{control=control, def=new_defs, use=new_uses, ismove=new_ismove},
                     nodes, labels_master, index+1))
      end

     | instr2graph(Assem.OPER({assem=a, dst=d, src=s, jump=SOME(labels)})::rest,
                   fgraph as Flow.FGRAPH({control=control, def=defs, use=uses, ismove=im}),
                   nodes,
                   labels_master,
                   index) =
       let
         val node = List.nth(nodes, index);
         val new_defs = Graph.Table.enter(defs, node, d);
         val new_uses = Graph.Table.enter(uses, node, s);
         val new_ismove = Graph.Table.enter(im, node, false);
       in
         (makeLabelEdges(node, nodes, labels, labels_master);
         instr2graph(rest, Flow.FGRAPH{control=control, def=new_defs, use=new_uses, ismove=new_ismove},
                     nodes, labels_master, index+1))
       end

     | instr2graph(Assem.LABEL({assem=a, lab=l})::rest,
                   fgraph,
                   nodes,
                   labels_master,
                   index) =
       (if (rest = nil)
       then ()
       else Graph.mk_edge{from=List.nth(nodes, index), to=List.nth(nodes, index+1)};
        instr2graph(rest, fgraph, nodes, labels_master, index+1))
     
     | instr2graph(Assem.MOVE({assem=a, dst=d, src=s})::rest,
                   fgraph,
                   nodes,
                   labels_master,
                   index) =
       instr2graph(rest, fgraph, nodes, labels_master, index+1)
     | instr2graph (nil, graph, nodes, labels_master, index) = (graph, nodes)

  and makeNodes(instr::rest, graph) = Graph.newNode(graph)::makeNodes(rest, graph)
  |   makeNodes(nil, graph) = nil
 
  and makeLabels(Assem.LABEL({assem=a, lab=l})::rest, index) = (l, index)::makeLabels(rest, index+1)
  | makeLabels(ins::rest, index) = makeLabels(rest, index+1)
  | makeLabels(nil, index) = nil

  and matchLabel((l, index)::rest, label) =
    if (label = l) then index else matchLabel(rest, label)
  | matchLabel(nil, label) = ~1

  and makeLabelEdges(node, nodes, label::rest, labels_master) =
   (Graph.mk_edge{from=node, to=List.nth(nodes, matchLabel(labels_master, label))};
    makeLabelEdges(node, nodes, rest, labels_master))
  | makeLabelEdges(node, nodes, nil, labels_master) = ()

  fun instrs2graph(instrs) =
    let
      val control = Graph.newGraph();
      val nodes = makeNodes(instrs, control);
      val defs = Graph.Table.empty;
      val uses = Graph.Table.empty;
      val im = Graph.Table.empty;
      val fgraph = Flow.FGRAPH{control=control, def=defs, use=uses, ismove=im};
      val labels = makeLabels(instrs, 0);
    in
      instr2graph(instrs, fgraph, nodes, labels, 0)
      (* (fgraph, nodes) *)
    end

 (*  debug functions    *)
  fun sym(x) = Symbol.symbol(x);
  val I1 = Assem.OPER({assem="I1", dst=[1], src=[], jump=NONE});
  val L1 = Assem.LABEL({assem="L1", lab=sym("I2")});
  val I2 = Assem.OPER({assem="I2", dst=[2], src=[1], jump=NONE});
  val I3 = Assem.OPER({assem="I3", dst=[3], src=[2,3], jump=NONE});
  val I4 = Assem.OPER({assem="I4", dst=[1], src=[2], jump=NONE});
  val I5 = Assem.OPER({assem="I5", dst=[], src=[1],
      jump=SOME([sym("I2"), sym("I6")])});
  val L2 = Assem.LABEL({assem="L2", lab=sym("I6")});
  val I6 = Assem.OPER({assem="I6", dst=[], src=[3], jump=NONE});
  val instrs = (I1::L1::I2::I3::I4::I5::L2::I6::nil);

  fun printLabels((l,index)::rest, n) = (print("label " ^ Int.toString(index) ^ " is " ^ Symbol.name(l) ^ "\n");
                                      printLabels(rest, n + 1))
  | printLabels(nil, n) = ()

  fun printSuccPred(node::rest) =
    (
        print(Graph.nodename(node) ^ ", ");
        printSuccPred(rest)
    )
  | printSuccPred(nil) = print("\n")

  fun printNodes(node::rest) =
    (
        print("Nodename: " ^ Graph.nodename(node) ^ "\n");
        printSuccPred(Graph.adj(node));
        print("\n");
     (*   print("succ: ");
        printSuccPred(Graph.succ(node));
        print("pred: ");
        printSuccPred(Graph.pred(node));
        print("\n"); *)
        printNodes(rest)
    )
  | printNodes(nil) = ()

  fun printGraph(fg as Flow.FGRAPH{control=c, def=d, use=u, ismove=i}, nodes) =
    (
      print("def table: \n");
      printDefUse(d, nodes);
      print("use table: \n");
      printDefUse(u, nodes)
    )
  and printDefUse(table, node::rest) =
    (
      print("Nodename: " ^ Graph.nodename(node) ^ ": ");
      print(printTemps(getOpt(Graph.Table.look(table, node), [~1])));
      printDefUse(table, rest)
    )     
  | printDefUse(table, nil) = nil

  and printTemps(temp::rest) = (Int.toString(temp) ^ "," ^ printTemps(rest))
    | printTemps(nil) = "\n"

  fun test() = 
    let
      val (fg, nodes) = instrs2graph(instrs);
    in
      (
      printGraph(fg, nodes);
      printNodes(nodes);
      ()
      )
    end
  
  fun test_generic(instructions) = 
    let
      val (fg, nodes) = instrs2graph(instructions);
    in
      (
      printGraph(fg, nodes);
      printNodes(nodes); ()
      )
    end

end
