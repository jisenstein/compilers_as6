(* regalloc.sml *)

signature REG_ALLOC =
sig
   structure R : REGISTER_STD
   
   type allocation = Register.register Temp.Table.table

   val color : {interference : Liveness.igraph,
                initial : allocation,
                registers : R.register list} -> allocation

end (* signature REG_ALLOC *)

functor RegAllocGen(Register : REGISTER_STD) : REG_ALLOC =
struct
   structure R : REGISTER_STD = Register

   type allocation = R.register Temp.Table.table

   (* The color function takes an initial allocation table (which assigns
      temporary variables such as FP or SP into certain fixed registers)
      plus an interference graph and a list of registers, and returns
      a new allocation table (mapping from temporaries to registers).

      Notice, you don't need to implement spilling and coalescing. 
      Just do the "simplify" and then do the "select".
    *)

   fun simplify (nodes, stack, gtemp, colors) =
     if List.length(nodes) <> List.length(stack) then
       let
         val pop = removeNode(nodes, nodes, stack, gtemp, colors);
       in
         simplify (nodes, pop::stack, gtemp, colors)
       end
     else stack

   and removeNode(node::rest, nodes, stack, gtemp, colors) =
     let
       val degree = getDegree(node, stack)
     in
       if degree < colors andalso not(exists(node, stack))
       then node
       else removeNode(rest, nodes, stack, gtemp, colors)
     end

     | removeNode(nil, nodes, stack, gtemp, colors) =
       optimistic(nodes, stack)

   and optimistic(node::rest, stack) =
     if exists(node, stack) then optimistic(rest, stack)
     else node
    | optimistic(nil, stack) = Graph.newNode(Graph.newGraph()) (* shouldn't get
    here *)
    
       (* fill in something here *)

   and getDegree(node, stack) =
     let
       val neighbors = removeDuplicates(Graph.adj(node));
       val diff = subLists(neighbors, stack);
     in
        List.length(neighbors) - List.length(diff) - existsInt(node, neighbors)
     end
     
     (* adapted from 
  * http://stackoverflow.com/questions/21077272/remove-duplicates-from-a-list-in-sml 
   *)
  and removeDuplicates [] = []
    | removeDuplicates (lst as elt::rest: Graph.node list) =
      let fun remove (elt, []) = []
            | remove (elt, l as y::ys: Graph.node list) =
            if Graph.nodename(elt) = Graph.nodename(y) then
                                       remove(elt, ys)
                                       else y::remove(elt, ys)
      in                                      
        elt::removeDuplicates(remove(elt,rest))
      end


   and existsInt(node, lst) =
     if exists(node, lst) then 1 else 0
  
  and subLists(elt::rest, lst2) =
    if exists(elt, lst2) then elt::subLists(rest, lst2)
    else subLists(rest, lst2)
  | subLists(nil, lst2) = []

  and exists(node, curr::rest) =
    if Graph.nodename(node) = Graph.nodename(curr) then true
    else exists(node, rest)
  | exists(node, nil) = false

  and nodeToIntList(neighbor::rest) =
    Graph.nodename(neighbor)::nodeToIntList(rest)
    | nodeToIntList(nil) = []

 fun select

   fun color {interference, initial, registers} = (* ... *) initial

end (* functor RegAllocGen *)
