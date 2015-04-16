import leon.annotation._
import Graph._

object GraphDFS {

  def visitNodes(g : Graph, nodes: NodeList, reach: Set[Node]) : (Graph, Set[Node], BigInt) = {
    require(validGraph(g) && contents(nodes).subsetOf(contents(g.nodes)))
    nodes match {
      case Nil() =>
        (g, reach, 1)      
      case Cons(n, tail) =>
        //mark that `n` is reachable        
        //take every successor of `n`, remove edges leading to them, and recurse
        val succs = getSuccs(g, n) //constant time               
        val newgraph = removeSuccEdges(g, n) // constant time               
        val (ng, reach1, t1) = visitNodes(newgraph, succs, reach ++ Set(n)) //recurse into the successors       
        val (fg, reach2, t2) = visitNodes(ng, tail, reach1) //continue the outer iteration
        (fg, reach2, t1 + t2 + 1)
    }
  } ensuring (res => validGraph(res._1) && 
      contents(res._1.nodes) == contents(g.nodes) && // only edges are removed
      res._3 <= 4 *(edgeSize(g) - edgeSize(res._1)) + 2*size(nodes) + 1)
  
  def dfsSimple(g: Graph) : (Graph, Set[Node], BigInt) = {
    require(validGraph(g))
    
    visitNodes(g, g.nodes, Set[Node]())
    
  } ensuring (res => res._3 <= 4 *graphSize(g) + 1)
  
  /**
   * DFS tail recursive
   */
  def dfs(g: Graph, stack: NodeList): (NodeList, BigInt) = {
    require(validGraph(g) && 
        isDistinct(stack) && contents(stack).subsetOf(contents(g.nodes)))        
    stack match {
      case Nil() =>
        (Nil(), 1)
      case Cons(n, tail) =>
        val succs = getSuccs(g, n) //constant time               
        val newgraph = removeSuccEdges(g, n) // constant time
        val (newstack, appendTime) = append(succs, tail) //O(succs) time        
        val (reach, recTime) = dfs(newgraph, newstack)
        (Cons(n, reach), appendTime + recTime + 1)
    }
  } ensuring (res => res._2 <= 6 * edgeSize(g) + 2 * size(stack) + 1)
  
  /**
   * A variant of dfs that checks for cycles
   */
   def hasCycles(g: Graph, stack: NodeList, visited: Set[Node]): (Boolean, BigInt) = {
    require(validGraph(g) && 
        isDistinct(stack) && contents(stack).subsetOf(contents(g.nodes)))        
    stack match {
      case Nil() =>
        (false, 1)
      case Cons(n, tail) if(visited.contains(n)) =>
        (true, 1)
      case Cons(n, tail) =>
        val succs = getSuccs(g, n) //constant time               
        val newgraph = removeSuccEdges(g, n) // constant time
        val (newstack, appendTime) = append(succs, tail) //O(succs) time
        val newvisited = visited ++ Set(n) 
        val (r, recTime) = hasCycles(newgraph, newstack, newvisited) 
        (r, appendTime + recTime + 1)
    }
  } ensuring (res => res._2 <= 6 * edgeSize(g) + 2 * size(stack) + 1)
  
}
