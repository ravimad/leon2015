import leon.annotation._
import Graph._

object GraphDFS {

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
