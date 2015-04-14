import leon.annotation._
import Graph._

object GraphDFS {  

  def dfs(g: Graph, stack: NodeList): (NodeList, BigInt) = {
    require(isDistinct(g.nodes) && isDistinct(stack) &&
      contents(stack).subsetOf(contents(g.nodes)))      
    stack match {
      case Nil() =>
        (Nil(), 1)
      case Cons(n, tail) =>
        val succs = getSuccs(g, n) //constant time       
        succs match {
          case Nil() =>
            val (reach, recTime) = dfs(g, tail)
            (reach, recTime + 1)
          case _ => 
            val newgraph = removeSuccEdges(g, n) // constant time
            val (newstack, appendTime) = append(succs, tail) //O(succs) time        
            val (reach, recTime) = dfs(newgraph, newstack)
            (reach, appendTime + recTime + 1)
        }        
    }
  } ensuring (res => res._2 <= 3 * edgeSize(g) + size(stack) + 1)
}
