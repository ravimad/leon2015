import leon.annotation._
import Graph._

object GraphBFS {
    
  /**
   * Assuming an imperative implementation that runs O(1)
   * time for enqueue and dequeue
   */
  def appendQueue(q: NodeList, elems: NodeList) : (NodeList, BigInt) = { 
    require(isDistinct(q) && isDistinct(elems))
    //using list append, but ideally this will have smaller running time
    val (res, t) = append(q, elems)
    (res, size(elems) + 1)
  } 
  
  def bfs(g: Graph, queue: NodeList): (NodeList, BigInt) = {
    require(validGraph(g) &&
        isDistinct(queue) && contents(queue).subsetOf(contents(g.nodes)))        
    queue match {
      case Nil() =>
        (Nil(), 1)
      case Cons(n, tail) =>
        val succs = getSuccs(g, n) //constant time       
        val newgraph = removeSuccEdges(g, n)
        val (newqueue, appendTime) = appendQueue(tail, succs) //time O(succs)
        val (reach, recTime) = bfs(newgraph, newqueue)
        (Cons(n, reach), appendTime + recTime + 1)
    }
  } ensuring (res => res._2 <= 6 * edgeSize(g) + 2 * size(queue) + 1)
  
  def bfsVertex(g: Graph, v : Node) : (NodeList, BigInt) = {
    require(validGraph(g) && contents(g.nodes).contains(v))
    
    bfs(g, Cons(v, Nil()))
    
  } ensuring (res => res._2 <= 6 * edgeSize(g) + 3)
  
  
}
