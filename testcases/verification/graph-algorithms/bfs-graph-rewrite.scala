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
    
  def bfs(g: Graph, queue: NodeList): (Graph, NodeList, BigInt) = {
    require(validGraph(g) &&
        isDistinct(queue) && contents(queue).subsetOf(contents(g.nodes)))        
        
    queue match {
      case Nil() =>
        (g, Nil(), 1)
      case Cons(n, tail) =>
        val succs = getSuccs(g, n) //constant time       
        val newgraph = removeSuccEdges(g, n)
        val (newqueue, appendTime) = appendQueue(tail, succs) //time O(succs)
        val (finalg, reach, recTime) = bfs(newgraph, newqueue)
        (finalg, Cons(n, reach), appendTime + recTime + 1)
    }
  } ensuring (res => //invaraints of resg
    	validGraph(res._1) && 
    	contents(res._1.nodes) == contents(g.nodes) && // only edges are removed
    	res._3 <= 6 * (edgeSize(g) - edgeSize(res._1)) + 2 * size(queue) + 1)  
  
  def bfsVertex(g: Graph, v : Node) : (Graph, NodeList, BigInt) = {
    require(validGraph(g) && contents(g.nodes).contains(v))
    
    val (rg, rl, t) = bfs(g, Cons(v, Nil()))
    (rg, rl, t + 1)
    
  } ensuring (res => res._3 <= 6 * (edgeSize(g) - edgeSize(res._1)) + 4)
  
  def bfsComplete(g: Graph) : (NodeList, BigInt) = {
    require(validGraph(g))    
    
  }
  
}
