import leon.annotation._
import Graph._

object GraphBFS {
    
  /**
   * Assuming an imperative implementation that runs O(1)
   * time for enqueue and dequeue
   */
  def appendQueue(q: NodeList, elems: NodeList) : (NodeList, BigInt) = { 
    //require(isDistinct(q) && isDistinct(elems))
    //using list append, but ideally this will have smaller running time
    val (res, t) = append(q, elems)
    (res, 1)
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
        val (newqueue, appendTime) = appendQueue(tail, succs) //constant time 
        val (finalg, reach, recTime) = bfs(newgraph, newqueue)
        (finalg, Cons(n, reach), appendTime + recTime + 1)
    }
  } ensuring (res => //invaraints of resg
    	validGraph(res._1) && 
    	contents(res._1.nodes) == contents(g.nodes) && // only edges are removed
    	res._3 <= 5 * (edgeSize(g) - edgeSize(res._1)) + 2 * size(queue) + 1)  
  
  def bfsVertex(g: Graph, v : Node) : (Graph, NodeList, BigInt) = {
    require(validGraph(g) && contents(g.nodes).contains(v))
    
    val (rg, rl, t) = bfs(g, Cons(v, Nil()))
    (rg, rl, t + 1)
    
  } ensuring (res => res._3 <= 5 * (edgeSize(g) - edgeSize(res._1)) + 4 && 
      contents(res._1.nodes) == contents(g.nodes) && // only edges are removed 
      validGraph(res._1))       
  
  //iterate over all vertices and invoke `bfsVertex` on each
  def bfsVertices(g: Graph, vs : NodeList) : (Graph, NodeList, BigInt) = {
    require(validGraph(g) && contents(vs).subsetOf(contents(g.nodes)))    
    vs match {
      case Nil() => 
        (g, Nil(), 1)
      case Cons(n, tail) =>
        val (ng1, nl1, t1) = bfsVertex(g, n)
        val (ng2, nl2, t2) = bfsVertices(ng1, tail)
        val (fl, t3) = appendQueue(nl1, nl2)
        (ng2, fl, t1 + t2 + t3 + 1)
    }
  } ensuring (res => validGraph(res._1) && 
      res._3 <= 5 *(edgeSize(g) - edgeSize(res._1)) + 6*size(vs) + 1)
  
  /**
   * Proven the complete running time of BFS
   */
  def bfsComplete(g: Graph) : (Graph, NodeList, BigInt) = {
    require(validGraph(g))
    
    val (ng, reach, t) = bfsVertices(g, g.nodes) //ng will not have any edges here
    (ng, reach, t +1)
    
  } ensuring (res => res._3 <= 6*graphSize(g) + 2)  
}
