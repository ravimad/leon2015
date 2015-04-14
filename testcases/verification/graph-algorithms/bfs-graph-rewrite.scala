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
  
//  def succsSize(g: Graph, nl : NodeList) : BigInt = {
//    require(validGraph(g) && contents(nl).subsetOf(contents(g.nodes)) )
//    
//    nl match {
//      case Nil() =>
//        0
//      case Cons(n, tail) =>
//        size(getSuccs(g, n)) + succsSize(g, tail)
//    } 
//  }
  
  def bfs(g: Graph, orig: Graph, queue: NodeList): (NodeList, Graph, BigInt) = {
    require(validGraph(g) &&
        isDistinct(queue) && contents(queue).subsetOf(contents(g.nodes))) 
        //&& edgeSize(g) <= edgeSize(orig))
        
    queue match {
      case Nil() =>
        (Nil(), g, 1)
      case Cons(n, tail) =>
        val succs = getSuccs(g, n) //constant time       
        val newgraph = removeSuccEdges(g, n)
        val (newqueue, appendTime) = appendQueue(tail, succs) //time O(succs)
        val (reach, finalg, recTime) = bfs(newgraph, orig, newqueue)
        (Cons(n, reach), finalg, appendTime + recTime + 1)
    }
  } ensuring (res => contents(res._1).subsetOf(contents(g.nodes))) 
		  //edgeSize(res._2) == edgeSize(g) - sumSuccs(orig, res._1))
  
  //ensuring (res => res._2 <= 6 * edgeSize(g) + 2 * size(queue) + 1)
  
  /*def bfsVertex(g: Graph, v : Node) : (NodeList, BigInt) = {
    require(validGraph(g) && contents(g.nodes).contains(v))
    
    bfs(g, Cons(v, Nil()))
    
  } *///ensuring (res => res._2 <= 6 * edgeSize(g) + 3)
  
  
}
