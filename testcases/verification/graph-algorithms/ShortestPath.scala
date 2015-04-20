import leon.annotation._
import Graph._

object ShortestPath {  
  
  def removeMin(q : NodeList, dist: Map[Node,BigInt]) : (Node, NodeList) ={
    require(size(q) >= 1)    
    q match {
      case Cons(x, Nil()) => 
        (x, Nil())
      case Cons(x, tail) =>
        val (y, q1) = removeMin(tail, dist)
        if(dist(y) <= dist(x))
          (y, Cons(x, q1)) 
        else
          (x, Cons(y, q1)) //here `y` is reshuffled a bit but it still holds
    }        
  } ensuring(res => size(res._2) == size(q) - 1 && 
      contents(res._2).subsetOf(contents(q)) &&
      contains(q, res._1))
        
  def weight(g: Graph, src: Node, dst: Node) : BigInt ={
    //for now implementing this as a constant
    1
  }
  
  def updateDist(g : Graph, root: Node, succs : NodeList, dist : Map[Node,BigInt], prev : Map[Node,Node]) 
  	: (Map[Node,BigInt], Map[Node,Node]) = {
    succs match {
      case Nil() => 
        (dist, prev)
      case Cons(n, tail) =>
        val alt = dist(root) + weight(g, root, n) //this is a consant time operation
        val (ndist, nprev) = if(dist(n) <= alt) {
          (dist, prev)
        } else {
          (dist.updated(n, alt), prev.updated(n, root))
        }
        updateDist(g, root, tail, ndist, nprev)
    }
  }   
    
  def shortestPath(g: Graph, queue: NodeList, dist : Map[Node,BigInt], prev: Map[Node,Node])
  	: (Graph, Map[Node, BigInt], Map[Node,Node], BigInt) = {  	  
    require(validGraph(g) && contents(queue).subsetOf(contents(g.nodes)))             
    queue match {
      case Nil() =>
        (g, dist, prev, 1)
      case _ =>
        val (minElem, nqueue) = removeMin(queue, dist) //O(size(queue))
        val succs = getSuccs(g, minElem) //constant time       
        val newgraph = removeSuccEdges(g, minElem) //we don't have to look at the minimum element again        
        //update the dist and prev
        val (dist1, prev1) = updateDist(g, minElem, succs, dist, prev)  //O(succs)        
        val (fg, dist2, prev2, recTime) = shortestPath(newgraph, nqueue, dist1, prev1)
        (fg, dist2, prev2, size(queue) + size(succs) + recTime + 1)
    }
  } ensuring (res => //invaraints of resg
    	validGraph(res._1) && 
    	contents(res._1.nodes) == contents(g.nodes) && // only edges are removed
    	res._4 <= 2*(edgeSize(g) - edgeSize(res._1)) + size(queue) * size(queue) + size(queue) + 1)   
    	
   //this would give a O(|E| + |V|^2) bound 
}
