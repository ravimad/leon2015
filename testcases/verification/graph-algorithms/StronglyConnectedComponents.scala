import leon.annotation._
import Graph._

object SCC {

  def filterSuccs(succs: NodeList, lowlinks: Map[Node, BigInt]) : (NodeList, BigInt) = {
    require(isDistinct(succs))
    succs match {
      case Nil() => 
        (Nil(), 1)
      case Cons(n, tail) if lowlinks.isDefinedAt(n) => 
        val (r, t) = filterSuccs(tail, lowlinks)
        (r, t + 1)
      case Cons(n, tail) => 
        val (r, t) = filterSuccs(tail, lowlinks)
        (Cons(n, r), t + 1)
    }
  } ensuring(res => isDistinct(res._1) && 
		  contents(res._1).subsetOf(contents(succs)) &&
		  size(res._1) <= size(succs) && res._2 <= size(succs) + 1)	
		 
  def minLowLinks(nodes: NodeList, lowlinks: Map[Node, BigInt]) : (BigInt, BigInt) = {
    nodes match {      
      case Cons(n, Nil()) =>
        (lowlinks(n), 1)
      case Cons(n, tail) => 
        val (r, t) = minLowLinks(tail, lowlinks)
        val l = lowlinks(n)
        if(r <= l)
          (r, t + 1)
        else (l, t + 1)
      case _ => 
        (0, 1)
    }
  } ensuring(res => res._2 <= size(nodes) + 1)
  
   /**
   * Strongly connnected components
   * TODO: need to do something to collect strongly connected components.
   * Probably use a forward propagation. 
   */
  def strongconnect(g: Graph, dfsStack: NodeList,
      index: BigInt, lowlinks: Map[Node, BigInt], onStack : Set[Node]) 
  : (Graph, Map[Node,BigInt], BigInt) = {
    require(validGraph(g) && 
        isDistinct(dfsStack) && contents(dfsStack).subsetOf(contents(g.nodes)))
    
    dfsStack match {
      case Nil() =>
        (g, lowlinks, 1)      
      case Cons(n, tail) if onStack.contains(n) =>
        val (rg, rl, t) = strongconnect(g, tail, index, lowlinks, onStack) //do nothing, but continue with recursion
        (rg, rl, t + 1)
        
      case Cons(n, tail) =>	    
	    val nlowlinks = lowlinks.updated(n, index)
	    val nindex = index + 1	    
	    val nonStack = onStack ++ Set(n)
                
        val (succs, filterTime) = filterSuccs(getSuccs(g, n), lowlinks) //O(succs) time 
        val newgraph = removeSuccEdges(g, n) // constant time
        val (newstack, appendTime) = append(succs, tail) //O(succs) time             
        val (g1, lowlinksPost, succTime) = strongconnect(newgraph, succs, 
            nindex, nlowlinks, nonStack)        
        //compute the minimum of the lowlinks of `n` and all the successors of `n`
        val (minlink, minTime) = minLowLinks(Cons(n, succs), lowlinksPost) //O(succs time)  
        val flowlinks = lowlinksPost.updated(n, minlink)        
        
        //use flow-links for processing tail
        val (rg, rl, tailTime) = strongconnect(g1, tail, nindex, flowlinks, onStack)        
        (rg, rl, filterTime + appendTime + succTime + minTime + tailTime + 1)                               
    }
  } ensuring (res => //invaraints of resg
    	validGraph(res._1) && 
    	contents(res._1.nodes) == contents(g.nodes) && // only edges are removed
    	res._3 <= 15 * (edgeSize(g) - edgeSize(res._1)) + 6 * size(dfsStack) + 1)
}
