import scala.collection.immutable._
import leon.annotation._

/**
 *  A proof of DFS. 
 *  Not sure if it is expressible in Leon as such.
 *  
 *  dfs(g, x, visited, completed, visited', completed') <-  	 
 *  	 x \in visited ^ visited' = visited ^ completed' = completed 
 *    	 x \in completed ^ visited' = visited ^ completed' = completed
 *    	 x \notin visited ^ completed' = succs(x).fold(completed){ 
 *      				(acc, succ) =>  
 *          				val (v', c') = dfs(g, succ, visited U {x}, acc)
 *              			c'                			 
 *          		} U { x }
 *      	^ visited' = visited 
 * (i) Pre/Post: forall y \in completed. y ->* r => r \in completed v (\exists z \in visited. z ->* r in g \ completed) 		
 *     (holds for primed and unprimed forms)                
 * (ii) Postcondition: visited' = visited        
 * (iii) Postcondition: x \notin visited => x \in completed'
 * 
 * The hardest part is establishing (i). In particular the following subpart
 * Let x ->* r and r != x. Let succ \in succ(x) and succ ->* r.
 * By Hypothesis:   
 * succ ->* r => r \in c' v (\exists z \in (visited U { x }).  z ->* r in g \ c')
 * 	r \in c' => r \in completed' (so this case is easy)
 * Say z \in (visited U { x }). z ->* r in g \ c'
 *  Say z \in visited 
 *  	since visited = visited', 
 *   	z \in visited' and  z ->* r under g \ c'
 *   Say \exists succ'' \in succ(x), s.t., r \in c''
 *   This implies, r \in c (by construction) which contradicts our assumption
 *   Hence, forall succ \in succ(x), r \notin c'
 *   Therefore, by hypothesis,
 *       forall succ \in succ(x), \exists z \in visited.  z ->* r in g \ c'
 *       But, for the `succ` visited last c' = completed' \ { x }
 *       Hence, \exists z \in visited.  z ->* r in g \ (completed' \ { x })
 *       Given, r != x. 
 *       (a) if all paths go through 'x' i.e, z ->* x ->* r 
 *       then they all have to be of the form: z ->* x -> succ ->*_(-x) r in (g \ (completed' U {x}))
 *       But, since (succ \notin visited U { x }) => succ \in (completed'  \ { x}) (by post iii)
 *        which implies succ \notin visited => succ \in (completed'  \ { x}) (by post iii)
 *        (because succ cannot be 'x' by the choice of the path from z to r)
 *       'succ' has to be in 'visited' since we are considering a graph in which (completed' U {x}) are removed.
 *       This implies that 'succ \in visited' and succ ->* r in g \ completed, 
 *       which satisfies the claim
 *       
 *       (b) Otherwise, there exists a path from z to r not going through 'x'.
 *           therefore, z ->* r in g \ completed'          
 * Say z = x.
 * 	 So we have, x ->* r in g \ c'
 *   As before, forall succ \in succ(x), r \notin c'
 *   As before, x ->* r in g \ (completed' \ { x })
 *   This implies that 'r' should be reachable only going through successors of 'x' belonging to 'visited' 
 *   Therefore, succ ->* r in g \ completed, which satisfies the claim   
 * QED.
 * 
 * We also need to establish that the precondition holds for the recursive calls:
 * It suffices to establish it initially, as for the later iteration its holds by the post-condition
 * of the previous iteration. Initially it holds, because we pass  'completed' as it is to recursive 
 * calls, and only increase the size of visited, which will not affect the correctness.
 * 
 * dfsInit(g, x, res) = dfs(g, x, Set(), Set(), visited', completed') ^ res = completed'
 * By (iii) x \in completed'
 * By (ii) visited' = Set()
 * By (i) (post) x ->* r => r \in completed' (the second part does not hold as visited' = Set())
 * Hence, res >= reach(x)
 * The converse is directly provable by induction i.e, r \in completed => x ->* r
 */
object Graph {

  case class Node(id: BigInt)
  case class Edge(src: Node, dst: Node)
  //a graph is a set of nodes with ids 1...nv and a mapping from vertices to incident edges
  case class Graph(nv: BigInt, adjlist: Map[Node, NodeList])
  sealed abstract class NodeList
  case class Cons(node: Node, tail: NodeList) extends NodeList
  case class Nil() extends NodeList

  def contains(nl: NodeList, key: Node): Boolean = {
    nl match {
      case Nil() =>
        false
      case Cons(n, tail) =>
        if (n == key)
          true
        else contains(tail, key)
    }
  }
  
  def size(nl : NodeList) : BigInt = {
    nl match {
      case Nil() => 
        0
      case Cons(n, tail) => 
        1 + size(tail)
    }
  }
  
  def add(nl: NodeList, e : Node) : NodeList = {
    nl match {
      case Nil() =>
        Cons(e, Nil())
      case Cons(n, tail) =>
        Cons(n, add(tail, e))
    }
  } ensuring(res => size(res) == size(nl) + 1)
  
  def getSuccs(g: Graph, node: Node) : NodeList = {
    g.adjlist(node)
  }
  
  def iterate(g : Graph, visited :  NodeList, succs : NodeList, x: Node, 
      /**a misc structure*/ visitSuccs : Map[Node,BigInt]) 
  	: (NodeList, Map[Node,BigInt], BigInt) = {
    require(visitSuccs(x) + size(succs) == size(getSuccs(g, x)))
    
    succs match {
      case Nil() =>
        (visited, visitSuccs, 1)
      case Cons(n, tail) =>        
        val (nvisited, nsuccs, cnt1) = dfs(g, visited, n,  visitSuccs)
        //nsuccs is actually ignored for now
        val (fvisit, fsuccs, cnt2) = iterate(g, nvisited, tail, x, 
             visitSuccs.updated(x, visitSuccs(x) + 1))
        (fvisit, fsuccs, cnt1 + cnt2)
    }
  } ensuring(res => {
	  size(res._1) >= size(visited) &&
	  (succs == Nil() || res._2(x) > visitSuccs(x)) &&
	  (res._2(x) == size(getSuccs(g,x)))  
  })
 
  def dfs(g: Graph, visited: NodeList, n: Node,
      /**a misc structure*/ visitSuccs : Map[Node,BigInt])
      : (NodeList, Map[Node,BigInt], BigInt) = {	    
	    
	if(contains(visited, n)){
	  (visited, visitSuccs, 1)
	} else {
	  //iterate over succs	  
	  val ivisit = visitSuccs.updated(n, BigInt(0))
	  val (nvisited, nsuccs, itercnt) = iterate(g, add(visited, n), 
	      getSuccs(g, n), n, ivisit)
	  (nvisited, nsuccs, itercnt + 1)
	}        
  } ensuring(res => {
	  (contains(visited, n) || size(res._1) > size(visited))	  
  })
}
