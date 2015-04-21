import leon.annotation._
import Graph._
import leon.lang._

object DisjointSet {
 
  //We consider a graph that contains all the forests corresponding to the disjoint sets.
  //Every node has a property that it has only one 'successor'. This is an invariant,
  //but not enforced currently.
  
  /**
   * Number of nodes that have a path to 'x'
   */
  def setSize(x: Node, g: Graph) : BigInt = {
    require(validGraph(g))
    
    1 + size(reachTo(g, x)) //every node that can reach 'x'
  } ensuring(_ >= 1)  
  
  //Rank invariant
  def twopower(x: BigInt) : BigInt = {
    require(x >= 0)
    if(x == 0)
        1
        else 
          2 * twopower(x - 1)
  } ensuring(_ >= 0)
  
  def rankBound(x: Node, g: Graph, rank: Map[Node, BigInt]) : Boolean = {
    require(validGraph(g) && rank.isDefinedAt(x) && rank(x) >= 0)
    twopower(rank(x)) <= setSize(x, g)    
  }
  
  def positiveRank(x: Node, rank: Map[Node,BigInt]) : Boolean = {
    rank.isDefinedAt(x) && rank(x) >= 0 
  }
  
  def positiveRanks(nl: NodeList, rank: Map[Node,BigInt]) : Boolean = {
    nl match {
      case Nil() => 
        true
      case Cons(n, tail) => 
        positiveRank(n, rank)  &&  positiveRanks(tail, rank)
    }
  }
  
  def ranksBound(nl: NodeList, g: Graph, rank: Map[Node, BigInt]) : Boolean = {
    require(validGraph(g) && positiveRanks(nl, rank))
    nl match {
      case Nil() => 
        true
      case Cons(n, tail) =>
        rankBound(n, g, rank) && ranksBound(tail, g, rank)
    }    
  }
  
  def validDisjointForest(g: Graph, rank: Map[Node, BigInt]) : Boolean = {
    require(validGraph(g) && positiveRanks(g.nodes, rank))
    
    ranksBound(g.nodes, g, rank)
  }
  
  
  /**
   * Returns the representative of each node
   */
  def find(x: Node, g: Graph, rank: Map[Node,BigInt]) : (Node, Graph) = {    
    require(validGraph(g) && positiveRanks(g.nodes, rank) && 
        validDisjointForest(g, rank) && contents(g.nodes).contains(x)) //auxiliary invariants
    			
    getSuccs(g, x) match {      
      case Nil() => 
        //x itself is the root
        (x, g)      
      case Cons(y, _) => //note: there can be only one successor
        //update 'x' successor as well
        /*val root = find(y, g)
        (root, createEdge(removeSuccs(g, x), x, root))*/
        find(y, g, rank)      
    }
  } ensuring(res => res._2 == g && 
      getSuccs(g, res._1) == Nil() && //the returned node is the root 
      contains(g.nodes, res._1) && 
      positiveRank(res._1, rank)) 
   
  /**
   * Need separation logic for graphs.
   * To prove that from disjoint input graphs, manipulating one graph
   * does not affect the behavior of the other.
   */
  def union(x : Node, y: Node, rank: Map[Node,BigInt], g: Graph) : (Map[Node,BigInt], Graph) = {
    require(validGraph(g) && positiveRanks(g.nodes, rank) && 
        validDisjointForest(g, rank) && 
        contents(g.nodes).contains(x) && contents(g.nodes).contains(y) &&
        //positiveRank(x, rank) && positiveRank(y, rank) &&
        rankBound(x, g, rank) && rankBound(y, g, rank) && 
        disjoint(contents(reachTo(g, x)), contents(reachTo(g, y)))) 
        							//it should ideally suffice to say that ig can be split into disjoint 
        							//graphs g1 and g2, one containing 'x' and other containing 'y'
  
     val (xRoot, _) = find(x, g, rank)
     val (yRoot, _) = find(y, g, rank)
     if(xRoot == yRoot){
       //nothing to be done as 'x' and 'y' belong to the same set 
       (rank, g)
     } else {
	     // x and y are not already in same set. Merge them.
	     if(rank(xRoot) < rank(yRoot)){
	       //make 'x's successor (parent) 'y'
	       val ng = createEdge(g, xRoot, yRoot) //constant time operations
	       //no change in rank
	       (rank, ng)
	     } else if(rank(xRoot) > rank(yRoot)) {
	       val ng = createEdge(g, yRoot, xRoot) 	      
	       (rank, ng)
	     } else {
	       //make 'x' y's parent
	       val ng = createEdge(g, yRoot, xRoot)
	       //update the rank of 'x'
	       (rank.updated(x, rank(x) + 1), ng) 
	     }       
     }
  } ensuring(res => rankBound(x, res._2, res._1) && rankBound(y, res._2, res._1))
}
