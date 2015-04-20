import leon.annotation._
import Graph._

object DisjointSet {
 
  //We consider a graph that contains all the forests corresponding to the disjoint sets.
  //Every node has a property that it has only one 'successor'. This is an invariant,
  //but not enforced currently.
  
  /**
   * Number of nodes that have a path to 'x'
   */
  def setSize(x: Node, g: Graph) : BigInt = {
    1 + size(transPrev(g, x))
  } ensuring(_ >= 1)  
  
  //Rank invariant
  def validRank(x: Node, g: Graph, rank: Map[Node, BigInt]) : Boolean = {
    rank(x) == size(x, g)    
  }
  
  def validRanks(nl: NodeList, g: Graph, rank: Map[Node, BigInt]) : Boolean = {    
    nl match {
      case Nil() => 
        true
      case Cons(n, tail) =>
        validRank(n, g) && validRanks(tail, g, rank)
    }    
  }
  
  def validDisjointForest(g: Graph, rank: Map[Node, BigInt]) : Boolean {
    validRanks(g.nodes, g, rank)
  }
  
  
  /**
   * Returns the representative of each node
   */
  def find(x: Node, g: Graph) : (Node, Graph) = {    
    getSuccs(g, x) match {      
      case Nil() => 
        //x itself is the root
        x      
      case List(y) =>
        //update 'x' successor as well
        /*val root = find(y, g)
        (root, createEdge(removeSuccs(g, x), x, root))*/
        find(y, g)
      case _ =>
        //doesn't matter what you do here
        x
    }
  } ensuring(res => getSuccs(g, res._1) == Nil()) //the returned node is the root
   
  def union(x : Node, y: Node, rank: Map[Node,BigInt], ig: Graph) : (Map[Node,BigInt], Graph) = {
    require(validDisjointForest(ig, rank) && validRank(x, ig, rank) && validRank(y, ig, rank))
  
     val (xRoot, ng1) = find(x, ig)
     val (yRoot, g) = find(y, ng1)
     if(xRoot == yRoot){
       //nothing to be done as 'x' and 'y' belong to the same set 
       (rank, g)
     } else {
	     // x and y are not already in same set. Merge them.
	     if(rank(xRoot) < rank(yRoot)){
	       //make 'x's successor (parent) 'y'
	       val ng = createEdge(xRoot, yRoot) //constant time operations
	       //no change in rank
	       (rank, ng)
	     } else if(rank(xRoot) > rank(yRoot)) {
	       val ng = createEdge(yRoot, xRoot) 	      
	       (rank, ng)
	     } else {
	       //make 'x' y's parent
	       val ng = createEdge(yRoot, xRoot)
	       //update the rank of 'x'
	       (rank.updated(x, rank(x) + 1), ng) 
	     }       
     }
  }

}
