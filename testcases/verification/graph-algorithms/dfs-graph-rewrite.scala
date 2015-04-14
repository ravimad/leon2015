import scala.collection.immutable._
import leon.annotation._

object Graph {

  sealed abstract class NodeList
  case class Cons(node: Node, tail: NodeList) extends NodeList
  case class Nil() extends NodeList

  case class Node(id: BigInt)
  case class Edge(src: Node, dst: Node)
  case class Graph(nodes: NodeList, adjlist: Map[Node, NodeList])

  def contains(nl: NodeList, key: Node): Boolean = {
    nl match {
      case Nil() =>
        false
      case Cons(n, tail) =>
        if (n == key)
          true
        else contains(tail, key)
    }
  } ensuring (res => (res && Set(key).subsetOf(contents(nl))) ||
    (!res && !Set(key).subsetOf(contents(nl))))

  /*def containsAll(nl: NodeList, keys: NodeList) : Boolean = {
    keys match {
      case Nil() => 
        true
      case Cons(n, tail) =>
        contains(nl, n) && containsAll(nl, tail) 
    }
  }*/

  def size(nl: NodeList): BigInt = {
    nl match {
      case Nil() =>
        0
      case Cons(n, tail) =>
        1 + size(tail)
    }
  } ensuring (_ >= 0)
  
  def nodeSize(g: Graph) : BigInt = {
    size(g.nodes)
  }
  
  def sumSuccs(g: Graph, nodes: NodeList) : BigInt = {
    nodes match {
      case Nil() => 
        0
      case Cons(n, tail) => 
        size(getSuccs(g, n)) + sumSuccs(g, tail) 
    }
  } ensuring(_ >= 0)
  
  def edgeSize(g: Graph) : BigInt = {
    sumSuccs(g, g.nodes)
  }
  
  def graphSize(g: Graph) : BigInt = {
    nodeSize(g) + edgeSize(g)
  }

  def isDistinct(nl: NodeList): Boolean = {
    nl match {
      case Nil() =>
        true
      case Cons(n, tail) =>
        !contains(tail, n) && isDistinct(tail)
    }
  }

  def contents(nl: NodeList): Set[Node] = {
    nl match {
      case Nil() =>
        Set[Node]()
      case Cons(n, tail) =>
        Set(n) ++ contents(tail)
    }
  }

  def getSuccs(g: Graph, node: Node): NodeList = {
    g.adjlist(node)

  } ensuring (res => contents(res).subsetOf(contents(g.nodes)) &&
    isDistinct(res) &&
    !Set(node).subsetOf(contents(res))) //disallowing self edges as of now

  def append(l1: NodeList, l2: NodeList): (NodeList, BigInt) = {
    require(isDistinct(l1) && isDistinct(l2))
    l1 match {
      case Nil() =>
        (l2, 1)
      case Cons(n, tail) =>
        val (res, t) = append(tail, l2)
        if (!contains(res, n))
          (Cons(n, res), t + 1)
        else
          (res, t + 1)
    }
  } ensuring (res => isDistinct(res._1) && 
      contents(res._1) == contents(l1) ++ contents(l2) && 
      res._2 <= size(l1) + 1)

  /**
   * Requires that 'key' is contained in 'nodes'.
   */
  def remove(nodes: NodeList, key: Node): NodeList = {
    require(Set(key).subsetOf(contents(nodes)) && isDistinct(nodes))
    nodes match {
      case Nil() =>
        Nil()
      case Cons(n, tail) if n == key =>
        tail
      case Cons(n, tail) =>
        Cons(n, remove(tail, key))
    }
  } ensuring (res => (contents(res) == contents(nodes) -- Set(key)) &&
      isDistinct(res) &&
    (size(res) == size(nodes) - 1))
       
    
  def removeNode(g: Graph, n: Node): Graph = {
    require(Set(n).subsetOf(contents(g.nodes)) && isDistinct(g.nodes))
    
    Graph(remove(g.nodes, n), g.adjlist)
    
  } ensuring(res => nodeSize(res) == nodeSize(g) - 1 && 
      edgeSize(res) == edgeSize(g) - size(getSuccs(g, n)))
/*
  def lemma(g: Graph, stack: NodeList) = {
    require(isDistinct(g.nodes) && isDistinct(stack) && contents(stack).subsetOf(contents(g.nodes)))
    stack match {
      case Nil() =>
        (Nil(), Nil())
      case Cons(n, tail) =>
        val succs = getSuccs(g, n)
        val newnodes = remove(g.nodes, n)
        val newstack = append(succs, tail)
        (newnodes, newstack) 
    }
  } ensuring(res => isDistinct(res._1) &&    
      isDistinct(res._2) &&       
      contents(res._2).subsetOf(contents(res._1)) && //checks for precondition 
      (stack == Nil() || size(res._1) < size(g.nodes))) //checks a property
*/
  def dfs(g: Graph, stack: NodeList) : (NodeList, BigInt) = {
    require(isDistinct(g.nodes) && isDistinct(stack) && 
        contents(stack).subsetOf(contents(g.nodes)))
    stack match {
      case Nil() =>
        (Nil(), 1)
      case Cons(n, tail) =>
        val succs = getSuccs(g, n) //constant time
        //val newnodes = remove(g.nodes, n) //constant time
        val newgraph = removeNode(g, n)
        val (newstack, appendTime) = append(succs, tail) //time O(succs)
        val (reach, recTime) = dfs(newgraph, newstack)
        (reach, appendTime + recTime + 1)
    }
  } ensuring(res => res._2 <= 2*graphSize(g) + 1)
  
  /* def dfs(g: Graph, stack : NodeList) : (BigInt, NodeList) = {
    require(isDistinct(stack) && contents(stack).subsetOf(contents(g.nodes)))
    g.nodes match { 
      case Nil() => 
        (1, stack)
      case _  => stack match {
      	case Nil() => 
      		(1, Nil())
      	case Cons(n, tail) => 
      		val succs = getSuccs(g, n)
      		val succs2 = 
      		  if(contains(succs, n))
      			remove(succs, n)
      			else succs
      		val newnodes = remove(g.nodes, n)
      		val newgraph = Graph(newnodes, g.adjlist)      		
      		val newstack = append(succs, tail, newgraph)      		
      		val (t, res) = dfs(newgraph, newstack)
      		(t + 1, res)
      }        
    }
  } ensuring(res => res._1 <= size(g.nodes) + 1)*/
}
