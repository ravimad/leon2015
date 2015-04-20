import scala.collection.immutable._
import leon.annotation._

object Graph {

  sealed abstract class NodeList
  case class Cons(node: Node, tail: NodeList) extends NodeList
  case class Nil() extends NodeList

  case class Node(id: BigInt)
  case class Edge(src: Node, dst: Node)
  case class Graph(nodes: NodeList, adjlist: Map[Node, NodeList])

  //list to set
  def contents(nl: NodeList): Set[Node] = {
    nl match {
      case Nil() =>
        Set[Node]()
      case Cons(n, tail) =>
        Set(n) ++ contents(tail)
    }
  }  
  
  //graph invariants    
  def nodeInv(g: Graph, n: Node) : Boolean = {
    !contents(g.nodes).contains(n) || (g.adjlist.contains(n) && {
      isDistinct(g.adjlist(n)) && //distinct successor list
        !contents(g.adjlist(n)).contains(n) && //no self loops (for now)
        contents(g.adjlist(n)).subsetOf(contents(g.nodes)) //succs contained in node set        
    })        
  }
  
  /**
   * For every node the graph invariant holds
   */
  def graphInvRec(g: Graph, nodes : NodeList) : Boolean = {
    nodes match {
      case Nil() => 
        true
      case Cons(v, tail) =>
        nodeInv(g, v) && graphInvRec(g, tail) 
    }
  }
  
  def validGraph(g: Graph) : Boolean = {
    isDistinct(g.nodes) && graphInvRec(g, g.nodes)  
  }   
  
  /**
   * This sort of encapsulates an axiom that when pre holds
   * post also holds
   */
  def getSuccs(g: Graph, node: Node): NodeList = {
    require(contents(g.nodes).contains(node) && validGraph(g))
    
    g.adjlist(node)

  } ensuring (res => nodeInv(g, node))  
  
   //graph size metrics
  def size(nl: NodeList): BigInt = {
    nl match {
      case Nil() =>
        0
      case Cons(n, tail) =>
        1 + size(tail)
    }
  } ensuring (_ >= 0)

  def nodeSize(g: Graph): BigInt = {
    size(g.nodes)
  }

  def sumSuccs(g: Graph, nodes: NodeList): BigInt = {
    require(validGraph(g) && contents(nodes).subsetOf(contents(g.nodes)))    
    nodes match {
      case Nil() =>
        0
      case Cons(n, tail) =>
        size(getSuccs(g, n)) + sumSuccs(g, tail)
    }
  } ensuring (_ >= 0)

  def edgeSize(g: Graph): BigInt = {
    require(validGraph(g))
    
    sumSuccs(g, g.nodes)
  }  

  def graphSize(g: Graph): BigInt = {
    require(validGraph(g))
    
    nodeSize(g) + edgeSize(g)
  }
  
  def succSize(g: Graph,n: Node) : BigInt = {
    require(validGraph(g) && contents(g.nodes).contains(n))
    
    size(getSuccs(g, n))
  }   
  
  //graph operations
  /**
   * This is a constant time operation.
   * Cycles are not allowed as of now.
   */
  def createEdge(g: Graph, src: Node, dst: Node) : Graph = {
    require(validGraph(g) && contents(g.nodes).contains(src) && 
        contents(g.nodes).contains(dst))
    if (src != dst && !contains(g.adjlist(src), dst)) {      
      Graph(g.nodes, g.adjlist.updated(src, Cons(dst, g.adjlist(src))))
    } else
      g
    
  } ensuring(res => validGraph(res) && 
      edgeSize(res) <= edgeSize(g) + 1 && edgeSize(res) >= edgeSize(g) &&
      succSize(res, src) <= succSize(g, src) + 1 && succSize(res, src) >= succSize(g, src) &&
      (src == dst || contents(getSuccs(res, src)).contains(dst)))

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

  def isDistinct(nl: NodeList): Boolean = {
    nl match {
      case Nil() =>
        true
      case Cons(n, tail) =>
        !contains(tail, n) && isDistinct(tail)
    }
  }

  def append(l1: NodeList, l2: NodeList): (NodeList, BigInt) = {    
    l1 match {
      case Nil() =>
        (l2, 1)
      case Cons(n, tail) =>
        val (res, t) = append(tail, l2)
        if (!contains(res, n)) //the time for this is not included
          (Cons(n, res), t + 1)
        else
          (res, t + 1)
    }
  } ensuring (res => (!isDistinct(l1) || !isDistinct(l2) || isDistinct(res._1)) &&    
    contents(res._1) == contents(l1) ++ contents(l2) &&
    size(res._1) <= size(l1) + size(l2) &&
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

  def removeSuccEdges(g: Graph, n: Node): Graph = {
    require(validGraph(g) && contents(g.nodes).contains(n))

    Graph(g.nodes, g.adjlist.updated(n, Nil()))

  } ensuring (res => validGraph(res) && 
      edgeSize(res) == edgeSize(g) - size(getSuccs(g, n)))
}
