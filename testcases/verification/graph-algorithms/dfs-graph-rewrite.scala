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
  }
  
  def size(nl : NodeList) : BigInt = {
    nl match {
      case Nil() => 
        0
      case Cons(n, tail) => 
        1 + size(tail)
    }
  }
    
  
  def getSuccs(g: Graph, node: Node) : NodeList = {
    g.adjlist(node)
  }
  
  def append(succs : NodeList, stack : NodeList) : NodeList = succs match {
    case Nil() => 
      stack
    case Cons(n, tail) if !contains(stack, n) => 
      Cons(n, append(tail, stack))
  }
  
  def remove(nodes: NodeList, key : Node) = nodes match {
    case Nil() => 
      Nil()
    case Cons(n, tail) if n == key => 
      tail
    case Cons(n, tail) => 
      Cons(n, remove(tail, key))
  }
  
  def dfs(g: Graph, stack : NodeList) : NodeList = g match {
    case (Nil(), nl) => 
      stack
    case _  => stack match {
      case Nil() => 
        Nil()
      case Cons(n, tail) => 
        val succs = getSuccs(g, n)
        val newnodes = remove(g.nodes, n)
        dfs(Graph(newnodes, nl), append(succs, stack))  
    }        
  }
}
