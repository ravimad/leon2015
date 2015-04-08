import scala.collection.immutable._
import leon.annotation._

object Graph {

  case class Node(id: Int)
  case class Edge(src: Node, dst: Node)
  //a graph is a set of nodes with ids 1...nv and a mapping from vertices to incident edges
  case class Graph(nv: Int, adjlist: Map[Node, NodeList])
  sealed abstract class NodeList
  case class Cons(node: Node, tail: NodeList) extends NodeList
  case class Nil() extends NodeList

  sealed abstract class Worklist
  case class WCons(nl: NodeList, rest: Worklist) extends Worklist
  case class WNil() extends Worklist

  //checks if a node is a valid node of a graph
  /*
  
  def nodesRec(nid: Int, g : Graph) : Set[Node] = {
    if(nid > g.nv) Set[Node]()
    else{
     Set[Node](Node(nid)) ++ nodesRec(nid + 1, g)
    }
  }
  
  def nodes(g : Graph) : Set[Node] = {
     nodesRec(1, g) 
  }    */
  
  def validNode(node: Node, graph: Graph) : Boolean = {
    node.id >= 1 && node.id <= graph.nv && 
    		graph.adjlist.isDefinedAt(node) 
  }
  
  //checks if edge targets refer to valid vertices
  def validNodes(nodes: NodeList, graph: Graph) : Boolean = {
    nodes match {
      case Cons(node,tail) => 
        validNode(node, graph) && validNodes(tail, graph)            
      case Nil() => true
    }
  }
  
  def validAdjList(nid: Int, graph: Graph) : Boolean = {
    require(nid >= 1)    
    if(nid > graph.nv) true
    else {
      graph.adjlist.isDefinedAt(Node(nid)) && 
      	validNodes(graph.adjlist(Node(nid)), graph) && 
      	validAdjList(nid + 1, graph)             
    }
  } 
  
  def validGraph(graph : Graph) : Boolean ={
    graph.nv >= 1 && validAdjList(1, graph)     
  }
  
  def validNodelist(g: Graph, nodes: NodeList) : Boolean = {
    nodes match {
      case Nil() =>
        true
      case Cons(x, tail) =>
        g.adjlist.isDefinedAt(x) && validNodelist(g, tail)
    }
  }
  
  def validWorklist(g: Graph, wl: Worklist) : Boolean = {
    wl match {
      case WNil() =>
        true
      case WCons(succs, rest) => 
        validNodelist(g, succs) && validWorklist(g, rest)
    }
  }

  def iterate(g: Graph, visited: Set[Node], wl: Worklist): Set[Node] = {
    require(validGraph(g) && validWorklist(g, wl))
    
    wl match {
      case WNil() =>
        visited
      case WCons(succs, rest) =>
        succs match {
          case Nil() =>
            //pop succs from the worklist          
            iterate(g, visited, rest)
          case Cons(x, xs) =>
            val wlMinusX = WCons(xs, rest)
            if (Set(x).subsetOf(visited)) {
              //here, remove 'x' and continue
              iterate(g, visited, wlMinusX)
            } else {
              //traverse 'x' by
              //marking 'x' as visited, removing it from succs, pushing the succs of 'x'          
              iterate(g, visited ++ Set(x), WCons(g.adjlist(x), wlMinusX))
            }
        }
    }
  }

  //a DFS operation on graphs
  def dfs(g: Graph, start: Node): Set[Node] = {
    require(validGraph(g) && g.adjlist.isDefinedAt(start))

    val initVisited = Set(start)
    val initWL = WCons(g.adjlist(start), WNil())
    //iterate until the worklist is empty
    iterate(g, initVisited, initWL)
  }
}
