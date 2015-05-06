import leon.lang._
import leon.annotation._
import leon._
import leon.collection._

object BinaryTree {
  sealed abstract class Tree
  case class Node(left: Tree, value: BigInt, right: Tree) extends Tree
  case class Leaf() extends Tree

  //  case class SortedTriple(min: Option[Int], max: Option[Int], sorted: Boolean)
  //
  //  def isSortedTriple(tree: Tree): SortedTriple = (tree match {
  //    case Leaf() => SortedTriple(None(), None(), true)
  //    case Node(l, v, r) =>
  //      (isSortedTriple(l), isSortedTriple(r)) match {
  //        case (SortedTriple(minl, maxl, sortedl), SortedTriple(minr, maxr, sortedr)) =>
  //          val sorted = sortedl && sortedr && (v > maxl.getOrElse(v - 1)) && (v < minr.getOrElse(v + 1))
  //          SortedTriple(minl.orElse(Some(v)), maxr.orElse(Some(v)), sorted)
  //      }
  //  }) ensuring { res =>
  //    res match {
  //      case SortedTriple(Some(min), Some(max), res) => !res || (min <= max)
  //      case SortedTriple(None(), None(), res) => res
  //      case _ => false
  //    }
  //  }
  //  def isSorted(tree: Tree): Boolean = isSortedTriple(tree).sorted

  //  def max(t: Tree) = {
  //    require(t != Leaf())
  //    t match {
  //      case Node(_, v, Leaf()) => v
  //      case Node(_, v, r) => max(r)
  //    }
  //  }
  //  
  //  def min(t: Tree) = {
  //    require(t != Leaf())
  //    t match {
  //      case Node(Leaf(), v, _) => v
  //      case Node(l, v, _) => min(l)
  //    }
  //  }

  def toList(t: Tree): List[BigInt] = {
    t match {
      case Node(l, v, r) =>
        (toList(l) ++ sing(v)) ++ toList(r)
      case _ =>
        Nil[BigInt]()
    }
  } ensuring (res => t == Leaf() || res != Nil[BigInt]())

  def BST(t: Tree): Boolean = t match {
    case Leaf() => true
    case Node(l, v, r) =>
      BST(l) && BST(r) && isSorted(toList(t)) &&
        (toList(l) == Nil[BigInt]() || toList(l).last < v) &&
        (toList(r) == Nil[BigInt]() || v < first(toList(r)))
  }

  def sing(x: BigInt): List[BigInt] = {
    Cons[BigInt](x, Nil[BigInt]())
  }

  def min(x: BigInt, y: BigInt): BigInt = {
    if (x <= y) x else y
  }

  def max(x: BigInt, y: BigInt): BigInt = {
    if (x >= y) x else y
  }

  def insert(tree: Tree, value: BigInt): Tree = ({
    require(BST(tree))
    tree match {
      case Leaf() => Node(Leaf(), value, Leaf())
      case Node(l, v, r) => if (v < value) {
        Node(l, v, insert(r, value))
      } else if (v > value) {
        Node(insert(l, value), v, r)
      } else {
        Node(l, v, r)
      }
    }
  }) ensuring (res => BST(res) &&
    res != Leaf() &&
    toList(res) != Nil[BigInt]() &&
    (tree match {
      case Leaf() => (first(toList(res)) == value) &&
        (toList(res).last == value)
      case _ =>
        first(toList(res)) == min(first(toList(tree)), value) &&
          toList(res).last == max(toList(tree).last, value)
    })
    &&
    instAppendSorted(tree, value))

  def instAppendSorted(t: Tree, value: BigInt): Boolean = {
    require(BST(t))
    t match {
      case Leaf() =>
        true
      case Node(l, v, r) =>
        appendSorted(toList(l), sing(v)) &&
          appendSorted(toList(l) ++ sing(v), toList(r)) &&
          (if (v < value) {
            appendSorted(toList(l), sing(v)) &&
              appendSorted(toList(l) ++ sing(v), toList(insert(r, value)))
          } else if (v > value) {
            appendSorted(toList(insert(l, value)), sing(v)) &&
              appendSorted(toList(insert(l, value)) ++ sing(v), toList(r))
          } else true)
    }
  }

  // this computes strict sortedness
  def isSorted(l: List[BigInt]): Boolean = {
    l match {
      case Nil() => true
      case Cons(x, Nil()) => true
      case Cons(x, tail @ Cons(y, _)) =>
        (x < y) && isSorted(tail)
    }
  } ensuring (res => !res || l == Nil[BigInt]() || first(l) <= l.last)

  def first(l: List[BigInt]): BigInt = {
    require(l != Nil[BigInt])
    l match {
      case Cons(x, _) => x
    }
  }

  // A lemma about `append` and `isSorted`
  def appendSorted(l1: List[BigInt], l2: List[BigInt]): Boolean = {
    require(isSorted(l1) && isSorted(l2) &&
      (l1 == Nil[BigInt]() || l2 == Nil[BigInt]() || l1.last < first(l2)))
    // induction scheme
    (l1 match {
      case Nil() => true
      case Cons(x, xs) => appendSorted(xs, l2)
    }) &&
      (l1 == Nil[BigInt]() || first(l1 ++ l2) == first(l1)) &&
      (l2 == Nil[BigInt]() || (l1 ++ l2).last == l2.last) &&
      (l2 != Nil[BigInt]() || l1 == Nil[BigInt]() || (l1 ++ l2).last == l1.last) &&
      isSorted(l1 ++ l2)
  }.holds

  //  def buggyMerge(t1: Tree, t2: Tree): Tree = ({
  //    require(isSorted(t1) && isSorted(t2))
  //    (t1, t2) match {
  //      case (Leaf(), _) => t2
  //      case (_, Leaf()) => t1
  //      case (t1 @ Node(l1, v1, r1), t2 @ Node(l2, v2, r2)) =>
  //        if (v1 < v2) {
  //          Node(buggyMerge(t1, l2), v2, r2)
  //        } else if (v2 < v1) {
  //          Node(buggyMerge(l1, t2), v1, r1)
  //        } else {
  //          Node(buggyMerge(l1, l2), v1, buggyMerge(r1, r2))
  //        }
  //    }
  //  }) ensuring (res => isSorted(res))
}
