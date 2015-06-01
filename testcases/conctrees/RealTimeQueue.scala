import leon.instrumentation._
import leon.lang._
import leon.collection._
import leon.annotation._

class RealTimeQueue {

  /**
   * We also need to keep track of a set of lazy nodes that have been evaluated
   * in a global state (which is in leon passed around as additional 
   * parameters and global variables). 
   * TODO: 'memVals' should store a lazy val of type "Any", but not sure if leon 
   * allows it. So for now using Lazy[E].
   * TODO: Moreover, we do want reference equality here, how
   * do we accomplish this ?  
   * Time taken to access a lazy val is a function of the current state
   */
  //memVals: Set[Lazy[E]]
  case class Lazy[E](x: E, tx: (Set[Lazy[E]] => BigInt)) {
    /**
     * The function that access a lazy value and returns a cost w.r.t
     * a history of operations summarized by a cache.
     */
    def access(cache: Set[Lazy[E]]): (E, BigInt, Set[Lazy[E]]) = {
      if (cache.contains(this)) {
        (this.x, 0)
      } else {
        (this.x, this.tx, cache + l)
      }
    }
 
  }
 
  sealed abstract class Stream[T]
  case class SCons[T](x: T, tail: Lazy[Stream[T]]) extends Stream[T]
  case class SNil[T]() extends Stream[T]

  case class Queue[T](f: Lazy[Stream[T]], r: List[T], s: Lazy[Stream[T]])
  //invariant: |s| = |f| - |r|

  /**
   * Here, 'cache' is the set of lazy values that are evaluated and memoized
   *  before rotate is invoked
   */
  def rotate[T](f: Lazy[Stream[T]], r: List[T], 
      a: Lazy[Stream[T]], cache: Set[Lazy[Stream[T]]]): (Lazy[Stream[T]], BigInt, Set[Lazy[T]]) = {
    val (res, t) = {
      val (feval, faccessTime, ncache) = access(f, cache)
      (feval, r) match {
        case (SNil(), Cons(y, _)) =>
          (SCons[T](y, a), faccessTime + 1)
        case (SCons(x, tail), Cons(y, r1)) =>
          val l = Lazy(SCons(y, a), 1, Set[Lazy[Stream[T]]]()) 
          	//note that the lazy closure that will be materialized by evaluating the 
          	//argument of lazy is empty here.          
          val (rot, t1) = rotate(tail, r1, l, cache)
          (SCons[T](x, Lazy(rot.x, rot.tx + t1)), tx + 1)
      }
    }
    (Lazy(res, t), 1)
  }

  def createQueue[T](f: Lazy[Stream[T]], r: List[T], s: Lazy[Stream[T]]): (Queue[T], BigInt) = {
    s match {
      case Lazy(SCons(x, s1), tx) =>
        (Queue(f, r, s1), tx + 1)
      case Lazy(SNil(), tx) =>
        val (rot, t1) = rotate(f, r, Lazy[Stream[T]](SNil[T](), 1))
        (Queue(rot, Nil[T](), rot), t1)
    }
  }

  def enqueue[T](x: T, q: Queue[T]): (Queue[T], BigInt) = {
    createQueue(q.f, Cons[T](x, q.r), q.s)
  }

  def dequeue[T](q: Queue[T]): (Queue[T], BigInt) = {
    q.f match {
      case Lazy(SCons(x, nf), tf) =>
        val (res, tq) = createQueue(nf, q.r, q.s)
        (res, tf + tq)
    }
  }
}