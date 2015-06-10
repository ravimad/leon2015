import leon.instrumentation._
import leon.lang._
import leon.collection._
import leon.annotation._

class RealTimeQueue {

  /*case class Lazy[E](x: E, tx: (Set[Lazy[E]] => BigInt)) {
    *//**
     * The function that access a lazy value and returns a cost w.r.t
     * a history of operations summarized by a cache.
     *//*
    def access(cache: Set[Lazy[E]]): (E, BigInt, Set[Lazy[E]]) = {
      if (cache.contains(this)) {
        (this.x, 0)
      } else {
        (this.x, this.tx, cache + l)
      }
    } 
  }*/
  
  sealed abstract class Stream[T] {
    def isLazy : Boolean = {
      this match {
        case RotateStream(_, _, _) =>  true
        case _ => false
      }
    }
    def isEmpty : Boolean = {
      this match {
        case SNil[T]() => true
        case _ => false
      }
    }
  }
  case class SCons[T](x: T, tail: Stream[T]) extends Stream[T] //this is a concrete constructor
  case class SNil[T]() extends Stream[T] 
  case class RotateStream[T](f: Stream, r: List[T], a: Stream) extends Stream[T] // this is a lazy constructor, i.e, 
		  //the values of the stream are not directly available and should be obtained by further processing.
		  //In some sense, this represents the closure corresponding to rotate.		  	

  case class Queue[T](f: Stream[T], r: List[T], s: Stream[T])
  //invariant: |s| = |f| - |r|, and |s| >= 0
  
  /**
   * A property that requires that the front of every lazy queue has already been evaluated
   */
  def nochainingProperty(s: Stream[T], cache: Set[Stream[T]]) : Boolean = {
    s match {
      case RotateStream(f, _, _) => 
        cache.contains(f) && nochainingProperty(f)
      case SCons(_, t) => 
        nochainingProperty(t)
      case _ => 
        true
    }
  } 
  
  def containsIfLazy(s: Stream[T], cache: Set[Stream[T]]) : Boolean = {
    s match {
      case RotateStream(_, _, _) => 
        cache.contains(s) 
      case => 
        true
    }
  }

  /**
   * Here, 'cache' is the set of streams that have a concrete constructor
   */
  def rotate[T](f: Stream[T], r: List[T], a: Stream[T], cache: Set[Stream[T]]): (SCons[T], BigInt, Set[Stream[T]]) = {
    require(nonchainingProperty(f, cache) && 
    		containsIfLazy(f))//here cache must additionally contain 'f' if it is a RotateStream

    (f, r) match {
      case (SNil(), Cons(y, _)) =>
        (SCons[T](y, a), 1, cache)
      case (SCons(x, tail), Cons(y, r1)) =>
        val rot = RotateStream(tail, r1, SCons[T](y, a)) //this creates a lazy rotate operation
        (SCons[T](x, rot), 1, cache)
      case (rs@RotateStream(_,_,_), Cons(y, r1)) => 
        val (SCons(x, tail), tc, cache1) = concretize(rs, cache)
        val rot = RotateStream(tail, r1, SCons[T](y, a))
        (SCons[T](x, rot), tc + 1, cache1)
    }
  }
  
  def concretize(rs: RotateStream, cache: Set[Stream[T]]): (SCons[T], BigInt, Set[Stream[T]]) = {
    require(nochaningProperty(rs, cache)) 
    
    if(cache.contains(rs)) {
      //here, res was already evaluated, so the cost is a constant
      val (res, _, _) = rotate(rs.f, rs.r, rs.s, cache)
      (res, 1, cache)
    } else {
      //here, the stream has to be evaluated
      val (res, tr, ncache) = rotate(rs.f, rs.r, rs.s, cache)
      (res, tr + 1, ncache + rs) //now rs has been evaluated
    }
  }

  def createQueue[T](f: Stream[T], r: List[T], s: Stream[T], cache: Set[Stream[T]]): (Queue[T], BigInt, Set[Stream[T]]) = {
    require( (s.isLazy || s.isEmpty) && 
        nochainingProperty(s, cache))
    s match {
      case rs : RotateStream => 
      	val (SCons(_, s1), tc, cache1) = concretize(rs, cache) 
      	(Queue(f, r, s1), tc + 1, cache1)      	
      case SNil() =>
        val rot = RotateStream(f, r, SNil[T]()) 
        (Queue(rot, Nil[T](), rot), 1, cache) //here we are not evaluating any closure.
    }
  }

  def enqueue[T](x: T, q: Queue[T], cache: Set[Stream[T]]): (Queue[T], BigInt, Set[Stream[T]]) = {
    require( (q.s.isLazy || q.s.isEmpty) && 
        nochainingProperty(q.s, cache))
        
    val (res, t, ncache) = createQueue(q.f, Cons[T](x, q.r), q.s)
    (res, t + 1, ncache)
  }

  def dequeue[T](q: Queue[T], cache: Set[Stream[T]]): (Queue[T], BigInt, Set[Stream[T]]) = {
    require(!q.f.isEmpty &&
        (q.s.isLazy || q.s.isEmpty) && 
        nochainingProperty(q.s, cache)
        )
    q.f match {
      case SCons(x, nf) => //here the front is concretized
        val (res, tq, ncache) = createQueue(nf, q.r, q.s, cache)
        (res, tq + 1, ncache)
        
      case rs : RotateStream => 
        val (SCons(x, nf), tc, ncache) = concretize(rs, cache) 
        val (res, tq, ncache2) = createQueue(nf, q.r, q.s, ncache)
        (res, tc + tq + 1, ncache2)
    }
  }
}