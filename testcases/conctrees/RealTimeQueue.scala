import leon.instrumentation._
import leon.lang._
import leon.collection._
import leon.annotation._

class RealTimeQueue {
  
  case class Lazy[T](x: T, tx: BigInt) 
  
  sealed abstract class Stream[T]
  case class SCons[T](x:T, tail: Lazy[Stream[T]]) extends Stream[T]
  case class SNil[T]() extends Stream[T]
  
  case class Queue[T](f: Lazy[Stream[T]], r: List[T], s: Lazy[Stream[T]])
  //invariant: |s| = |f| - |r|
  
  def rotate[T](f: Lazy[Stream[T]], r: List[T], a: Lazy[Stream[T]]) : (Lazy[Stream[T]], BigInt)  = {
    val (res, t) = {
      (f, r) match {
        case (Lazy(SNil(), tx), Cons(y, _)) => 
          (SCons[T](y, a), tx + 1)
        case (Lazy(SCons(x, tail), tx), Cons(y, r1)) => 
          val (rot, t1) = rotate(tail, r1, Lazy(SCons(y, a), 1)) 
          (SCons[T](x, Lazy(rot.x, rot.tx + t1)), tx + 1)
      }
    }
    (Lazy(res, t), 1)    
  }
  
  def createQueue[T](f: Lazy[Stream[T]], r: List[T], s: Lazy[Stream[T]]) : (Queue[T], BigInt)  = {
    s match {
      case Lazy(SCons(x, s1), tx) => 
        (Queue(f, r, s1), tx + 1)
      case Lazy(SNil(), tx) =>
        val (rot, t1) = rotate(f, r, Lazy[Stream[T]](SNil[T](), 1))     
        (Queue(rot, Nil[T]() , rot), t1)        
    }
  }
  
  def enqueue[T](x: T, q: Queue[T]) : (Queue[T], BigInt) = {
    createQueue(q.f, Cons[T](x, q.r), q.s )
  }
  
  def dequeue[T](q: Queue[T]) : (Queue[T], BigInt) = {
    q.f match {
      case Lazy(SCons(x, nf), tf) => 
        val (res, tq) = createQueue(nf, q.r, q.s)
      	(res, tf + tq)        
    } 
  }
}