import leon.instrumentation._
import leon.lang._
import leon.collection._
import leon.annotation._

object RealTimeQueue {

  sealed abstract class Stream[T] {

    def isEmpty: Boolean = {
      this match {
        case SNil() => true
        case _ => false
      }
    }

    def isCons: Boolean = {
      this match {
        case SCons(_, _) => true
        case _ => false
      }
    }

    def size: BigInt = {
      this match {
        case SNil() => 0
        case SCons(x, t) => 1 + t.size
        case RotateStream(f, r, a) =>
          f.size + r.size + a.size
      }
    } ensuring (_ >= 0)

    def sizeInv: Boolean = {
      this match {
        case rs @ RotateStream(f, r, a) =>
          r.size == f.size + 1 &&
            f.sizeInv && a.sizeInv
        case SCons(_, tail) =>
          tail.sizeInv
        case _ =>
          true
      }
    }

    /**
     * Argument to rotates are evaluated
     */
    def rotateInv: Boolean = {
      this match {
        case rs @ RotateStream(f, r, a) =>
          //f.isEval(cache) && a.isCons &&
          f.isConcrete && a.isConcrete && //arguments to rotate are concrete.
            f.rotateInv && a.rotateInv
        case SCons(_, tail) =>
          tail.rotateInv
        case _ =>
          true
      }
    }

    //this is a stronger property than valid
    def isConcrete: Boolean = {
      this match {
        case SNil() =>
          true
        case SCons(_, tail) =>
          tail.isConcrete
        case _ =>
          false
      }
    } ensuring (res => !res || this.valid)

    def valid: Boolean = {
      rotateInv && sizeInv
    }
  }
  case class SCons[T](x: T, tail: Stream[T]) extends Stream[T] //this is a concrete constructor
  case class SNil[T]() extends Stream[T]
  case class RotateStream[T](f: Stream[T], r: List[T], a: Stream[T]) extends Stream[T] // this is a lazy constructor, i.e, 
  //the values of the stream are not directly available and should be obtained by further processing.
  //In some sense, this represents the closure corresponding to rotate.		  	

  case class Queue[T](f: Stream[T], r: List[T], s: Stream[T]) {
    def isEmpty = f.isEmpty
  }
  //invariant: |s| = |f| - |r|, and |s| >= 0

  /**
   * Here, 'cache' is the set of streams that have a concrete constructor
   */
  def rotate[T](f: Stream[T], r: List[T], a: Stream[T]): (SCons[T], BigInt) = {
    require(f.isConcrete && a.isConcrete && // 'f' and 'a' are concretized              
      r.size == f.size + 1) // size invariant between 'f' and 'r' holds 
    (f, r) match {
      case (SNil(), Cons(y, _)) => //in this case 'y' is the only element in 'r'
        (SCons[T](y, a), 1)

      case (SCons(x, tail), Cons(y, r1)) =>
        val rot = RotateStream(tail, r1, SCons[T](y, a)) //this creates a lazy rotate operation
        (SCons[T](x, rot), 1)
    }
  } ensuring (res => res._1.valid &&
    res._1.size == f.size + r.size + a.size &&
    res._2 <= 1 && //time bound
    res._1.isCons) //auxiliary invariants

  /**
   * Materialize will update 'f' and construct a new result.
   * Ideally, the second argument should include every structure that may contain
   * the target of 'rs'.
   */
  def materialize[T](mats: RotateStream[T], s: Stream[T]): (SCons[T], Stream[T], BigInt) = {
    require(mats.valid && s.valid &&
      suffix(s, mats) &&
      firstLazyClosure(s) == mats)

    val (matres, matt) = rotate(mats.f, mats.r, mats.a)
    (matres, updateReferences(s, mats), matt + 1)

  } ensuring (res => res._1.valid && res._2.valid &&
    res._3 <= 2 && //time taken is bounded by executing rotate    
    firstLazyClosure(res._2) == firstLazyClosure(res._1) && //first lazy closure property is preserved
    suffix(res._2, res._1) && //proper suffix is preserved
    (res._2.isCons || res._2.isEmpty) &&
    res._1.size == mats.size && res._2.size == s.size && //sizes are preserved
    //(!s.isCons || res._2.isCons) && // if the first element of 's' is cons, so is res._2 
    res._1.isCons //auxiliary invariants
    )

  /**
   * This does not take any time, by the definition of laziness
   */
  def updateReferences[T](s: Stream[T], mats: RotateStream[T]): Stream[T] = {
    require(s.valid && mats.valid &&
      suffix(s, mats) &&
      firstLazyClosure(s) == mats)
    s match {
      //go into every case of 'f' and update the structure
      case RotateStream(f, r, a) =>
        if (s == mats) { //ADT property implies that we need not search in the sub-structures 'f' and 'a' as well.
          rotate(f, r, a)._1 //here, we can ignore the time, this only captures the semantics
        } else {
          //this is an unreachable case because of the preconditions
          // search in 'f' and 'a' and update the occurences of 'rs'          
          RotateStream(updateReferences(f, mats), r, updateReferences(a, mats))
        }
      case SCons(x, t) => //here s and rs cannot be equal, so look in the substructures        
        SCons(x, updateReferences(t, mats))
      case SNil() => //here rs is not found, so the structure  remains the same
        s
    }
  } ensuring (res => res.valid &&
    res.size == s.size &&
    (!s.isConcrete || res.isConcrete) && //concreteness is preserved.       
    firstLazyClosure(res) == firstLazyClosure(rotate(mats.f, mats.r, mats.a)._1) && //first lazy closure property is preserved
    suffix(res, rotate(mats.f, mats.r, mats.a)._1) && //proper suffix is preserved
    (res.isCons || res.isEmpty) //result is cons, when the firstLazy property holds      
    )
    
  def firstLazyClosure[T](f: Stream[T]): Stream[T] = {
    require(f.valid)
    f match {
      case SCons(_, tail) =>
        firstLazyClosure(tail)
      case _ =>
        f
    }
  } ensuring (res => !res.isCons &&
    (!res.isEmpty || f.isConcrete)) //if there are no lazy closures then the stream is concrete

  def suffix[T](f: Stream[T], sch: Stream[T]): Boolean = {
    (f == sch) || {
      f match {
        case SCons(_, t) =>
          suffix(t, sch)
        case _ =>
          false
      }
    }
  } ensuring(res => sch match {
    case SCons(_, t) => 
      !res || suffix(f, t)
    case _ => true
  })

  def queueInvariant[T](q: Queue[T]) = {
    q.f.valid && q.s.valid &&
      (firstLazyClosure(q.f) == firstLazyClosure(q.s)) &&     
      (suffix(q.f, q.s)) &&
      q.s.size == q.f.size - q.r.size
  }

  def createQueue[T](f: Stream[T], r: List[T], sch: Stream[T]): (Queue[T], BigInt) = {
    require(f.valid && sch.valid &&
      firstLazyClosure(f) == firstLazyClosure(sch) && //note: we only need the first lazy closures to be equal
      suffix(f, sch) &&     
      sch.size == f.size - r.size + 1) //size invariant holds 
    sch match {
      case rs: RotateStream[T] =>
        val (SCons(_, s1), fnew, tc) = materialize(rs, f)
        (Queue(fnew, r, s1), tc + 1)
      case SCons(_, s1) =>
        //here, the first element of 's' is already concretized, so nothing is to be done
        (Queue(f, r, s1), 1)
      case SNil() =>
        //directly calling rotate method (the original implementation creates a RotateStream and materializes it)        
        val (rotres, tr) = rotate(f, r, SNil[T]())
        (Queue(rotres, Nil[T](), rotres), tr + 1)
    }
  } ensuring (res => queueInvariant(res._1) &&
    res._2 <= 3) //time bounds 

  def enqueue[T](x: T, q: Queue[T]): (Queue[T], BigInt) = {
    require(queueInvariant(q))

    val (res, t) = createQueue(q.f, Cons[T](x, q.r), q.s)
    (res, t + 1)
  } ensuring (res => queueInvariant(res._1) && res._2 <= 4)

  def dequeue[T](q: Queue[T]): (Queue[T], BigInt) = {
    require(!q.isEmpty && queueInvariant(q))
    q.f match {
      case SCons(x, nf) =>
        q.s match {
          case SCons(_, st) => //here, the precondition of createQueue (reg. suffix property) may get violated,             
            // so it is handled specially here.
          	(Queue(nf, q.r, st), 1)            
          case _ => 
          	val (res, tq) = createQueue(nf, q.r, q.s)
          	(res, tq + 1)
        }
      case RotateStream(_, _, _) => //here, 'q.f' is not yet materialized, materialize it and return the new queue
        //here, q.s and f are equal
        val rs@RotateStream(_, _, _) = q.s
        val (SCons(_, s1), SCons(_, nf), tc) = materialize(rs, q.f) 
        (Queue(nf, q.r, s1), tc + 1)        
    }
  } ensuring(res => queueInvariant(res._1) && res._2 <= 4)
}