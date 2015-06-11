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
    

    def sizeInv(cache: Set[RotateStream[T]]): Boolean = {
      this match {
        case rs @ RotateStream(f, r, a) =>
          r.size == f.size + 1 &&
            f.sizeInv(cache) && a.sizeInv(cache)
        case SCons(_, tail) =>
          tail.sizeInv(cache)
        case _ =>
          true
      }
    }

    /**
     * Argument to rotates are evaluated
     */
    def rotateInv(cache: Set[RotateStream[T]]): Boolean = {
      this match {
        case rs @ RotateStream(f, r, a) =>
          f.isEval(cache) && a.isCons &&
            f.rotateInv(cache) && a.rotateInv(cache)
        case SCons(_, tail) =>
          tail.rotateInv(cache)
        case _ =>
          true
      }
    } //ensuring(res => !isEval(cache) || res) //isEval is a stronger property
    
    def isEval(cache: Set[RotateStream[T]]): Boolean = {
      (this match {
        case rs @ RotateStream(f, _, a) =>
          cache.contains(rs) &&  f.isEval(cache)
        case SCons(_, tail) => 
          tail.isEval(cache)
        case _ => 
          true
      }) //&& rotateInv(cache)
    }

    def valid(cache: Set[RotateStream[T]]): Boolean = {
      rotateInv(cache) && sizeInv(cache)
    }
  }
  case class SCons[T](x: T, tail: Stream[T]) extends Stream[T] //this is a concrete constructor
  case class SNil[T]() extends Stream[T]
  case class RotateStream[T](f: Stream[T], r: List[T], a: SCons[T]) extends Stream[T] // this is a lazy constructor, i.e, 
  //the values of the stream are not directly available and should be obtained by further processing.
  //In some sense, this represents the closure corresponding to rotate.		  	

  case class Queue[T](f: Stream[T], r: List[T], s: Stream[T]) {
    def isEmpty = f.isEmpty
  }
  //invariant: |s| = |f| - |r|, and |s| >= 0

  def validMonotonicity[T](s: Stream[T], c1: Set[RotateStream[T]], c2: Set[RotateStream[T]]): Boolean = {
    !c1.subsetOf(c2) || !s.valid(c1) || s.valid(c2) && {
      //induction scheme
      s match {
        case SCons(x, tail) =>
          validMonotonicity(tail, c1, c2)
        case SNil() =>
          true
        case RotateStream(f, r, a) =>
          validMonotonicity(f, c1, c2) && validMonotonicity(a, c1, c2)
      }
    }
  } holds
  /**
   * This is basically required to prove that the queue invariant will be preserved
   */
  /*def firstUnevaluatedSuffixProperty[T](f: Stream[T], sch: Stream[T], cache: Set[RotateStream[T]]): Boolean = {
    require(concretizedProperty(f, cache))
    (f == sch) || {
      f match {
        case SCons(_, tail) =>
          firstUnevaluatedSuffixProperty(tail, sch, cache)
        case rs: RotateStream[T] =>
          firstUnevaluatedSuffixProperty(concretize(rs, cache)._1, sch, cache)
        case SNil() =>
          false
      }
    }
  } ensuring (res => !res || concretizedProperty(sch, cache)) */ //true implies that 'sch' also satisfies 'concretizedProperty'  

  /**
   * Here, 'cache' is the set of streams that have a concrete constructor
   */
  def rotate[T](f: Stream[T], r: List[T], a: SCons[T], cache: Set[RotateStream[T]]): (SCons[T], BigInt, Set[RotateStream[T]]) = {
    require(f.valid(cache) && a.valid(cache) &&
      f.isEval(cache) && // 'f' is concretized   		     
      r.size == f.size + 1) // size invariant between 'f' and 'r' holds 
    (f, r) match {
      case (SNil(), Cons(y, _)) => //in this case 'y' is the only element in 'r'
        (SCons[T](y, a), 1, cache)
        
      case (SCons(x, tail), Cons(y, r1)) =>
        val rot = RotateStream(tail, r1, SCons[T](y, a)) //this creates a lazy rotate operation
        (SCons[T](x, rot), 1, cache)        
        
      case (rs @ RotateStream(_, _, _), Cons(y, r1)) =>
        concretize(rs, cache) match {
          case (SCons(x, tail), tc, cache1) =>
            val rot = RotateStream(tail, r1, SCons[T](y, a))
            (SCons[T](x, rot), tc + 1, cache1)
        }
    }
  } ensuring (res => res._1.valid(res._3) &&
		  			 instMonotonicity2(a, f, cache) && 
		  			 res._1.size == f.size + r.size + a.size)
  // && 
  //res._1.isCons)
  //res._3 == cache) //&& //the old and new caches are the same (this procedure does not evaluate any closure)
  //res._2 <= 2) //time bound

  def concretize[T](rs: RotateStream[T], cache: Set[RotateStream[T]]): (SCons[T], BigInt, Set[RotateStream[T]]) = {
    require(rs.valid(cache)) //here, we require that the 'front' is concretizd  

    if (cache.contains(rs)) {
      //here, rs was already evaluated, so the cost is a constant
      val (res, _, ncache) = rotate(rs.f, rs.r, rs.a, cache)
      (res, 1, ncache)
    } else {
      //here, rotate stream has to be forced
      val (res, tr, ncache) = rotate(rs.f, rs.r, rs.a, cache)
      (res, tr + 1, ncache ++ Set(rs)) //now rs has been evaluated. 
    }
  } ensuring (res => res._1.isEval(res._3) && res._1.valid(res._3) &&
    res._1.size == rs.size &&
    cache.subsetOf(res._3) &&
    //(!cache.contains(rs) || res._3 == cache) && //a property that old and new caches are the same if 'rs' is already evaluated    
    //res._2 <= 3 && //time bound
    res._1.isCons && //some auxiliary invariants to keep leon happy
    instMonotonicity(rs, cache) //axiom instantiations
    )

  def instMonotonicity[T](rs: RotateStream[T], cache: Set[RotateStream[T]]): Boolean = {
    require(rs.valid(cache))
    val (res, _, ncache) = rotate(rs.f, rs.r, rs.a, cache)
    validMonotonicity(res, ncache, ncache ++ Set(rs))
  }

  def instMonotonicity2[T](a: SCons[T], f: Stream[T], cache: Set[RotateStream[T]]): Boolean = {
    require(f.valid(cache))
    f match {
      case rs: RotateStream[T] =>
        val (res, _, cache1) = concretize(rs, cache)
        validMonotonicity(a, cache, cache1)
      case _ =>
        true
    }
  }

  /*def createQueue[T](f: Stream[T], r: List[T], s: Stream[T], cache: Set[RotateStream[T]]): (Queue[T], BigInt, Set[RotateStream[T]]) = {
    require(concretizedProperty(f, cache) //&&
      //firstUnevaluatedSuffixProperty(f, s, cache) //states that schedule is the first unevaluated suffix of 'f'
      )
    s match {
      case rs: RotateStream[T] =>
        val (SCons(_, s1), tc, cache1) = concretize(rs, cache) //here, just forcing the first element of schedule
        (Queue(f, r, s1), tc + 1, cache1)
      case SCons(_, s1) =>
        //here, the first element of 's' is already concretized, so nothing is to be done
        (Queue(f, r, s1), 1, cache)
      case SNil() =>
        //directly calling rotate method (the original implementation creates a RotateStream and concretizes it)        
        val (rot, tr, _) = rotate(f, r, SNil[T](), cache)
        (Queue(rot, Nil[T](), rot), tr + 1, cache)
    }
  } ensuring (res => concretizedProperty(res._1.f, res._3) && 
		  			res._2 <= 4) //&&
		  			 //firstUnevaluatedSuffixProperty(res._1.f, res._1.s, res._3))

  */

  /*def queueInvariant[T](q: Queue[T], cache: Set[RotateStream[T]]) = {
    concretizedProperty(q.f, cache) //&& //the front of the queue is in the cache, and it satisfies 'concretizedProperty'
      //firstUnevaluatedSuffixProperty(f, s, cache) //the schedule is the first unevaluated part of the queue
  }
  
  def enqueue[T](x: T, q: Queue[T], cache: Set[RotateStream[T]]): (Queue[T], BigInt, Set[RotateStream[T]]) = {
    require(queueInvariant(q, cache))

    val (res, t, ncache) = createQueue(q.f, Cons[T](x, q.r), q.s, cache)
    (res, t + 1, ncache)
  }

  def dequeue[T](q: Queue[T], cache: Set[RotateStream[T]]): (Queue[T], BigInt, Set[RotateStream[T]]) = {
    require(!q.isEmpty && queueInvariant(q, cache))
    q.f match {
      case SCons(x, nf) => //here the front is concretized
        val (res, tq, ncache) = createQueue(nf, q.r, q.s, cache)
        (res, tq + 1, ncache)

      case rs: RotateStream[T] =>
        val (SCons(x, nf), tc, ncache) = concretize(rs, cache)
        val (res, tq, ncache2) = createQueue(nf, q.r, q.s, ncache)
        (res, tc + tq + 1, ncache2)
    }
  }*/
}