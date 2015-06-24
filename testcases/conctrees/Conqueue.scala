import leon.instrumentation._
import leon.collection._
import leon.lang._
import ListSpecs._
import leon.annotation._

object Conqueue {
  import conctrees.ConcTrees._

  def max(x: BigInt, y: BigInt): BigInt = if (x >= y) x else y
  def abs(x: BigInt): BigInt = if (x < 0) -x else x

  sealed abstract class ConQ[T] {

    /*def isTip: Boolean = {
      this match {
        case Tip(_) => true
        case _ => false
      }
    }*/

    val isLazy: Boolean = this match {
      case _: PushLazy => true
      case _ => false
    }
    
    val isSpine : Boolean = this match {
      case _ : Spine => true
      case   _ => false
    }
    
    val pushLazyInv : Boolean = this match {
      case PushLazy(ys, xs) =>
        xs match {
          case Spine(h, _) =>
          	h.level == ys.level
          case _ => false
        }        
      case Spine(_, rear) => rear.pushLazyInv
      case _ => true
    }
    
    val zeroPreceedsLazy : Boolean = this match {
      case Spine(h, PushLazy(_, q)) => 
        (h == Empty()) && q.zeroPreceedsLazy // the position before pushlazy is Empty
      case Spine(_, rear) =>
        rear.zeroPreceedsLazy
      case Tip(_) => true
      case _ => false // this implies that a ConQ cannot start with a lazy closure
    }

    val valid = {
      zeroPreceedsLazy && pushLazyInv
    }
    
    val weakZeroPreceedsLazy : Boolean = this match {
      case Spine(h, PushLazy(_, q)) => 
        q.zeroPreceedsLazy 
      case Spine(_, rear) =>
        rear.weakZeroPreceedsLazy
      case Tip(_) => true
      case _ => false // this implies that a ConQ cannot start with a lazy closure
    }
    
    val weakValid = {
      weakZeroPreceedsLazy && pushLazyInv
    }
    
    def firstLazyClosure: ConQ[T] = {
      this match {
        case Spine(_, tail) =>
          tail.firstLazyClosure
        case _ =>
          this
      }
    } ensuring (res => !res.isSpine) 

    def suffix(sch: ConQ[T]): Boolean = { //checks if sch is a suffix of 'this'
      (this == sch) || {
        this match {
          case Spine(_, rear) =>
            rear.suffix(sch)
          case _ =>
            false
        }
      }
    } ensuring (res => sch match {
      case Spine(_, rear) =>
        !res || suffix(rear)
      case _ => true
    })
  }
  
  case class Tip[T](t: Conc[T]) extends ConQ[T]
  case class Spine[T](head: Conc[T], rear: ConQ[T]) extends ConQ[T]
  // a closure corresponding to 'push' operations
  case class PushLazy[T](ys: Single[T], xs: Spine[T]) extends ConQ[T]
  
  def queueScheduleProperty[T](xs: ConQ[T], sch: ConQ[T]) = {
    xs.valid && sch.valid &&
      xs.firstLazyClosure == sch.firstLazyClosure && //sch is the first lazy closure of 's'
      xs.suffix(sch) //sch is a suffix of s
  }
  
  def weakScheduleProperty[T](xs: ConQ[T], sch: ConQ[T]) = {
    xs.weakValid && sch.valid &&
      xs.firstLazyClosure == sch.firstLazyClosure && //sch is the first lazy closure of 's'
      xs.suffix(sch) //sch is a suffix of s
  }
  
  case class Wrapper[T](queue: ConQ[T], schedule: ConQ[T]) {
    val valid : Boolean = {
      queueScheduleProperty(queue, schedule) 
    }
  }

  def pushLeft[T](ys: Single[T], xs: ConQ[T]): (ConQ[T], BigInt) = {
    require(xs.valid)
    xs match {
      case Tip(CC(_, _)) =>
        (Spine(ys, xs), 1)
      case Tip(Empty()) =>
        (Tip(ys), 1)
      case Tip(t @ Single(_)) =>
        (Tip(CC(ys, t)), 1)
      case s @ Spine(_, _) =>
        val (r, t) = pushLeftLazy(ys, s) //ensure precondition here
        (r, t + 1)
    }
  } ensuring(res => !res._1.isLazy && res._2 <= 2) 

  def pushLeftLazy[T](ys: Conc[T], xs: Spine[T]): (Spine[T], BigInt) = {
    require(!ys.isEmpty && xs.valid && 
      (xs.head.isEmpty || xs.head.level == ys.level))

    xs match {
      case Spine(Empty(), rear) => //note: 'rear' is not materialized here         
        (Spine(ys, rear), 1) // if rear was 'PushLazy', this would temporarily break the 'zeroPreceedsLazy' invariant
      case Spine(head, rear) =>        
        val carry = CC(head, ys) //here, head and ys are of the same level
        rear match { //here, rear cannot be 'PushLazy' by the 'zeroPreceedsLazy' invariant
          case s @ Spine(_, _) =>
            (Spine(Empty(), PushLazy(carry, s)), 1)
            
          case t @ Tip(tree) if tree.level > carry.level => // can this happen ? this means tree is of level at least two greater than rear ?
            (Spine(Empty(), Spine(carry, t)), 1)
            
          case Tip(tree) =>
            // here tree level and carry level are equal
            (Spine(Empty(), Spine(Empty(), Tip(CC(tree, carry)))), 1)
        }
    }
  } ensuring(res => res._1.isSpine && 
      (res._1.valid || (res._1.rear == xs.rear)) && 
      res._2 <= 1) // this invariant implies that the result if invalid is of the form Spine(t, PushLazy(...)) 
  
  /**
   * Materialize will evaluate ps and update the references to 
   * ps in xs. Ideally, the second argument should include every 
   * structure that may contain 'pl'.
   */
  /*def materialize[T](mat: Spine[T], xs: ConQ[T]): (Spine[T], ConQ[T], BigInt) = {
    require(weakScheduleProperty(xs, mat) && 
        mat.rear.isLazy)
    mat match {
      case Spine(h, PushLeft(elem, q)) =>
        val (nr, t) = pushLeftLazy(elem, q)
        (Spine(h, nr), updateReferences(xs, mat), t + 1)
    }
  } ensuring(res => queueScheduleProperty(res._2, res._1) && // a stronger property will be satisfied after materialization 
		  			res._3 <= 2) 
  
  *//**
   * This does not take any time, by the definition of laziness
   *//*
  def updateReferences[T](xs: ConQ[T], mat: Spine[T]): ConQ[T] = {
	  require(weakScheduleProperty(xs, mat))   
    xs match {      
      case Spine(h, PushLazy(elem, q)) if (xs == mat) =>
        //ADT property implies that we need not search in the sub-structure 'q'.
        Spine(h, pushLeftLazy(elem, q)._1) //here, we can ignore the time, this only captures the semantics        
      case Spine(h, rear) => //here mat and xs cannot be equal, so look in the substructures        
        Spine(h, updateReferences(rear, mat))      
    }
  } ensuring (res => queueScheduleProperty(res, Spine(mat.h, pushLeftLazy(mat.ys, mat.xs)))) // a stronger property will be satisfied here  

  def pushLeftAndPay[T](ys: Single[T], w: Wrapper[T]): (Wrapper[T], BigInt) = {
    require(w.valid)
    
    val (nq, t1) = pushLeft(ys, w.queue) // the queue invariant could be temporarily broken
    // update the schedule
    val nsched = nq match {
      case Spine(_, _ : PushLazy) => nq
      case _ => w.schedule
    } //here, we need to ensure that new schedule is a suffix of the new queue    
    val (fsched, fq, t2) = pay(nsched, nq)
    (Wrapper(fq, fsched), t1 + t2 + 1)
    
  } ensuring(res => res._1.valid && res._2 <= 6)
  
  def pay[T](sched: ConQ[T], xs: ConQ[T]) : (ConQ[T], ConQ[T], BigInt) = {
    requrie(weakScheduleProperty(xs, sched))
    sched match {      
      case Spine(_, pl @ PushLazy(elem, q)) =>
        val (Spine(_, matr), nxs, matt) = materialize(pl, xs)
        (matr, nxs, matt + 1)
      case Spine(_, rear) =>
        (rear, xs, 1)
      case Tip(_) => 
        (sched, xs, 1)
    }
  } ensuring(res => queueScheduleProperty(res._2, res._1) && res._3 <= 3)*/
}
