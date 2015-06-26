import leon.instrumentation._
import leon.collection._
import leon.lang._
import ListSpecs._
import leon.annotation._
import conctrees.ConcTrees._

object Conqueue {

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
      case PushLazy(_, _) => true
      case _ => false
    }

    val isSpine: Boolean = this match {
      case Spine(_, _) => true
      case _ => false
    }

    val pushLazyInv: Boolean = this match {
      case PushLazy(ys, xs) =>
        !ys.isEmpty && (xs match {
          case Spine(h, rear) =>
            !h.isEmpty && rear.pushLazyInv //note: head cannot be empty for a lazy closure
          //h.level == ys.level (omitting this for now)
          case _ => false
        })
      case Spine(_, rear) => rear.pushLazyInv
      case _ => true
    }

    val zeroPreceedsLazy: Boolean = {
      this match {
        case Spine(h, PushLazy(_, q)) =>
          (h == Empty[T]()) && q.zeroPreceedsLazy // the position before pushlazy is Empty
        case Spine(Empty(), rear) =>
          rear.weakZeroPreceedsLazy // here we have seen a zero
        case Spine(h, rear) =>
          rear.zeroPreceedsLazy //here we have not seen a zero 
        case Tip(_) => true
        case _ => false // this implies that a ConQ cannot start with a lazy closure
      }
    } ensuring (res => !res || weakZeroPreceedsLazy) //zeroPreceedsLazy is a stronger property

    val weakZeroPreceedsLazy: Boolean = {
      this match {
        case Spine(h, PushLazy(_, q)) =>
          q.zeroPreceedsLazy
        case Spine(_, rear) =>
          rear.weakZeroPreceedsLazy
        case Tip(_) => true
        case _ => false // this implies that a ConQ cannot start with a lazy closure
      }
    } //ensuring (res => !zeroPreceedsLazy || res) //zeroPreceedsLazy is a stronger property

    /*val spineInv = this match {
      case 
    }*/

    val valid = {
      zeroPreceedsLazy && pushLazyInv
    }

    val weakValid = {
      weakZeroPreceedsLazy && pushLazyInv
    }

    def firstLazyClosure: ConQ[T] = {
      require(this.pushLazyInv)
      this match {
        case Spine(_, pl: PushLazy[T]) => pl
        case Spine(_, tail) =>
          tail.firstLazyClosure
        case _ =>
          this
      }
    } ensuring (res => !res.isSpine && res.pushLazyInv)

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
  case class PushLazy[T](ys: Conc[T], xs: Spine[T]) extends ConQ[T]

  /*def queueScheduleProperty[T](xs: ConQ[T], sch: ConQ[T]) = {
    xs.valid && sch.weakValid &&
      xs.firstLazyClosure == sch.firstLazyClosure && //sch is the first lazy closure of 's'
      xs.suffix(sch) //sch is a suffix of s
  }*/

  def queueScheduleProperty[T](xs: ConQ[T], sch: PushLazy[T]) = {
    sch match {
      case PushLazy(_, _) =>
        xs.valid && xs.firstLazyClosure == sch //sch is the first lazy closure of 's'      
      case _ => false
    }
  }

  /*def weakScheduleProperty[T](xs: ConQ[T], sch: ConQ[T]) = {
    xs.weakValid && sch.weakValid &&
      xs.firstLazyClosure == sch.firstLazyClosure && //sch is the first lazy closure of 's'
      xs.suffix(sch) //sch is a suffix of s
  }*/

  def weakScheduleProperty[T](xs: ConQ[T], sch: PushLazy[T]) = {
    sch match {
      case PushLazy(_, _) =>
        xs.weakValid && xs.firstLazyClosure == sch //sch is the first lazy closure of 's'
      case _ => false
    }
  }

  def schedulesProperty[T](q: ConQ[T], schs: List[ConQ[T]]): Boolean = {
    schs match {
      case Cons(pl @ PushLazy(_, nestq), tail) =>
        queueScheduleProperty(q, pl) &&
          schedulesProperty(nestq, tail)
      case Nil() =>
        q.valid // here, for now we do not enforce that q should not have any closures.
      case _ =>
        false // other cases are not valid
    }
  }

  def weakSchedulesProperty[T](q: ConQ[T], schs: List[ConQ[T]]): Boolean = {
    schs match {
      case Cons(pl @ PushLazy(_, nestq), tail) =>
        weakScheduleProperty(q, pl) &&
          schedulesProperty(nestq, tail)
      case Nil() =>
        q.valid
      case _ =>
        false
    }
  }

  case class Wrapper[T](queue: ConQ[T], schedule: List[ConQ[T]]) {
    val valid: Boolean = {
      schedulesProperty(queue, schedule)
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
  } ensuring (res => !res._1.isLazy && res._2 <= 2)

  def pushLeftLazy[T](ys: Conc[T], xs: Spine[T]): (Spine[T], BigInt) = {
    require(!ys.isEmpty && xs.valid) // &&
    //(xs.head.isEmpty || xs.head.level == ys.level)) 

    xs match {
      case Spine(Empty(), rear) => //note: 'rear' is not materialized here         
        (Spine(ys, rear), 1) // if rear was 'PushLazy', this would temporarily break the 'zeroPreceedsLazy' invariant
      case Spine(head, rear) =>
        val carry = CC(head, ys) //here, head and ys are of the same level
        rear match { //here, rear cannot be 'PushLazy' by the 'zeroPreceedsLazy' invariant
          case s @ Spine(Empty(), srear) =>
            (Spine(Empty(), Spine(carry, srear)), 1)

          case s @ Spine(_, _) =>
            (Spine(Empty(), PushLazy(carry, s)), 1)

          case t @ Tip(tree) if tree.level > carry.level => // can this happen ? this means tree is of level at least two greater than rear ?
            (Spine(Empty(), Spine(carry, t)), 1)

          case Tip(tree) =>
            // here tree level and carry level are equal
            (Spine(Empty(), Spine(Empty(), Tip(CC(tree, carry)))), 1)
        }
    }
  } ensuring (res => res._1.isSpine &&
    (res._1.valid || (res._1.rear == xs.rear)) &&
    (res._1.valid || res._1.weakValid) &&
    res._2 <= 1) // this invariant implies that the result if invalid is of the form Spine(t, PushLazy(...)) 

  /**
   * Materialize will evaluate ps and update the references to
   * ps in xs. Ideally, the second argument should include every
   * structure that may contain 'pl'.
   */
  def materialize[T](mat: ConQ[T], xs: ConQ[T], schs: Cons[ConQ[T]]): (Spine[T], ConQ[T], BigInt) = {
    require(weakSchedulesProperty(xs, schs) && schs.head == mat)
    mat match {
      case PushLazy(elem, q) =>
        val (nr, t) = pushLeftLazy(elem, q)
        (nr, updateReferences(xs, mat, schs), t + 1)
    }
  } ensuring (res => (res._1 match {
    case Spine(_, pl @ PushLazy(_, _)) =>
      schedulesProperty(res._2, Cons(pl, schs.tail))
    case _ =>
      schedulesProperty(res._2, schs.tail)
  }) &&
    res._3 <= 2)

  /**
   * This does not take any time, by the definition of laziness
   */
  def updateReferences[T](xs: ConQ[T], mat: ConQ[T], schs: Cons[ConQ[T]]): ConQ[T] = {
    require(weakSchedulesProperty(xs, schs) && schs.head == mat)
    xs match {
      case Spine(h, pl @ PushLazy(elem, q)) if (pl == mat) =>
        //ADT property implies that we need not search in the sub-structure 'q'.
        Spine(h, pushLeftLazy(elem, q)._1) //here, we can ignore the time, this only captures the semantics      
      case Spine(h, rear) => //here mat and xs cannot be equal, so look in the substructures        
        Spine(h, updateReferences(rear, mat, schs))
    }
  } ensuring (res => mat match {
    case PushLazy(elem, q) =>
      pushLeftLazy(elem, q)._1 match {
        case Spine(_, pl @ PushLazy(_, _)) =>
          schedulesProperty(res, Cons(pl, schs.tail))
        case _ =>
          schedulesProperty(res, schs.tail)
      }
    //queueScheduleProperty(res, Spine(h, pushLeftLazy(elem, q)._1)) // a stronger property will be satisfied here    
  })

  /*def pushLeftAndPay[T](ys: Single[T], w: Wrapper[T]): (Wrapper[T], BigInt) = {
    require(w.valid)

    val (nq, t1) = pushLeft(ys, w.queue) // the queue invariant could be temporarily broken
    // update the schedule
    val nsched = nq match {
      case Spine(_, PushLazy(_, _)) => Cons[ConQ[T]](nq, w.schedule)
      case _ =>
        assert(schedulesProperty(w.queue, w.schedule))
        w.schedule
    } //here, we need to ensure that new schedule is a suffix of the new queue    
    val (fsched, fq, t2) = pay(nsched, nq)
    (Wrapper(fq, fsched), t1 + t2 + 1)

  } //ensuring(res => res._1.valid && res._2 <= 6)

  def pay[T](sched: List[ConQ[T]], xs: ConQ[T]): (List[ConQ[T]], ConQ[T], BigInt) = {
    require(
      //        /queueScheduleProperty(xs, sched) ||
      sched match {
        case Cons(s @ Spine(_, PushLazy(_, nestq)), tail) =>
          weakScheduleProperty(xs, s) &&
            schedulesProperty(nestq, tail)
        case Nil() =>
          xs.valid
        case _ => false
      })
    sched match {
      case Cons(s @ Spine(_, PushLazy(_, nestq)), rest) =>
        val (Spine(_, matr), nxs, matt) = materialize(s, xs)
        matr match {
          case Spine(_, PushLazy(_, _)) =>
            (Cons(matr, rest), nxs, matt + 1)
          case Spine(_, rear) =>
            (rest, nxs, matt + 1)
        }
      case Nil() =>
        (Nil(), xs, 1) // here every thing is concretized
    }
  }*/ /*ensuring (res => schedulesProperty(res._2, res._1) && 
		  			res._3 <= 3)*/
}
