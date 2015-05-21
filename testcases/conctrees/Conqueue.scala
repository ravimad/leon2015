import leon.instrumentation._
import leon.collection._
import leon.lang._
import ListSpecs._
import leon.annotation._

object Conqueue {
  import conctrees.ConcTrees._

  def max(x: BigInt, y: BigInt): BigInt = if (x >= y) x else y
  def abs(x: BigInt): BigInt = if (x < 0) -x else x
  
  /**
   * This class stores a value and the
   * time it would take to compute the value if
   * it was completed lazily while accessing it.
   */
  case class Lazy[T](x: T, tx: BigInt) 

  sealed abstract class ConQ[T] {

    /*def isTip: Boolean = {
      this match {
        case Tip(_) => true
        case _ => false
      }
    }*/    
  }  
  case class Tip[T](t: Conc[T]) extends ConQ[T]
  case class Spine[T](head: Conc[T], rear: Lazy[ConQ[T]]) extends ConQ[T] {
    /**
     * Evaluates the rear one step and returns it.
     * The second return value is the time taken
     * to evalute the rear, which is captured by the Lazy 
     * constructor.
     */
    def getRear: (ConQ[T], BigInt) = {      
      this.rear match {
        case Lazy(rear, tme) => (rear, tme)        
      }
    }
  }
//  /case class SpineLazy[T](head :Conc[T], rear: () => ConQ[T]) extends ConQ[T] // rear is lazily evaluated

  def pushLeft[T](ys: Single[T], xs: ConQ[T]): (ConQ[T], BigInt) = { //require some validity invariants 
    xs match {
      case Tip(CC(_, _)) => 
        (new Spine(ys, Lazy(xs, 0)), 0) //time needed to evalute xs is '0'
      case Tip(Empty()) => 
        (Tip(ys), 0)
      case Tip(t @ Single(_)) => 
        (Tip(CC(ys, t)), 0)
      case s@Spine(_, _) => 
        pushLeftLazy(ys, s) 
    }
  }

  def pushLeftLazy[T](ys: Conc[T], xs: Spine[T]): (ConQ[T], BigInt) = {
    require(!ys.isEmpty &&
      (xs.head.isEmpty || xs.head.level == ys.level))
      
    xs.head match {
      case Empty() => 
        val (rear, tme) = xs.getRear //evaluates rear one step
        (Spine(ys, Lazy(rear, 0)), tme)  //adds up the time taken to evaluate rear
      case head =>
        //here, head and ys are of the same level
        val carry = CC(head, ys)
        val (rear, tme) = xs.getRear //evaluates rear one step
        rear match { 
          case s@Spine(h, _) =>
            val (nrear, ntme) = pushLeftLazy(carry, s)
            (Spine(Empty(), Lazy(nrear, ntme)), tme) 
            	// note: ntme is not added here but passed to the lazy constructor.
            	//  this mimics lazy evaluation.
          case Tip(tree) if tree.level > carry.level =>
            (Spine(Empty(), Lazy[ConQ[T]](Spine(carry, Lazy(rear, 0)), 0)), tme) 
            		// no lazy evaluation here, so the time passed to lazy construct are zero
          case Tip(tree) =>
            //here tree level and carry level are equal
            (Spine(Empty(), Lazy[ConQ[T]](Spine(Empty(),  
                Lazy[ConQ[T]](Tip(CC(tree, carry)), 0)), 
                0)), tme)
                	//no lazy evaluation here as well
        }
    }
  }  
  
  case class Wrapper[T](queue: ConQ[T], schedule: List[Spine[T]])
  
  def pushLeftAndPay[T](w: Wrapper[T], ys: Single[T]): (Wrapper[T], BigInt) = {
    val (newSchedule, t1) = w.schedule match {
      case Nil() => (Nil[Spine[T]](), BigInt(0)) // hoorah, no work scheduled
      case Cons(work, moreWork) =>
        // evaluate one step  
      	// (note: we got the time to evaluate rear from the Lazy construct)
        val (rear, tme) = work.getRear
        rear match {
          case s: Spine[T] =>
            (s :: moreWork, tme)
          case _ =>
            (moreWork, tme)
        }
    }

    val (nq, t2) = pushLeft(ys, w.queue)
    nq match {
      case s: Spine[T] => //omitting created-with-suspension for now.
        (Wrapper(s, Cons[Spine[T]](s, newSchedule)), t1 + t2)
      case tree =>
        (Wrapper(tree, newSchedule), t1 + t2)
    }
  }

}
