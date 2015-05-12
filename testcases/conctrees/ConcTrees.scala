import leon.instrumentation._
import leon.collection._
import leon.lang._
import ListSpecs._

object ConcTrees {

  import ListOperationsAndProperties._

  def max(x: BigInt, y: BigInt): BigInt = if (x >= y) x else y
  def abs(x: BigInt): BigInt = if (x < 0) -x else x

  sealed abstract class Conc[T] {

    def isEmpty: Boolean = {
      this == Empty[T]()
    }

    def isLeaf: Boolean = {
      this match {
        case Empty() => true
        case Single(_) => true
        case _ => false
      }
    }

    def isNormalized: Boolean = this match {
      case Append(_, _) => false
      case _ => true
    }

    def valid: Boolean = {
      concInv && balanced && appendInv
      /*(this match { //validity should hold for sub-structures
          case Empty() => true
          case Single(_) => true
          case CC(l, r) =>
            l.valid && r.valid
          case Append(l, r) =>
            l.valid && r.valid
        })*/
    }

    /**
     * (a) left and right trees of conc node should be non-empty
     * (b) they cannot be append nodes
     */
    def concInv: Boolean = this match {
      case CC(l, r) =>
        !l.isEmpty && !r.isEmpty &&
          l.isNormalized && r.isNormalized &&
          l.concInv && r.concInv
      case _ => true
    }

    def balanced: Boolean = {
      this match {
        case CC(l, r) =>
          l.level - r.level >= -1 && l.level - r.level <= 1 &&
            l.balanced && r.balanced
        case _ => true
      }
    }

    /**
     * (a) Right subtree of an append node is not an append node
     * (b) If the tree is of the form a@Append(b@Append(_,_),_) then
     * 		a.right.level < b.right.level
     * (c) left and right are not empty
     */
    def appendInv: Boolean = this match {
      case Append(l, r) =>
        !l.isEmpty && !r.isEmpty &&
          l.valid && r.valid &&
          r.isNormalized &&
          (l match {
            case Append(_, lr) =>
              lr.level > r.level
            case _ => true
          })
      case _ => true
    }

    val level: BigInt = {
      (this match {
        case Empty() => 0
        case Single(x) => 0
        case CC(l, r) =>
          1 + max(l.level, r.level)
        case Append(l, r) =>
          1 + max(l.level, r.level)
      }): BigInt
    } ensuring (_ >= 0)

    val size: BigInt = {
      (this match {
        case Empty() => 0
        case Single(x) => 1
        case CC(l, r) =>
          l.size + r.size
        case Append(l, r) =>
          l.size + r.size
      }): BigInt
    } ensuring (_ >= 0)

    def toList: List[T] = {
      this match {
        case Empty() => Nil[T]()
        case Single(x) => Cons(x, Nil[T]())
        case CC(l, r) =>
          l.toList ++ r.toList // note: left elements precede the right elements in the list
        case Append(l, r) =>
          l.toList ++ r.toList
      }
    } ensuring (res => res.size == this.size)
  }

  case class Empty[T]() extends Conc[T]
  case class Single[T](x: T) extends Conc[T]
  case class CC[T](left: Conc[T], right: Conc[T]) extends Conc[T]
  case class Append[T](left: Conc[T], right: Conc[T]) extends Conc[T]

  /*class Chunk(val array: Array[T], val size: Int, val k: Int) extends Leaf[T] {
    def level = 0
    override def toString = s"Chunk(${array.mkString("", ", ", "")}; $size; $k)"
  }*/

  def lookup[T](xs: Conc[T], i: BigInt): (T, BigInt) = {
    require(xs.valid && !xs.isEmpty && i >= 0 && i < xs.size)
    xs match {
      case Single(x) => (x, 0)
      case CC(l, r) =>
        if (i < l.size) {
          val (res, t) = lookup(l, i)
          (res, t + 1)
        } else {
          val (res, t) = lookup(r, i - l.size)
          (res, t + 1)
        }
      case Append(l, r) =>
        if (i < l.size) {
          val (res, t) = lookup(l, i)
          (res, t + 1)
        } else {
          val (res, t) = lookup(r, i - l.size)
          (res, t + 1)
        }
    }
  } ensuring (res => res._2 <= xs.level && // lookup time is linear in the height
    res._1 == xs.toList(i) && // correctness
    instAppendIndexAxiom(xs, i)) // an auxiliary axiom instantiation that required for the proof

  def instAppendIndexAxiom[T](xs: Conc[T], i: BigInt): Boolean = {
    require(0 <= i && i < xs.size)
    xs match {
      case CC(l, r) =>
        appendIndex(l.toList, r.toList, i)
      case Append(l, r) =>
        appendIndex(l.toList, r.toList, i)
      case _ => true
    }
  }.holds

  def update[T](xs: Conc[T], i: BigInt, y: T): (Conc[T], BigInt) = {
    require(xs.valid && !xs.isEmpty && i >= 0 && i < xs.size)
    xs match {
      case Single(x) => (Single(y), 0)
      case CC(l, r) =>
        if (i < l.size) {
          val (nl, t) = update(l, i, y)
          (CC(nl, r), t + 1)
        } else {
          val (nr, t) = update(r, i - l.size, y)
          (CC(l, nr), t + 1)
        }
      case Append(l, r) =>
        if (i < l.size) {
          val (nl, t) = update(l, i, y)
          (Append(nl, r), t + 1)
        } else {
          val (nr, t) = update(r, i - l.size, y)
          (Append(l, nr), t + 1)
        }
    }
  } ensuring (res => res._1.level == xs.level && // heights of the input and output trees are equal
    res._1.valid && // tree invariants are preserved
    res._2 <= xs.level && // update time is linear in the height of the tree
    res._1.toList == updated(xs.toList, i, y) && // correctness
    instAppendUpdateAxiom(xs, i, y)) // an auxiliary axiom instantiation

  def instAppendUpdateAxiom[T](xs: Conc[T], i: BigInt, y: T): Boolean = {
    require(i >= 0 && i < xs.size)
    xs match {
      case CC(l, r) =>
        appendUpdate(l.toList, r.toList, i, y)
      case Append(l, r) =>
        appendUpdate(l.toList, r.toList, i, y)
      case _ => true
    }
  }.holds

  def normalize[T](t: Conc[T]): (Conc[T], BigInt) = {
    require(t.valid)
    t match {
      case Append(l, r) =>
        wrap(l, r)
      case _ =>
        (t, 0)
    }
  } ensuring (res => res._1.valid && res._1.isNormalized)

  def wrap[T](xs: Conc[T], ys: Conc[T]): (Conc[T], BigInt) = {
    require(xs.valid && ys.valid && ys.isNormalized)
    xs match {
      case Append(l, r) =>
        val (nr, t) = concatNormalized(r, ys)
        val (res, t2) = wrap(l, nr)
        (res, t + t2)
      case _ =>
        concatNormalized(xs, ys)
    }
  } ensuring (res => res._1.valid && res._1.isNormalized)

  /**
   * A generic concat that applies to general concTrees
   */
  def concat[T](xs: Conc[T], ys: Conc[T]): (Conc[T], BigInt) = {
    require(xs.valid && ys.valid)
    val (nxs, t1) = normalize(xs)
    val (nys, t2) = normalize(ys)
    val (res, t3) = concatNormalized(nxs, nys)
    (res, t1 + t2 + t3)
  }

  /**
   * This concat applies only to normalized trees.
   * This prevents concat from being recursive
   */
  def concatNormalized[T](xs: Conc[T], ys: Conc[T]): (Conc[T], BigInt) = {
    require(xs.valid && ys.valid &&
      xs.isNormalized && ys.isNormalized)
    (xs, ys) match {
      case (xs, Empty()) => (xs, 0)
      case (Empty(), ys) => (ys, 0)
      case _ =>
        concatNonEmpty(xs, ys)
    }
  } ensuring (res => res._1.valid && // tree invariants
    res._1.level <= max(xs.level, ys.level) + 1 && // height invariants
    res._1.level >= max(xs.level, ys.level) &&
    (res._1.toList == xs.toList ++ ys.toList) && // correctness
    res._1.isNormalized && //auxiliary properties
    appendEmpty(xs.toList, ys.toList) // an auxiliary lemma     
    )

  def concatNonEmpty[T](xs: Conc[T], ys: Conc[T]): (Conc[T], BigInt) = {
    require(xs.valid && ys.valid &&
      xs.isNormalized && ys.isNormalized &&
      !xs.isEmpty && !ys.isEmpty)

    val diff = ys.level - xs.level
    if (diff >= -1 && diff <= 1)
      (CC(xs, ys), 0)
    else if (diff < -1) {
      // ys is smaller than xs
      xs match {
        case CC(l, r) =>
          if (l.level >= r.level) {
            val (nr, t) = concatNonEmpty(r, ys)
            (CC(l, nr), t + 1)
          } else {
            r match {
              case CC(rl, rr) =>
                val (nrr, t) = concatNonEmpty(rr, ys)
                if (nrr.level == xs.level - 3) {
                  val nl = l
                  val nr = CC(rl, nrr)
                  (CC(nl, nr), t + 1)
                } else {
                  val nl = CC(l, rl)
                  val nr = nrr
                  (CC(nl, nr), t + 1)
                }
            }
          }
      }
    } else {
      ys match {
        case CC(l, r) =>
          if (r.level >= l.level) {
            val (nl, t) = concatNonEmpty(xs, l)
            (CC(nl, r), t + 1)
          } else {
            l match {
              case CC(ll, lr) =>
                val (nll, t) = concatNonEmpty(xs, ll)
                if (nll.level == ys.level - 3) {
                  val nl = CC(nll, lr)
                  val nr = r
                  (CC(nl, nr), t + 1)
                } else {
                  val nl = nll
                  val nr = CC(lr, r)
                  (CC(nl, nr), t + 1)
                }
            }
          }
      }
    }
  } ensuring (res => res._2 <= abs(xs.level - ys.level) && // time bound
    res._1.level <= max(xs.level, ys.level) + 1 && // height invariants
    res._1.level >= max(xs.level, ys.level) &&
    res._1.valid && // tree invariant is preserved
    res._1.toList == xs.toList ++ ys.toList && // correctness
    res._1.isNormalized && // auxiliary properties
    appendAssocInst(xs, ys) // instantiation of an axiom
    )

  def appendAssocInst[T](xs: Conc[T], ys: Conc[T]): Boolean = {
    (xs match {
      case CC(l, r) =>
        appendAssoc(l.toList, r.toList, ys.toList) && //instantiation of associativity of concatenation              
          (r match {
            case CC(rl, rr) =>
              appendAssoc(rl.toList, rr.toList, ys.toList) &&
                appendAssoc(l.toList, rl.toList, rr.toList ++ ys.toList)
            case _ => true
          })
      case _ => true
    }) &&
      (ys match {
        case CC(l, r) =>
          appendAssoc(xs.toList, l.toList, r.toList) &&
            (l match {
              case CC(ll, lr) =>
                appendAssoc(xs.toList, ll.toList, lr.toList) &&
                  appendAssoc(xs.toList ++ ll.toList, lr.toList, r.toList)
              case _ => true
            })
        case _ => true
      })
  }.holds

  def insert[T](xs: Conc[T], i: BigInt, y: T): (Conc[T], BigInt) = {
    require(xs.valid && i >= 0 && i <= xs.size &&
      xs.isNormalized) //note the precondition
    xs match {
      case Empty() => (Single(y), 0)
      case Single(x) =>
        if (i == 0)
          (CC(Single(y), xs), 0)
        else
          (CC(xs, Single(y)), 0)
      case CC(l, r) if i < l.size =>
        val (nl, t) = insert(l, i, y)
        val (res, t1) = concatNonEmpty(nl, r)
        (res, t + t1 + 1)
      case CC(l, r) =>
        val (nr, t) = insert(r, i - l.size, y)
        val (res, t1) = concatNonEmpty(l, nr)
        (res, t + t1 + 1)
    }
  } ensuring (res => res._1.valid && res._1.isNormalized && // tree invariants            
    res._1.level - xs.level <= 1 && res._1.level >= xs.level && // height of the output tree is at most 1 greater than that of the input tree
    res._2 <= 3 * xs.level && // time is linear in the height of the tree
    res._1.toList == insertAtIndex(xs.toList, i, y) && // correctness
    insertAppendAxiomInst(xs, i, y) // instantiation of an axiom 
    )

  def insertAppendAxiomInst[T](xs: Conc[T], i: BigInt, y: T): Boolean = {
    require(i >= 0 && i <= xs.size)
    xs match {
      case CC(l, r) => appendInsert(l.toList, r.toList, i, y)
      case _ => true
    }
  }.holds

  //TODO: why with instrumentation we are not able prove the running time here ?   
  def split[T](xs: Conc[T], n: BigInt): (Conc[T], Conc[T], BigInt) = {
    require(xs.valid && xs.isNormalized)
    xs match {
      case Empty() =>
        (Empty(), Empty(), 0)
      case s @ Single(x) =>
        if (n <= 0) { //a minor fix
          (Empty(), s, 0)
        } else {
          (s, Empty(), 0)
        }
      case CC(l, r) =>
        if (n < l.size) {
          val (ll, lr, t) = split(l, n)
          val (nr, t2) = concatNormalized(lr, r)
          (ll, nr, t + t2 + 1)
        } else if (n > l.size) {
          val (rl, rr, t) = split(r, n - l.size)
          val (nl, t2) = concatNormalized(l, rl)
          (nl, rr, t + t2 + 1)
        } else {
          (l, r, 0)
        }
    }
  } ensuring (res => res._1.valid && res._2.valid && // tree invariants are preserved
    res._1.isNormalized && res._2.isNormalized &&
    xs.level >= res._1.level && xs.level >= res._2.level && // height bounds of the resulting tree
    res._3 <= xs.level + res._1.level + res._2.level && // time is linear in height
    res._1.toList == xs.toList.take(n) && res._2.toList == xs.toList.drop(n) && // correctness
    instSplitAxiom(xs, n) // instantiation of an axiom     
    )

  def instSplitAxiom[T](xs: Conc[T], n: BigInt): Boolean = {
    xs match {
      case CC(l, r) =>
        appendTakeDrop(l.toList, r.toList, n)
      case _ => true
    }
  }.holds

  /*def appendTop[T](xs: Conc[T], ys: Conc[T]): Conc[T] = {
    require(ys.isLeaf)
    xs match {
      case Append() => append(xs, ys)
      case _ <> _ => new Append(xs, ys)
      case Empty => ys
      case xs: Leaf[T] => new <>(xs, ys)
    }
  }

  @tailrec private def append[T](xs: Append[T], ys: Conc[T]): Conc[T] = {
    if (xs.right.level > ys.level) new Append(xs, ys)
    else {
      val zs = new <>(xs.right, ys)
      xs.left match {
        case ws @ Append(_, _) => append(ws, zs)
        case ws if ws.level <= zs.level => ws <> zs
        case ws => new Append(ws, zs)
      }
    }
  }*/
}

object ListOperationsAndProperties {

  /**
   * A procedure that updates a list at a given index.
   * This will be added to the standard list library
   */
  def updated[T](l: List[T], i: BigInt, y: T): List[T] = {
    require(0 <= i && i < l.size)
    l match {
      case Cons(x, tail) if i == 0 =>
        Cons[T](y, tail)
      case Cons(x, tail) =>
        Cons[T](x, updated(tail, i - 1, y))
    }
  }

  /**
   * A procedure that inserts into a list at a given index.
   * This will be added to the standard list library
   */
  def insertAtIndex[T](l: List[T], i: BigInt, y: T): List[T] = {
    require(0 <= i && i <= l.size)
    l match {
      case Nil() => Cons[T](y, Nil())
      case _ if i == 0 => Cons[T](y, l)
      case Cons(x, tail) =>
        Cons[T](x, insertAtIndex(tail, i - 1, y))
    }
  }

  // A lemma about `append` and `updated`
  def appendUpdate[T](l1: List[T], l2: List[T], i: BigInt, y: T): Boolean = {
    require(0 <= i && i < l1.size + l2.size)
    // induction scheme
    (l1 match {
      case Nil() => true
      case Cons(x, xs) => if (i == 0) true else appendUpdate[T](xs, l2, i - 1, y)
    }) &&
      // lemma
      (updated(l1 ++ l2, i, y) == (
        if (i < l1.size)
          updated(l1, i, y) ++ l2
        else
          l1 ++ updated(l2, (i - l1.size), y)))
  }.holds

  // A lemma about list `append`
  def appendEmpty[T](l1: List[T], l2: List[T]): Boolean = {
    // induction scheme
    (l1 match {
      case Nil() => true
      case Cons(x, xs) => appendEmpty(xs, l2)
    }) &&
      // lemma
      (l2 != Nil[T]() || l1 ++ l2 == l1) // the property
  }.holds

  // a lemma about `append`, `take` and `drop`
  def appendTakeDrop[T](l1: List[T], l2: List[T], n: BigInt): Boolean = {
    //induction scheme
    (l1 match {
      case Nil() => true
      case Cons(x, xs) => if (n <= 0) true else appendTakeDrop[T](xs, l2, n - 1)
    }) &&
      // lemma
      ((l1 ++ l2).take(n) == (
        if (n < l1.size) l1.take(n)
        else if (n > l1.size) l1 ++ l2.take(n - l1.size)
        else l1)) &&
        ((l1 ++ l2).drop(n) == (
          if (n < l1.size) l1.drop(n) ++ l2
          else if (n > l1.size) l2.drop(n - l1.size)
          else l2))
  }.holds

  // A lemma about `append` and `insertAtIndex`
  def appendInsert[T](l1: List[T], l2: List[T], i: BigInt, y: T): Boolean = {
    require(0 <= i && i <= l1.size + l2.size)
    (l1 match {
      case Nil() => true
      case Cons(x, xs) => if (i == 0) true else appendInsert[T](xs, l2, i - 1, y)
    }) &&
      // lemma
      (insertAtIndex(l1 ++ l2, i, y) == (
        if (i < l1.size) insertAtIndex(l1, i, y) ++ l2
        else l1 ++ insertAtIndex(l2, (i - l1.size), y)))
  }.holds
}
