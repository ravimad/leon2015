import leon.instrumentation._
import leon.collection._
import leon.lang._
import ListSpecs._
import leon.annotation._

object ConcTrees {

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
            case _ =>
              l.level > r.level
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

  @library
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

  @library
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

  @library
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
    res._1.toList == xs.toList.updated(i, y) && // correctness
    numTrees(res._1) == numTrees(xs) && //auxiliary property that preserves the potential function 
    instAppendUpdateAxiom(xs, i, y)) // an auxiliary axiom instantiation

  @library
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

  //@library
  def normalize[T](t: Conc[T]): (Conc[T], BigInt) = {
    require(t.valid)
    t match {
      case Append(l, r) =>
        wrap(l, r)
      case _ =>
        (t, 0)
    }
  } ensuring (res => res._1.valid &&
    res._1.isNormalized &&
    res._1.toList == t.toList && //correctness
    res._1.size == t.size && res._1.level == t.level) //normalize preseves level and size

  //@library
  def wrap[T](xs: Conc[T], ys: Conc[T]): (Conc[T], BigInt) = {
    require(xs.valid && ys.valid && ys.isNormalized && 
        xs.level > ys.level)
    xs match {
      case Append(l, r) =>
        val (nr, t) = concatNormalized(r, ys)
        val (res, t2) = wrap(l, nr)
        (res, t + t2)
      case _ =>
        concatNormalized(xs, ys)
    }
  } ensuring (res => res._1.valid &&
    res._1.isNormalized &&
    res._1.toList == xs.toList ++ ys.toList && //correctness
    res._1.size == xs.size + ys.size && //other auxiliary properties
    res._1.level <= max(xs.level, ys.level) + 1 &&
    appendAssocInst2(xs, ys)) //some lemma instantiations

  /**
   * A generic concat that applies to general concTrees
   */
  @library
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
  @library
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
    res._1.isNormalized //auxiliary properties    
    )

  @library
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
    res._1.balanced && res._1.appendInv && res._1.concInv && //this is should not be needed. But, seems necessary for leon 
    res._1.valid && // tree invariant is preserved
    res._1.toList == xs.toList ++ ys.toList && // correctness
    res._1.isNormalized && // auxiliary properties
    appendAssocInst(xs, ys) // instantiation of an axiom
    )

  @library
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

  @library
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
    res._1.toList == xs.toList.insertAtIndex(i, y) && // correctness
    insertAppendAxiomInst(xs, i, y) // instantiation of an axiom 
    )

  @library
  def insertAppendAxiomInst[T](xs: Conc[T], i: BigInt, y: T): Boolean = {
    require(i >= 0 && i <= xs.size)
    xs match {
      case CC(l, r) => appendInsert(l.toList, r.toList, i, y)
      case _ => true
    }
  }.holds

  //TODO: why with instrumentation we are not able prove the running time here ? (performance bug ?)
  @library
  def split[T](xs: Conc[T], n: BigInt): (Conc[T], Conc[T], BigInt) = {
    require(xs.valid && xs.isNormalized)
    xs match {
      case Empty() =>
        (Empty(), Empty(), BigInt(0))
      case s @ Single(x) =>
        if (n <= 0) { //a minor fix
          (Empty(), s, BigInt(0))
        } else {
          (s, Empty(), BigInt(0))
        }
      case CC(l, r) =>
        if (n < l.size) {
          val (ll, lr, t) = split(l, n)
          val (nr, t2) = concatNormalized(lr, r)
          (ll, nr, t + t2 + BigInt(1))
        } else if (n > l.size) {
          val (rl, rr, t) = split(r, n - l.size)
          val (nl, t2) = concatNormalized(l, rl)
          (nl, rr, t + t2 + BigInt(1))
        } else {
          (l, r, BigInt(0))
        }
    }
  } ensuring (res => res._1.valid && res._2.valid && // tree invariants are preserved
    res._1.isNormalized && res._2.isNormalized &&
    xs.level >= res._1.level && xs.level >= res._2.level && // height bounds of the resulting tree
    res._3 <= xs.level + res._1.level + res._2.level && // time is linear in height
    res._1.toList == xs.toList.take(n) && res._2.toList == xs.toList.drop(n) && // correctness
    instSplitAxiom(xs, n) // instantiation of an axiom     
    )

  @library
  def instSplitAxiom[T](xs: Conc[T], n: BigInt): Boolean = {
    xs match {
      case CC(l, r) =>
        appendTakeDrop(l.toList, r.toList, n)
      case _ => true
    }
  }.holds

  @library
  def append[T](xs: Conc[T], x: T): (Conc[T], BigInt) = {
    require(xs.valid)
    val ys = Single[T](x)
    xs match {
      case xs @ Append(_, _) =>
        appendPriv(xs, ys)
      case CC(_, _) =>
        (Append(xs, ys), 0) //creating an append node
      case Empty() =>
        (ys, 0)
      case Single(_) =>
        (CC(xs, ys), 0)
    }
  } ensuring (res => res._1.valid && //conctree invariants
    res._1.toList == xs.toList ++ Cons(x, Nil[T]()) && //correctness
    res._2 <= numTrees(xs) - numTrees(res._1) + 1 //time bound (worst case)
    )

  /**
   * This is a private method and is not exposed to the
   * clients of conc trees
   */
  @library
  def appendPriv[T](xs: Append[T], ys: Conc[T]): (Conc[T], BigInt) = {
    require(xs.valid && ys.valid &&
      !ys.isEmpty && ys.isNormalized &&
      xs.right.level >= ys.level)

    if (xs.right.level > ys.level)
      (Append(xs, ys), 0)
    else {
      val zs = CC(xs.right, ys)
      xs.left match {
        case l @ Append(_, _) =>
          val (r, t) = appendPriv(l, zs)
          (r, t + 1)
        case l if l.level <= zs.level => //note: here < is not possible           
          (CC(l, zs), 0)
        case l =>
          (Append(l, zs), 0)
      }
    }
  } ensuring (res => res._1.valid && //conc tree invariants
    res._1.toList == xs.toList ++ ys.toList && //correctness invariants
    res._2 <= numTrees(xs) - numTrees(res._1) + 1 && //time bound (worst case)
    appendAssocInst2(xs, ys))

  @library
  def appendAssocInst2[T](xs: Conc[T], ys: Conc[T]): Boolean = {
    xs match {
      case CC(l, r) =>
        appendAssoc(l.toList, r.toList, ys.toList)
      case Append(l, r) =>
        appendAssoc(l.toList, r.toList, ys.toList)
      case _ => true
    }
  }.holds

  @library
  def numTrees[T](t: Conc[T]): BigInt = {
    t match {
      case Append(l, r) => numTrees(l) + 1
      case _ => BigInt(1)
    }
  } ensuring (res => res >= 0)

  /**
   * A class that represents an operation on a concTree.
   * opid - an integer that denotes the function that has to be performed e.g. append, insert, update ...
   * 		opid <= 0 => the operation is lookup
   *   		opid == 1 => the operation is update
   *     	opid == 2 => the operation is insert
   *      	opid == 3 => the operation is split
   *        opid >= 4 => the operation is append
   * index, x - denote the arguments the function given by opid
   */
  case class Operation[T](opid: BigInt, /*argument to the operations*/ index: BigInt /*for lookup, update, insert, split*/ ,
    x: T /*for update, insert, append*/ )

  /**
   * Proving amortized running time of 'Append' when used ephimerally.
   * ops- a arbitrary sequence of operations,
   * noaps - number of append operations in the list
   * nops - number  of non-append operations in the list
   */
  def performOperations[T](xs: Conc[T], ops: List[Operation[T]], noaps: BigInt, nops: BigInt): (Conc[T], BigInt) = {
    require(xs.valid &&
      noaps + nops == ops.size) //not strictly necessary
    ops match {
      case Cons(Operation(id, i, _), tail) if id <= 0 =>
        //we need to perform a lookup operation
        val t1 = if (0 <= i && i < xs.size) //do the operation only if its precondition holds
          lookup(xs, i)._2
        else BigInt(0)
        val (r, t2) = performOperations(xs, tail, noaps, nops - 1)
        (r, t1 + t2) //total time = time taken by this operation + time taken by the remaining operations 

      case Cons(Operation(id, i, x), tail) if id == 1 =>
        val (newt, t1) = if (0 <= i && i < xs.size)
          update(xs, i, x)
        else (xs, BigInt(0))
        //note that only the return value is used by the subsequent operations (emphimeral use)
        val (r, t2) = performOperations(newt, tail, noaps, nops - 1)
        (r, t1 + t2)

      case Cons(Operation(id, i, x), tail) if id == 2 =>
        val (normt, t0) = normalize(xs)
        val (newt, t1) = if (0 <= i && i <= xs.size)
          insert(normt, i, x)
        else (xs, BigInt(0))
        val (r, t2) = performOperations(newt, tail, noaps, nops - 1)
        (r, t0 + t1 + t2)

      case Cons(Operation(id, n, _), tail) if id == 3 =>
        //here we use the larger tree to perform the remaining operations
        val (normt, t0) = normalize(xs)
        val (newl, newr, t1) = split(normt, n)
        val newt = if (newl.size >= newr.size) newl else newr
        val (r, t2) = performOperations(newt, tail, noaps, nops - 1)
        (r, t0 + t1 + t2)

      case Cons(Operation(id, _, x), tail) =>
        //here, we need to perform append operation
        val (newt, t1) = append(xs, x)
        val (r, t2) = performOperations(newt, tail, noaps - 1, nops)
        (r, t1 + t2)

      case Nil() =>
        (xs, 0)
    }
  }
}
