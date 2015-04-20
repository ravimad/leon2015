.. _purescala:

Pure Scala
=============================


Leon supports two kinds of top-level declarations:

1. ADT definitions in the form of an abstract class and case classes/objects

.. code-block:: scala

   abstract class Foo
   case class Bar(a: Int) extends Foo
   case object Gee extends Foo

2. Objects/modules, for grouping classes and functions

.. code-block:: scala

   object Specs {
      def foo(a: Int) = {
         a + 1
      }

      case class Foo(a: Int)
   }


Algebraic Data Types
--------------------

Abstract Classes
****************

ADT roots need to be defined as abstract, unless the ADT is defined with only one case class/object. Unlike in Scala, abstract classes cannot define fields or constructor arguments.

.. code-block:: scala

 abstract class MyType


Case Classes
************

This abstract root can be extended by a case-class, defining several fields:

.. code-block:: scala

 case class MyCase1(f: Type, f2: MyType) extends MyType
 case class MyCase2(f: Int) extends MyType

.. note::
 You can also define single case-class, for Tuple-like structures.

Case Objects
************

It is also possible to defined case objects, without fields:

.. code-block:: scala

 case object BaseCase extends MyType


Generics
--------

Leon supports type parameters for classes and functions.

.. code-block:: scala

 object Test {
   abstract class List[T]
   case class Cons[T](hd: T, tl: List[T]) extends List[T]
   case class Nil[T]() extends List[T]

   def contains[T](l: List[T], el: T) = { ... }
 }


.. note::
 Type parameters are always **invariant**. It is not possible to define ADTs like:

 .. code-block:: scala

  abstract class List[T]
  case class Cons[T](hd: T, tl: List[T]) extends List[T]
  case object Nil extends List[Nothing]

 Leon in fact restricts type parameters to "simple hierarchies", where subclasses define the same type parameters in the same order.

Methods
-------

You can currently define methods in ADT roots:

.. code-block:: scala

 abstract class List[T] {
   def contains(e: T) = { .. }
 }
 case class Cons[T](hd: T, tl: List[T]) extends List[T]
 case object Nil extends List[Nothing]

 def test(a: List[Int]) = a.contains(42)


Specifications
--------------

Leon supports two kinds of specifications to functions and methods:

Preconditions
*************

Preconditions constraint the argument and is expressed using `require`. It should hold for all calls to the function.

.. code-block:: scala

 def foo(a: Int, b: Int) = {
   require(a > b)
   ...
 }

Postconditions
**************

Postconditions constraint the resulting value, and is expressed using `ensuring`:

.. code-block:: scala

 def foo(a: Int): Int = {
   a + 1
 } ensuring { res => res > a }


Expressions
-----------

Leon supports most purely-functional Scala expressions:

Pattern matching
****************

.. code-block:: scala

 expr match {
    // Simple (nested) patterns:
    case CaseClass( .. , .. , ..) => ...
    case v @ CaseClass( .. , .. , ..) => ...
    case v : CaseClass => ...
    case (t1, t2) => ...
    case 42 => ...
    case _ => ...

    // can also be guarded, e.g.
    case CaseClass(a, b, c) if a > b => ...
 }

Values
******

.. code-block:: scala

 val x = ...

 val (x, y) = ...


Inner Functions
***************

.. code-block:: scala

 def foo(x: Int) = {
   val y = x + 1
   def bar(z: Int) = {
      z + y
   }
   bar(42)
 }


Predefined Types
****************

TupleX
######

.. code-block:: scala

 val x = (1,2,3)
 val x = 1 -> 2 // alternative Scala syntax for Tuple2
 x._1 // 1

Boolean
#######

.. code-block:: scala

  a && b
  a || b
  a == b
  !a

Int
###

.. code-block:: scala

 a + b
 a - b
 -a
 a * b
 a / b
 a % b // a modulo b
 a < b
 a <= b
 a > b
 a >= b
 a == b

.. note::
 Integers are treated as 32bits integers and are subject to overflows.

BigInt
######

.. code-block:: scala

 val a = BigInt(2)
 val b = BigInt(3)

 -a
 a + b
 a - b
 a * b
 a / b
 a % b // a modulo b
 a < b
 a > b
 a <= b
 a >= b
 a == b

.. note::
 BigInt are mathematical integers (arbitrary size, no overflows).

Set
###

.. code-block:: scala

 val s1 = Set(1,2,3,1)
 val s2 = Set[Int]()

 s1 ++ s2 // Set union
 s1 & s2  // Set intersection
 s1 -- s2 // Set difference
 s1 subsetOf s2
 s1 contains 42


Functional Array
################

.. code-block:: scala

 val a = Array(1,2,3)

 a(index)
 a.updated(index, value)
 a.length


Map
###

.. code-block:: scala

 val  m = Map[Int, Boolean](42 -> false)

 m(index)
 m isDefinedAt index
 m contains index
 m.updated(index, value)

