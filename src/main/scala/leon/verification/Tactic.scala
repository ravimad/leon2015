/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package verification

import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._

abstract class Tactic(vctx: VerificationContext) {
  val description : String

  def generateVCs(fdUnsafe: FunDef): Seq[VC] = {
    val fd = fdUnsafe.duplicate
    fd.fullBody = matchToIfThenElse(fd.fullBody)
    generatePostconditions(fd) ++
    generatePreconditions(fd) ++
    generateCorrectnessConditions(fd)
  }

  def generatePostconditions(function: FunDef): Seq[VC]
  def generatePreconditions(function: FunDef): Seq[VC]
  def generateCorrectnessConditions(function: FunDef): Seq[VC]

  // Helper functions
  protected def precOrTrue(fd: FunDef): Expr = fd.precondition match {
    case Some(pre) => pre
    case None => BooleanLiteral(true)
  }

  protected def collectWithPC[T](f: PartialFunction[Expr, T])(expr: Expr): Seq[(T, Expr)] = {
    CollectorWithPaths(f).traverse(expr)
  }
}
