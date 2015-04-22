package leon
package transformations
import purescala.Common._
import purescala.Definitions._
import purescala.Extractors._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Types._
import leon.purescala.ScalaPrinter
import leon.utils._
import Util._

object RecursionCountPhase extends InstrumentationPhase {
  val name = "Recursion/Loop count Instrumentation Phase"
  val description = "Allows use of `rec` in the postconditions"  

  def IsInstrumentationVariable(p: Program): (Expr => Boolean) = {
    val instFun = Library(p).lookup("leon.instrumentation.rec") collect { case fd: FunDef => fd }
    (e: Expr) => e match {
      case FunctionInvocation(tfd, _) if (tfd.fd == instFun.get) =>
        true
      case _ => false
    }
  }

  def instrumentationType: TypeTree = IntegerType

  def instrumentation(fd: FunDef, e: Expr, subInsts: Seq[Expr]): Expr = e match {
    case t: Terminal => zero
    case FunctionInvocation(TypedFunDef(`fd`, _), _) =>
      //Note that the last element of subInsts is the instExpr of the invoked function
      Plus(one, subInsts.last) //this adds the costs of recursive invocations 
    case _ => zero
  }

  def instrumentIfThenElse(e: IfExpr, condInst: Expr, thenInst: Expr, elzeInst: Expr): (Expr, Expr) = {
    (zero, zero)
  }
}
