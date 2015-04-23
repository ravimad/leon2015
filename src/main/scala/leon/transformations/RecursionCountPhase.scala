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

  def getProgramInstrumenter(p: Program) = {
    new ProgramInstrumenter(p) {
      val instFun = Library(p).lookup("leon.instrumentation.rec") collect { case fd: FunDef => fd }

      def instrumentVariable(e: Expr) = e match {
        case FunctionInvocation(tfd, _) if (tfd.fd == instFun.get) =>
          true
        case _ => false
      }

      def instrumentType: TypeTree = IntegerType

      def getExprInstrumenter(fd: FunDef, funMap: Map[FunDef, FunDef]): ExprInstrumenter = {
        new ExprInstrumenter(fd, funMap) {
          def instrumentation(e: Expr, subInsts: Seq[Expr]): Expr = e match {
            case t: Terminal => zero
            case FunctionInvocation(TypedFunDef(`fd`, _), _) => // is this is a direct recursive call ?
              //Note that the last element of subInsts is the instExpr of the invoked function
              Plus(one, subInsts.last) //this adds the costs of recursive invocations 
            case FunctionInvocation(TypedFunDef(callee, _), _) if(cg.transitivelyCalls(callee, fd)) =>
              //this is an indirect recursive call
              Plus(one, subInsts.last) 
            case _ => zero
          }

          def instrumentIfThenElse(e: IfExpr, condInst: Expr, thenInst: Expr, elzeInst: Expr): (Expr, Expr) = {
            (zero, zero)
          }
        }
      }
    }
  }

}
