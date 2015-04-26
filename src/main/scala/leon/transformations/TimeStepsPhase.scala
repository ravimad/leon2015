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

/**
 * TODO: to be tested.
 */
object TimeStepsPhase extends InstrumentationPhase {
  val name = "Time Instrumentation Phase"
  val description = "Allows use of `time` in the postconditions"

  def getProgramInstrumenter(p: Program) = {
    new ProgramInstrumenter(p) {
      val timeFun = Library(p).lookup("leon.instrumentation.time") collect { case fd: FunDef => fd }
      def instrumentVariable(e: Expr): Boolean = e match {
        case FunctionInvocation(tfd, _) if (tfd.fd == timeFun.get) =>
          true
        case _ => false
      }
      def instrumentType: TypeTree = IntegerType

      def functionsToInstrument(rootFuns: Set[FunDef]): Set[FunDef] = {
        //find all functions transitively called from rootFuncs (here ignore functions called via pre/post conditions)      
        rootFuns.foldLeft(Set[FunDef]())((acc, fd) => acc ++ cg.transitiveCallees(fd))
      }
      
      def getExprInstrumenter(fd: FunDef, funMap: Map[FunDef, FunDef]): ExprInstrumenter = {
        new ExprInstrumenter(fd, funMap) {
          def shouldInstrument(e : Expr) = true 
          
          def instrument(e: Expr, subInsts: Seq[Expr]): Expr = e match {
            case t: Terminal => costOfExpr(t)
            case _ =>
              subInsts.foldLeft(costOfExpr(e): Expr)(
                (acc: Expr, subeTime: Expr) => Plus(subeTime, acc))
          }          
          def instrumentIfThenElse(e: IfExpr, condInst: Option[Expr],
            thenInst: Option[Expr], elzeInst: Option[Expr]): (Expr, Expr) = {
            val costIf = costOfExpr(e)
            (Plus(costIf, Plus(condInst.get, thenInst.get)), 
                Plus(costIf, Plus(condInst.get, elzeInst.get)))
          }
        }
      }
    }
  }

  def costOf(e: Expr): Int =
    e match {
      case FunctionInvocation(fd, args) => 1
      case t: Terminal => 0
      case _ => 1
    }

  def costOfExpr(e: Expr) = InfiniteIntegerLiteral(costOf(e))
}
