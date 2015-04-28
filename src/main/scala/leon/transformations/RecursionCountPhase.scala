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

      val sccs = cg.graph.sccs.flatMap { scc =>
        scc.map(fd => (fd -> scc.toSet))
      }.toMap

      /**
       * Instrument only those functions that are in the same sccs of the root functions
       */
      def functionsToInstrument(rootFuns: Set[FunDef]): Set[FunDef] = {
        rootFuns.flatMap(sccs.apply _)
        //        val sccs = cg.graph.sccs
        //        sccs.filterNot(_.toSet.intersect(rootFuns).isEmpty).flatten.toSet
      }

      def getExprInstrumenter(fd: FunDef, funMap: Map[FunDef, FunDef]): ExprInstrumenter = {
        new ExprInstrumenter(fd, funMap) {

          def shouldInstrument(e: Expr): Boolean = {
            exists {
              //is this a mutually recursive call ?
              case FunctionInvocation(TypedFunDef(callee, _), _) if sccs(fd)(callee) =>
                true
              case _ => false
            }(e)
          }

          def addSubInstsIfNonZero(subInsts: Seq[Expr], init: Expr): Expr = {
            subInsts.foldLeft(init) {
              case (acc, subinst) if subinst != zero =>
                if (acc == zero) subinst
                else Plus(acc, subinst)
            }
          }

          /**
           * Need to do constant propagation at the end of instrumentation
           */
          def instrument(e: Expr, subInsts: Seq[Expr]): Expr = e match {
            case FunctionInvocation(TypedFunDef(callee, _), _) if sccs(fd)(callee) =>
              //this is a recursive call
              //Note that the last element of subInsts is the instExpr of the invoked function
              addSubInstsIfNonZero(subInsts, one)
            case FunctionInvocation(TypedFunDef(callee, _), _) if instFuncs(callee) =>
              //this is not a recursive call, so do not consider the cost of the callee
              //Note that the last element of subInsts is the instExpr of the invoked function
              addSubInstsIfNonZero(subInsts.take(subInsts.size - 1), zero)
            case _ =>
              //add the cost of every sub-expression
              addSubInstsIfNonZero(subInsts, zero)
          }

          def instrumentIfThenElse(e: IfExpr, condInst: Option[Expr],
            thenInst: Option[Expr], elzeInst: Option[Expr]): (Expr, Expr) = {
            def optionToList(opte: Option[Expr]) = opte match {
              case Some(x) => List(x)
              case _ => List()
            }
            val cinst = optionToList(condInst)
            val tinst = optionToList(thenInst)
            val einst = optionToList(elzeInst)

            (addSubInstsIfNonZero(cinst ++ tinst, zero),
              addSubInstsIfNonZero(cinst ++ einst, zero))
          }
        }
      }
    }
  }

}
