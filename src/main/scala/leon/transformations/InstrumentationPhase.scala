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
 * A generic instrumentation phase that instruments every expression (function invocation etc.)
 * as function of its sub-expressions
 * TODO: is it necessary to create new functions even if they are not instrumented or do not use instrumented functions?
 */
abstract class InstrumentationPhase extends TransformationPhase {

  def apply(ctx: LeonContext, program: Program): Program = {
    getProgramInstrumenter(program)()
  }

  def getProgramInstrumenter(p: Program): ProgramInstrumenter

  abstract class ProgramInstrumenter(program: Program) {
    //the instrumentation variable is generall a function call
    def instrumentVariable(e: Expr): Boolean

    def instrumentType: TypeTree

    protected val cg = CallGraphUtil.constructCallGraph(program, onlyBody = true)

    def functionsToInstrument(rootFuns: Set[FunDef]): Set[FunDef]

    var instFuncs: Set[FunDef] = _ //set in the function apply (TODO: get rid of this mutable state)

    def apply(): Program = {
      // Map from old fundefs to new fundefs
      var funMap = Map[FunDef, FunDef]()

      val rootFuncs = program.definedFunctions.collect {
        case fd if (fd.hasPostcondition &&
          exists(instrumentVariable)(fd.postcondition.get)) =>
          //println("Found a function with time: "+fd)
          fd
      }.toSet
      instFuncs = functionsToInstrument(rootFuncs)

      //create new functions.  Augment the return type of a function iff the postcondition uses     
      //the instrumentation variable or if the function is transitively called from such a function
      for (fd <- program.definedFunctions) {
        if (instFuncs.contains(fd)) {
          val newRetType = TupleType(Seq(fd.returnType, instrumentType))
          val freshId = FreshIdentifier(fd.id.name, newRetType)
          val newfd = new FunDef(freshId, fd.tparams, newRetType, fd.params, DefType.MethodDef)
          funMap += (fd -> newfd)
        } else {
          //here we need not augment the return types
          val freshId = FreshIdentifier(fd.id.name, fd.returnType)
          val newfd = new FunDef(freshId, fd.tparams, fd.returnType, fd.params, DefType.MethodDef)
          funMap += (fd -> newfd)
        }
      }
      //println("FunMap: "+funMap.map((elem) => (elem._1.id, elem._2.id)))

      def mapExpr(ine: Expr): Expr = {
        simplePostTransform((e: Expr) => e match {
          case FunctionInvocation(tfd, args) =>
            if (instFuncs.contains(tfd.fd)) {
              TupleSelect(FunctionInvocation(TypedFunDef(funMap(tfd.fd), tfd.tps), args), 1)
            } else {
              val fi = FunctionInvocation(TypedFunDef(funMap(tfd.fd), tfd.tps), args)
              fi
            }
          case _ => e
        })(ine)
      }

      def mapBody(body: Expr, f: FunDef) = {
        //instrument the expression so that it tracks time
        if (instFuncs.contains(f)) {
          getExprInstrumenter(f, funMap)(body)
        } else {
          mapExpr(body)
        }
      }

      def mapPost(pred: Expr, from: FunDef, to: FunDef) = {
        pred match {
          case Lambda(Seq(ValDef(fromRes, _)), postCond) if (instFuncs.contains(from)) =>
            val toResId = FreshIdentifier(fromRes.name, to.returnType, true)
            val instCond = postMap((e: Expr) => e match {
              case Variable(`fromRes`) =>
                Some(TupleSelect(toResId.toVariable, 1))
              case _ if instrumentVariable(e) =>
                Some(TupleSelect(toResId.toVariable, 2))
              case _ =>
                None
            })(postCond)
            Lambda(Seq(ValDef(toResId)), mapExpr(instCond))
          case _ =>
            //replace fromRes by toRes in postCond
            /*(e: Expr) => e match {
          	case Variable(fromRes) => 
          	  Some(toResId.toVariable)          	
          	case _ => 
          	  None
          	}*/
            mapExpr(pred)
        }
      }

      for ((from, to) <- funMap) {
        //println("considering function: "+from.id.name)
        //consider from.fullBody
        to.fullBody = from.fullBody match {
          case Require(pre, body) =>
            Require(mapExpr(pre), mapBody(body, from))
          case Ensuring(Require(pre, body), post) =>
            Ensuring(Require(mapExpr(pre),
              mapBody(body, from)),
              mapPost(post, from, to))
          case Ensuring(body, post) =>
            Ensuring(mapBody(body, from), mapPost(post, from, to))
          case body =>
            mapBody(body, from)
        }
        //copy annotations
        from.annotations.foreach((str) => {
          to.addAnnotation(str)
        })
      }

      val newprog = Util.copyProgram(program, (defs: Seq[Definition]) => defs.map {
        case fd: FunDef => funMap(fd)
        case d => d
      })
      println("After Time Instrumentation: \n" + ScalaPrinter.apply(newprog))

      //print all the templates
      /*newprog.definedFunctions.foreach((fd) => 
      if(FunctionInfoFactory.hasTemplate(fd))
        println("Function: "+fd.id+" template --> "+FunctionInfoFactory.getTemplate(fd))
        )*/
      newprog
    }

    def getExprInstrumenter(fd: FunDef, funMap: Map[FunDef, FunDef]): ExprInstrumenter

    abstract class ExprInstrumenter(fd: FunDef, funMap: Map[FunDef, FunDef]) {

      def shouldInstrument(e: Expr): Boolean
      /**
       * Given an expression to be instrumented
       * and the instrumentation of each of its subexpressions,
       * computes an instrumentation for the procedure.
       * The sub-expressions correspond to expressions returned
       * by Expression Extractors.
       * fd is the function containing the expression `e`
       */
      def instrument(e: Expr, subInsts: Seq[Expr]): Expr

      /**
       * Instrument procedure specialized for if-then-else
       */
      def instrumentIfThenElse(e: IfExpr, condInst: Option[Expr],
        thenInst: Option[Expr], elzeInst: Option[Expr]): (Expr, Expr)

      // Should be called only if 'expr' has to be instrumented
      // Returned Expr is always an expr of type tuple (Expr, Int)
      def tupleify(e: Expr, subs: Seq[Expr], recons: Seq[Expr] => Expr): Expr = {
        // When called for:
        // Op(n1,n2,n3)
        // e      = Op(n1,n2,n3)
        // subs   = Seq(n1,n2,n3)
        // recons = { Seq(newn1,newn2,newn3) => Op(newn1, newn2, newn3) }
        //
        // This transformation should return, informally:
        //
        // LetTuple((e1,t1), transform(n1),
        //   LetTuple((e2,t2), transform(n2),
        //    ...
        //      Tuple(recons(e1, e2, ...), t1 + t2 + ... costOfExpr(Op)
        //    ...
        //   )
        // )
        //
        // You will have to handle FunctionInvocation specially here!
        tupleifyRecur(e, subs, recons, List(), List())
      }

      def tupleifyRecur(e: Expr, subs: Seq[Expr], recons: Seq[Expr] => Expr,
        subeVals: List[Expr], subeInsts: List[Expr]): Expr = {
        //note: subs.size should be zero if e is a terminal
        if (subs.size == 0) {
          e match {
            case t: Terminal =>
              Tuple(Seq(recons(Seq()), instrument(t, Seq())))

            case f @ FunctionInvocation(tfd, args) => {
              val newfd = funMap(tfd.fd)
              val newFunInv = FunctionInvocation(TypedFunDef(newfd, tfd.tps), subeVals)
              //create a variables to store the result of function invocation                              
              if (instFuncs(tfd.fd)) {
                //this function is also instrumented
                val resvar = Variable(FreshIdentifier("e", newfd.returnType, true))
                val valexpr = TupleSelect(resvar, 1)
                val instexpr = TupleSelect(resvar, 2)
                //Note we need to ensure that the last element of list
                val baseExpr = Tuple(Seq(valexpr, instrument(e, subeInsts :+ instexpr)))
                Let(resvar.id, newFunInv, baseExpr)
              } else {
                Tuple(Seq(newFunInv, instrument(e, subeInsts)))
              }
            }

            case _ => {
              val exprPart = recons(subeVals)
              Tuple(Seq(exprPart, instrument(e, subeInsts)))
            }
          }
        } else {
          val currExp = subs.head
          if (shouldInstrument(currExp)) {
            val resvar = Variable(FreshIdentifier("e",
              TupleType(Seq(currExp.getType, IntegerType)), true))
            val einst = TupleSelect(resvar, 2)
            val eval = TupleSelect(resvar, 1)
            val recRes = tupleifyRecur(e, subs.tail, recons, subeVals :+ eval, subeInsts :+ einst)
            //transform the current expression        
            val newCurrExpr = transform(currExp)
            val newexpr = Let(resvar.id, newCurrExpr, recRes)
            newexpr
          } else {
            //here we need not instrument the current subexpression
            tupleifyRecur(e, subs.tail, recons, subeVals :+ currExp, subeInsts)
          }
        }
      }

      /**
       * TODO: need to handle new expression trees
       * At least `match` needs to be handled so that we can have readable code
       */
      def transform(e: Expr): Expr = e match {
        case Let(i, v, b) =>
          val (ni, nv, nb, instv) = if (shouldInstrument(v)) {
            val ir = Variable(FreshIdentifier("ir", TupleType(Seq(v.getType, instrumentType)), true))
            (ir.id, transform(v), replace(Map[Expr, Expr](Variable(i) -> TupleSelect(ir, 1)), b),
              List(TupleSelect(ir, 2)))
          } else
            (i, v, b, List())
          if (shouldInstrument(b)) {
            val r = Variable(FreshIdentifier("r", TupleType(Seq(b.getType, instrumentType)), true))
            Let(ni, nv,
              Let(r.id, transform(nb), Tuple(Seq(TupleSelect(r, 1),
                instrument(e, instv :+ TupleSelect(r, 2))))))
          } else {
            Let(ni, nv, Tuple(Seq(nb, instrument(e, instv))))
          }

        case ife @ IfExpr(cond, th, elze) => {

          val (nifCons, condInstExpr) = if (shouldInstrument(cond)) {
            val rescond = Variable(FreshIdentifier("c",
              TupleType(Seq(cond.getType, instrumentType)), true))
            val recons = (e1: Expr, e2: Expr) =>
              Let(rescond.id, transform(cond), IfExpr(TupleSelect(rescond, 1), e1, e2))

            (recons, Some(TupleSelect(rescond, 2)))
          } else
            ((e1: Expr, e2: Expr) => IfExpr(cond, e1, e2), None)

          val (nthenCons, thenInstExpr) = if (shouldInstrument(th)) {
            val resthen = Variable(FreshIdentifier("th",
              TupleType(Seq(th.getType, instrumentType)), true))
            val recons = (theninst: Expr) => Let(resthen.id, transform(th),
              Tuple(Seq(TupleSelect(resthen, 1), theninst)))

            (recons, Some(TupleSelect(resthen, 2)))
          } else
            ((theninst: Expr) => Tuple(Seq(th, theninst)), None)

          val (nelseCons, elseInstExpr) = if (shouldInstrument(elze)) {
            val reselse = Variable(FreshIdentifier("el",
              TupleType(Seq(elze.getType, instrumentType)), true))
            val recons = (einst: Expr) => Let(reselse.id, transform(elze),
              Tuple(Seq(TupleSelect(reselse, 1), einst)))
            (recons, Some(TupleSelect(reselse, 2)))
          } else
            ((einst: Expr) => Tuple(Seq(elze, einst)), None)

          val (thenInst, elseInst) = instrumentIfThenElse(ife, condInstExpr,
            thenInstExpr, elseInstExpr)
          //create a final expression
          nifCons(nthenCons(thenInst), nelseCons(elseInst))
        }

        // For all other operations, we go through a common tupleifier.
        case n @ NAryOperator(ss, recons) =>
          tupleify(e, ss, recons)

        case b @ BinaryOperator(s1, s2, recons) =>
          tupleify(e, Seq(s1, s2), { case Seq(s1, s2) => recons(s1, s2) })

        case u @ UnaryOperator(s, recons) =>
          tupleify(e, Seq(s), { case Seq(s) => recons(s) })

        case t: Terminal =>
          tupleify(e, Seq(), { case Seq() => t })
      }

      def apply(e: Expr): Expr = {
        //lift all expressions that are used in matches to before matches.
        val newe = liftExprInMatch(e)
        // Removes pattern matching by translating to equivalent if-then-else            
        val input = matchToIfThenElse(newe)

        // For debugging purposes      
        /*println("#"*80)
      println("BEFORE:")
      println(input)*/

        // Apply transformations
        val res = transform(input)
        val simple = simplifyArithmetic(simplifyLets(res))

        /*println("#"*80)
      println("After:")
      println(input)*/
        simple
      }

      def liftExprInMatch(ine: Expr): Expr = {
        simplePostTransform((e: Expr) => e match {
          case MatchExpr(strut, cases) => strut match {
            case t: Terminal => e
            case _ => {
              val freshid = FreshIdentifier("m", strut.getType, true)
              Let(freshid, strut, MatchExpr(freshid.toVariable, cases))
            }
          }
          case _ => e
        })(ine)
      }
    }
  }
}
