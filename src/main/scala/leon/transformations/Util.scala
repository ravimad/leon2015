package leon
package transformations

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Types._


object FileCountGUID {
	 var fileCount = 0
	 def getID : Int = {
	   var oldcnt = fileCount
	   fileCount += 1
	   oldcnt
	 }
}

//three valued logic
object TVL {
  abstract class Value 
  object FALSE extends Value
  object TRUE extends Value
  object MAYBE extends Value
}

object Util {
    
  val zero = InfiniteIntegerLiteral(0)
  val one = InfiniteIntegerLiteral(1)
  
  /**
   * Here, we exclude empty units that do not have any modules and empty 
   * modules that do not have any definitions
   */
  def copyProgram(prog: Program, mapdefs: (Seq[Definition] => Seq[Definition])) : Program = {
    prog.copy(units = prog.units.collect {
      case unit if(!unit.modules.isEmpty) => unit.copy(modules = unit.modules.collect {
        case module if(!module.defs.isEmpty) => 
          module.copy(defs = mapdefs(module.defs))
      })
    })    
  }
  
}  