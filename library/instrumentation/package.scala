/* Copyright 2009-2015 EPFL, Lausanne */

package leon
import leon.annotation._
import leon.lang._

package object instrumentation {
  @library
  def time: BigInt = error[BigInt]("")    
  
  @library
  def rec: BigInt = error[BigInt]("")
}
