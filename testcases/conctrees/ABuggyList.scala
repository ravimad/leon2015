object Testcase {

  abstract class LeftList 
  case class LCons(l: LeftList, x: BigInt) extends LeftList
  case class LNil() extends LeftList
  
  def append(xs: LCons, y: BigInt, b: Boolean): (LCons, BigInt) = {
    if (b)
      (LCons(xs, y), 0)
    else {
      xs.l match {
        case l @ LCons(_, _) =>
          val (r, t) = append(l, y, b)
          (r, t + 1)
        case LNil() =>
          (LCons(LCons(LNil(), y), xs.x), 0)        
      }
    }
  } ensuring (res => res._2 <= lsize(xs) - lsize(res._1))
  
  def lsize(l: LeftList) : BigInt = {
    l match {
      case LCons(l, r) => lsize(l) + 1
      case _ => 0        
    }
  } ensuring(_ >= 0)  
}
