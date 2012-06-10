package skeptik.experiment.compression

import scala.collection.generic.CanBuildFrom
import scala.collection.immutable.HashMap
import scala.collection.immutable.List
import scala.collection.immutable.Map
import scala.collection.immutable.MapLike
import scala.collection.mutable.ArrayBuffer
import scala.collection.mutable.Builder


class Report private (val m: HashMap[String,Double])
extends Map[String,Double] with MapLike[String,Double,Report] {
  // useless
  def +[B >: Double](kv: (String, B)) = {
    if (kv.isInstanceOf[(String,Double)])
      new Report(m + kv.asInstanceOf[(String,Double)])
    else
      m + kv
  }
  def +(kv: (String, Double)) = new Report(m + kv)
  def -(key: String) = new Report(m - key)
  override def empty = new Report(HashMap())
  def iterator = m.iterator
  def get(key: String) = m.get(key)

  def add(other: Report) = {
    def op (acc: HashMap[String,Double], kv: (String, Double)) = {
      if (acc.contains(kv._1))
        acc + (kv._1 -> (acc(kv._1) + kv._2))
      else
        acc + kv
    }
    val nmap = m.foldLeft(other.m)(op _)
    new Report(nmap)
  }

  override def toString(): String = {
    ( for ((k,v) <- m ; if (k != "num"))
      yield {
        val dotPos = k.indexOf('.')
        val valStr = String.format("%.2f", double2Double(v/m("num")))
        if (dotPos >= 0)
            k.substring(0, dotPos) + " " + valStr + " " + k.substring(dotPos+1)
        else
            k + " " + valStr
      }
    ) mkString (", ")
  }
}
object Report {
  def apply(args: (String,Double)*) = {
    val nargs = args ++ Array("num" -> 1.)
    new Report(HashMap(nargs: _*))
  }

  val empty = new Report(HashMap())
  
  // useless
  def newBuilder: Builder[(String,Double), Report] =
    new ArrayBuffer mapResult ((a: ArrayBuffer[(String,Double)]) => Report(a.toArray: _*))

  // useless
  implicit def canBuildFrom: CanBuildFrom[Report, (String,Double), Report] =
    new CanBuildFrom[Report, (String,Double), Report] {
      def apply(): Builder[(String,Double), Report] = newBuilder
      def apply(from: Report): Builder[(String,Double), Report] = newBuilder
    }
}



abstract class Measure[-P]
extends Function2[P, Report, Report]
{
  def init(p:P, r:Report): Report
}

object DumbMeasure extends Measure[Any] {
  def init (p: Any, report: Report) = report
  def apply(p: Any, report: Report) = report
}

class NoStateMeasure[P] private (name: String, fct: (P) => Double)
extends Measure[P]
{
  def init(p: P, report: Report) = report
  def apply(p:P, report: Report) = report + (name -> fct(p))
}
object NoStateMeasure
{
  def apply[P](name: String, fct: P => Double) = new NoStateMeasure(name, fct)
  def apply[P](name: String, fct: P => Double, unit: String) =
    new NoStateMeasure(name + "." + unit, fct)
}

class PercentMeasure[P] private (name: String, fct: (P) => Double)
extends Measure[P]
{
  def init( p:P, report:Report) = report + (name -> fct(p))
  def apply(p:P, report:Report) = report + (name -> (100. * fct(p) / report(name)))
}
object PercentMeasure {
  def apply[P](name: String, fct: P => Double) = new PercentMeasure(name + ".%", fct)
}

class CompositeMeasure[P] private (childs: List[Measure[P]])
extends Measure[P]
{
  def init(p:P, report:Report): Report = {
    def aux(acc: Report, child: Measure[P]) = child.init(p, acc)
    childs.foldLeft(report)(aux _)
  }
  def apply(p:P, report:Report): Report = {
    def aux(acc: Report, child: Measure[P]) = child(p, acc)
    childs.foldLeft(report)(aux _)
  }
}

class Measurer[-P] protected (m: Measure[P], baseReport: Report)
extends Function1[P,Report]
{
  def apply(p:P) = m(p, baseReport)
}

object Measurer {
  def apply[P](m: Measure[P], p:P) = new Measurer(m, m.init(p, Report()))
}

object DumbMeasurer extends Measurer[Any] (DumbMeasure, Report()) {}
