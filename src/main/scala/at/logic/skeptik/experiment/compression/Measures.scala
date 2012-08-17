package at.logic.skeptik.experiment.compression

import collection.mutable.{HashMap => MMap}

abstract class Measure[-P]
extends Function1[P,Double] {
  def before(proof: P):String
  def after(algorithm: String, proof: P):String
  def average(algorithm: String):String
}


class IntMeasure[-P] (unit: String, op: P => Int)
extends Measure[P] {

  var nb = 0
  var sum = MMap[String,Int]()

  def apply(proof: P) = op(proof).toDouble

  def before(proof: P) = {
    nb += 1
    op(proof).toString + unit
  }

  def after(algorithm: String, proof: P) = {
    val value = op(proof)
    sum.update(algorithm, sum.getOrElse(algorithm,0) + value)
    value.toString + unit
  }

  def average(algorithm: String) = String.format("%.1f%s", double2Double(sum(algorithm).toDouble / nb.toDouble), unit)

}

class DoubleMeasure[-P] (format: String, op: P => Double)
extends Measure[P] {

  var nb = 0
  var sum = MMap[String,Double]()

  def apply(proof: P) = op(proof)

  def before(proof: P) = {
    nb += 1
    String.format(format, double2Double(op(proof)))
  }

  def after(algorithm: String, proof: P) = {
    val value = op(proof)
    sum.update(algorithm, sum.getOrElse(algorithm,0.) + value)
    String.format(format, double2Double(value))
  }

  def average(algorithm: String) = String.format(format, double2Double(sum(algorithm) / nb.toDouble))
}

class IntPercentMeasure[-P] (op: P => Int)
extends Measure[P] {

  var beforeVal = 0
  var beforeSum:Long = 0
  val afterSum = MMap[String,Long]()

  def apply(proof: P) = op(proof).toDouble

  def before(proof: P) = {
    beforeVal = op(proof)
    beforeSum += beforeVal
    beforeVal.toString
  }

  def after(algorithm: String, proof: P) = {
    val afterVal = op(proof)
    afterSum.update(algorithm, afterSum.getOrElse(algorithm, 0.toLong) + afterVal.toLong)
    String.format("%7.3f %%", double2Double(100. * afterVal.toDouble / beforeVal.toDouble))
  }

  def average(algorithm: String) = String.format("%.3f %%", double2Double(100. * afterSum(algorithm).toDouble / beforeSum.toDouble))

}

