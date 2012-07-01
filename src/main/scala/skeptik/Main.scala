package skeptik

object Main {
  def main(args: Array[String]): Unit = {
    import skeptik.judgment.mutable._
    import skeptik.expression.E
    import skeptik.expression.formula.Prop
    import collection.mutable.{Set => MSet}
    val a = new SetSequent(MSet(Prop("a")), MSet(Prop("b")))
    println(a)
    a += Prop("c")
    println(a)
    Prop("d") =+: a
    println(a)
    a += Left(Prop("e"))
    println(a)
    a += Right(Prop("f"))
    println(a)
    
    skeptik.experiment.proving.ProverExperiment.main(Array());
  }
}
