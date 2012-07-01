package skeptik

object Main {
  def main(args: Array[String]): Unit = {
    import skeptik.judgment.mutable._
    import skeptik.expression.E
    import skeptik.expression.formula.Prop
    import collection.mutable.{Set => MSet}
    val a = new Sequent(MSet(Prop("a").asInstanceOf[E]), MSet(Prop("b").asInstanceOf[E]))
    
    skeptik.experiment.proving.ProverExperiment.main(Array());
  }
}
