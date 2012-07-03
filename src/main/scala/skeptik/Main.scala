package skeptik

object Main {
  def main(args: Array[String]): Unit = {
    if (args(0) == "-experiment") {
      if (args(1) == "--NDc") {
        skeptik.experiment.proving.ProverExperiment.run(Array());
      }   
      else if (args(1) == "--compression") {
        skeptik.experiment.compression.Experimenter.run(args.drop(2));
      } 
    }
    else if (args(0) == "-prove") {
      
    }
    else if (args(0) == "-compress") {
      
    }
  }
}
