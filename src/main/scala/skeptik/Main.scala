package skeptik

object Main {
  def main(args: Array[String]): Unit = {
    def help() = print(usageInstructions)

    if (args.length == 0) help()
    else if (args(0) == "-experiment") {
      if (args.length == 1) help()
      else if (args(1) == "--NDc") {
        skeptik.experiment.proving.ProverExperiment.run(Array());
      }   
      else if (args(1) == "--compression") {
        skeptik.experiment.compression.Experimenter.run(args.drop(2));
      } 
      else help()
    }
    else if (args(0) == "-prove") {
      
    }
    else if (args(0) == "-compress") {
      
    }
    else help()

  }
    
  private val usageInstructions = 
  """
    
  Skeptik Usage Instructions
  ==========================
      
    -experiment    : runs pre-defined experiment
      --NDc          : contextual natural deduction experiment
      --compression  : proof compression experiment
  
    -prove         : proves theorem
  
    -compress      : compress proof
    
  """   
}
