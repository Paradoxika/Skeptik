package skeptik.algorithm.generator

import skeptik.expression.E
import skeptik.expression.formula.{Prop, Imp}


class FormulaGenerator {
  private val atoms = Seq("A","B","C","D","E","F","G","H","I","J","K").map(Prop(_))
  
  def generate(maxLength: Int, maxSymbols: Int) = {
    def growLists(lists: Seq[List[E]]) = {
      var grownLists = Seq[List[E]]()
      for (l <- lists) {
        val numberOfSymbolsInList = l.distinct.length
        val numberOfSymbols = if (numberOfSymbolsInList < maxSymbols) numberOfSymbolsInList + 1 else maxSymbols
        for (a <- atoms.take(numberOfSymbols)) grownLists ++= Seq((a::l))
      }
      grownLists
    }
    
    val lists = {
      def rec(i:Int):Seq[List[E]] = {
        if (i == 1) Seq(List(Prop("A")))
        else {
          val previous = rec(i-1)
          growLists(previous).toSeq
        }
      }
      rec(maxLength)
    }
    
    def generateFormulas(l:List[E]):List[E] = {
      var formulas = List[E]()
      if (l.length == 1) formulas = l
      else for (i <- 1 to l.length - 1) {
        val left = l.take(i)
        val right = l.drop(i)
        val leftFormulas = generateFormulas(left)
        val rightFormulas = generateFormulas(right)
        for (lf <- leftFormulas; rf <- rightFormulas) formulas = Imp(lf,rf)::formulas
      }
      formulas
    } 
    
    var formulas = Seq[E]()
    for (l <- lists) formulas ++= generateFormulas(l)
    
    formulas
  }
}