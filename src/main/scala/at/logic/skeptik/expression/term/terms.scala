package at.logic.skeptik.expression.term

import at.logic.skeptik.expression.{AppRec, AtomicType, E, T, Var, i, o}

/**
  * Objects to facilitate the creation of logical terms.
  *
  * @author Ezequiel Postan
  * @since 24.05.2016
  */
class Term {
  final val conditional = "conditionalTerm"
  final val ifThenElse  = new Var(conditional,o->(i->(i->i)))
  def newTerm(name : String, termType : T) = new Var(name,termType)
}

object DistinctObjectTerm extends Term {
  def apply(name : String) :E = newTerm(name,i)
}

object NumberTerm extends Term {
  def apply(number : String) :E = newTerm(number,AtomicType("$int"))
}

object Constant extends Term {
  def apply(name : String) : E = newTerm(name,i)
}

object Variable extends Term {
  def apply(name : String) : E = newTerm(name,i)
}

object FunctionTerm extends Term {
  def apply(name : String, args : List[E]) : E = {
    def createType(list : List[E]) : T = list match {
      case Nil   => i
      case e::es => e.t -> createType(es)
    }
    AppRec(newTerm(name,createType(args)),args)
  }
  def apply(name : String,typ : T , args : List[E]) : E = AppRec(newTerm(name,typ),args)
  def unapply(e:E) = e match {
    case AppRec(f,args) if e.t == i && args.nonEmpty => Some((f,args))
    case _ => None
  }
}

object TypedNumberTerm extends Term {
  def apply(number : String, numberType : String) : E = newTerm(number,new AtomicType(numberType))
}

object TypedConstant extends Term {
  def apply(name : String, constantType : T) : E = newTerm(name,constantType)
}

object TypedVariable extends Term {
  def apply(name : String, variableType : T) : E = newTerm(name,variableType)
}

object TypedFunctionSymbol extends Term {
  def apply(name : String, functionSymbolType : T) : E = newTerm(name,functionSymbolType)
}

object ConditionalTerm extends Term {
  def apply(condition : E , t1 : E, t2 : E) : E = {
    AppRec(ifThenElse,List(condition,t1,t2))
  }
}


