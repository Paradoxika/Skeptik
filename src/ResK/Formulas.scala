package ResK

object logicalConstants {
  import ResK.expressions._
  val andS = "&"
  def andC = Var(andS, o -> (o -> o))
  
  val impS = "->"
  def impC = Var(impS, o -> (o -> o))

  val allS = "A"
  def allC(t:T) = Var(allS, (t -> o ) -> o)
  
  val exS = "E"
  def exC(t:T) = Var(exS, (t -> o ) -> o)
  
  val negS = "-"
  def negC = Var(negS, o -> o)
  
  def isLogicalConnective(c:E) = c match {
    case c: Var => {
      val n = c.name 
      if (n == andS || n == impS || n == allS || n == exS || n == negS) true else false
    }
    case _ => false
  }
}

object positions {
  import expressions._
  import formulas._
  

  
  abstract class Position {
    // returns the subformula of f at this position
    def !:(f:E):E
    
    // applies f at this position in formula
    def @:(f: E => E)(formula:E): E
    
    def isPositiveIn(formula:E): Boolean
  }
  
  type IntListPosition = List[Int] // ToDo: refactor this into a subclass of Position, if needed. Maybe it is better to try to use SubformulaP instead.
  
  class InexistentPositionException(formula: E, position: Position) extends Exception("Position " + position + " does not exist in formula " + formula)
  
  // position of the index-th occurrence of subformula
  case class SubformulaP(subformula:E, index:Int) extends Position {
    def !:(formula:E):E = {
      //ToDo
      formula
    }
    
    def @:(f: E => E)(formula:E): E = {
      var count = 0
      def rec(e: E): E = {
        if (e == subformula) count += 1
        if (e == subformula && count == index) f(e)
        else e match {
          case v: Var => v
          case App(g,a) => App(rec(g),rec(a))
          case Abs(v,g) => Abs(rec(v).asInstanceOf[Var],rec(g))
        }     
      } 
      val result = rec(formula)
      if (count >= index) result 
      else throw new InexistentPositionException(formula,this)
    }
    
    def isPositiveIn(formula: E): Boolean = {
      var count = 0 
      def rec(e:E): Option[Boolean] = {
        if (e == subformula) count += 1
        
        def propagateResult(r1:Option[Boolean],r2:Option[Boolean]) = (r1,r2) match {
          case (Some(b),None) => Some(b)
          case (None,Some(b)) => Some(b)
          case (None,None) => None
          case (Some(b1),Some(b2)) => throw new Exception("this case should never occur.")
        }
        
        if (e == subformula && count == index) Some(true)
        else e match {
          case Imp(a,b) => (rec(a),rec(b)) match {
            case (Some(b),None) => Some(!b)
            case (r1,r2) => propagateResult(r1,r2) 
          }
          case App(g,a) => propagateResult(rec(g),rec(a))
          case Abs(v,g) => propagateResult(rec(v),rec(g))
          case v: Var => None
        }
      }
      rec(formula).getOrElse(throw new InexistentPositionException(formula,this))
    }
  }
  
  
}

object formulas {
  import expressions._
  import logicalConstants._
  import positions._
  import formulaAlgorithms._

  abstract class FormulaConstructorExtractor {
    def unapply(f:E):Option[_]
    def ?:(f: E) = unapply(f).isInstanceOf[Some[Any]] 
    //def ?:(f: E) = unapply(f).isInstanceOf[Some[Any]] 
  }
  
  
  object Prop {
    def apply(name: String) = Var(name, o)
  }
  
  object Atom {
    def apply(p: E, args: List[E]) = {
      val atom = (p /: args)((p,a) => App(p,a))
      require(atom.t == o)
      atom
    }
    def unapply(e:E) = e match {
      case e: Var if e.t == o => Some((e,Nil))
      case e: App if e.t == o => {
        val r @ (p,args) = unapplyRec(e)
        if (isLogicalConnective(p)) None 
        else Some(r)
      }
      case _ => None
    }
    private def unapplyRec(e: App): (E,List[E]) = e.function match {
      case a : App => {
          val (predicate, firstArgs) = unapplyRec(a)
          return (predicate, firstArgs ::: (e.argument::Nil))
      }
      case _ => return (e.function, e.argument::Nil) 
    } 
  }
  
  object And extends FormulaConstructorExtractor {
    def apply(f1: E, f2: E) = App(App(andC,f1),f2)
    def unapply(e:E) = e match {
      case App(App(c,f1),f2) if c == andC => Some((f1,f2))
      case _ => None
    }  
  }
  
  object Imp extends FormulaConstructorExtractor {
    def apply(f1: E, f2: E) = App(App(impC,f1),f2)
    def unapply(e:E) = e match {
      case App(App(c,f1),f2) if c == impC => Some((f1,f2))
      case _ => None
    }  
  }
    
  
  object Neg {
    def apply(f: E) = App(negC,f)
    def unapply(e:E) = e match {
      case App(c,f) if c == negC => Some(f)
      case _ => None
    }  
  }
  

  abstract class Q(quantifierC:T=>E) {
    def apply(v:Var, f:E) = App(quantifierC(v.t), Abs(v,f))
    def apply(f:E, v:Var, pl:List[IntListPosition]) = {
      // ToDo: check that the terms in all positions are syntactically equal.
      val h = (f /: pl)((e,p) => deepApply(t => v.copy, e, p)) // This could be made more efficient by traversing the formula only once, instead of traversing it once for each position.
      App(quantifierC(v.t), Abs(v,h))
    }
    def apply(f:E, v:Var, t:E) = {
      val h = deepApplyAll(x => v.copy, f, t)
      App(quantifierC(v.t), Abs(v,h))
    }
    def unapply(e:E) = e match {
      case App(q, Abs(v,f)) if q == quantifierC(v.t) => Some((v,f))
      case _ => None
    }  
  }
  
  object All extends Q(allC)  
  object Ex extends Q(exC)
}

object formulaGenerator {
  import ResK.formulas._
  import ResK.expressions._
  
  //def generate(quantity: Int) = for (i <- 1 until quantity+1) yield Prop("P"+i)
  def generate(quantity: Int) = Seq("A","B","C","D","E","F","G","H","I","J","K").map(Prop(_)).take(quantity)
    
  def generate(expSeq: Seq[E], depth: Int): Seq[E] = {
    val exps = if (depth == 1) expSeq else generate(expSeq, depth - 1)
    (for (f1 <- exps.par; f2 <- exps.par) yield Imp(f1,f2)).seq
  }

  def generateAcc(expSeq: Seq[E], depth: Int): Seq[E] = {
    val exps = if (depth == 1) expSeq else generateAcc(expSeq, depth - 1)
    expSeq ++ (for (f1 <- exps.par; f2 <- exps.par) yield Imp(f1,f2)).seq
  }
  
}


object formulaAlgorithms {
  import expressions._
  import positions._
  import formulas._
  
  def deepApplyAll(f:E=>E, e:E, t:E):E = if (e == t) f(e) else e match {
    case v: Var => v.copy
    case App(g,a) => App(deepApplyAll(f,g,t),deepApplyAll(f,a,t))
    case Abs(v,g) => Abs(deepApplyAll(f,v,t).asInstanceOf[Var],deepApplyAll(f,g,t))
  }
  
  def deepApply(f:E=>E, e:E, p:IntListPosition):E = (e,p) match {
    case (e,Nil) => f(e)
    case (Atom(p,args),n::tail) => {
      val newArg = deepApply(f,args(n-1),tail)
      val newArgs = (args.dropRight(args.length-n+1):::(newArg::args.drop(n))).map(x=>x.copy)
      Atom(p.copy,newArgs)
    }
    case (And(a1,a2),1::tail) => And(deepApply(f,a1,tail),a2.copy)
    case (And(a1,a2),2::tail) => And(a1.copy,deepApply(f,a2,tail))
    case (Imp(a1,a2),1::tail) => Imp(deepApply(f,a1,tail),a2.copy)
    case (Imp(a1,a2),2::tail) => Imp(a1.copy,deepApply(f,a2,tail))
    case (All(v,q),1::Nil) => All(f(v).asInstanceOf[Var],q.copy)
    case (All(v,q),2::tail) => All(v.copy,deepApply(f,q,tail))
    case _ => throw new Exception("deepApply: provided position seems to be an invalid position in the formula")
  }
}