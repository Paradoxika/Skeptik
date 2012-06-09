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
  import scala.collection.mutable.{HashMap => MMap}
  

  
  abstract class Position {
    // returns the subformula of f at this position
    def !:(f:E):E
    
    // applies f at this position in formula
    def @:(f: E => E)(formula: E): E
    
    def isPositiveIn(formula: E): Boolean
    
    def getSubpositions(formula: E) : Seq[Position]
  }
  
  type IntListPosition = List[Int] // ToDo: refactor this into a subclass of Position, if needed. Maybe it is better to try to use SubformulaP instead.
  
  class InexistentPositionException(formula: E, position: Position) extends Exception("Position " + position + " does not exist in formula " + formula)
  
  class EmptyP() extends IntListP(Nil)
  
  class SubformulaP(subformula: E, override val index: Int) extends PredicateP(_ == subformula, index)
  
  
  // position of the index-th occurrence of subformula
  case class IntListP(list: List[Int]) extends Position {
    def !:(formula:E):E = {
      (list, formula) match {
        case (0::t,Imp(a,b)) => b !: IntListP(t)
        case (1::t,Imp(a,b)) => a !: IntListP(t)
        case (Nil,f) => f
        case _ => throw new InexistentPositionException(formula,this)
      }
    }  
    
    def getSubpositions(formula: E) : Seq[IntListP] = {  
      def rec(e: E):Seq[List[Int]] = e match {
        case v @ Prop(name) => Seq(Nil)
        case i @ Imp(a,b) => Seq(Nil) ++ rec(a).map(1::_) ++ rec(b).map(0::_)
      }
      rec(formula).map(l => IntListP(this.list ::: l))
    }
    
    def @:(f: E => E)(formula:E): E = {
      def rec(e: E, l: List[Int]): E = (e,l) match {
          case (_,Nil) => f(e) 
          case (Imp(a,b),0::t) => Imp(a,rec(b,t))
          case (Imp(a,b),1::t) => Imp(rec(a,t),b)
          case _ => throw new InexistentPositionException(formula,this)
      }     
      rec(formula, this.list)
    }
    
    def existsIn(formula: E): Boolean = {
      try {
        formula !: this
        true
      } catch {
        case e: InexistentPositionException => false
      }
    }
    
    def isPositiveIn(formula: E): Boolean = {
      (list, formula) match {
        case (0::t,Imp(a,b)) => IntListP(t) isPositiveIn b
        case (1::t,Imp(a,b)) => ! (IntListP(t) isPositiveIn a)
        case (Nil,f) => true
        case _ => throw new InexistentPositionException(formula,this)
      }
    }
  }
  
  
  // position of the index-th occurrence of subformula
  case class PredicateP(isSearchedSubformula: E => Boolean, index: Int) extends Position {
    def !:(formula:E):E = {
      var count = 0
      def rec(e: E): Option[E] = {
        def propagateResult[A](r1:Option[A],r2:Option[A]) = (r1,r2) match {
          case (Some(b),None) => Some(b)
          case (None,Some(b)) => Some(b)
          case (None,None) => None
          case (Some(b1),Some(b2)) => throw new Exception("this case should never occur.")
        }
        if (isSearchedSubformula(e)) count += 1
        if (isSearchedSubformula(e) && count == index) Some(e)
        else e match {
          case v: Var => None
          case App(g,a) => propagateResult(rec(g),rec(a))
          case Abs(v,g) => propagateResult(rec(v),rec(g))
        }
      } 
      rec(formula).getOrElse(throw new InexistentPositionException(formula,this))
    }
    
    
    // I think this is buggy.
    def getSubpositions(formula: E) : Seq[PredicateP] = {
      val counter = new MMap[E,Int]
      def getPositionOf(e:E) = {
        counter.update(e, counter.getOrElse(e,0)+1)
        PredicateP(_ == e, counter(e))
      }      
      def rec(e: E):Seq[PredicateP] = e match {
        case v @ Prop(name) => Seq(getPositionOf(v))
        case i @ Imp(a,b) => Seq(getPositionOf(i)) ++ rec(a) ++ rec(b)
      }
      rec(formula)
    }
    
    def @:(f: E => E)(formula:E): E = {
      var count = 0
      def rec(e: E): E = {
        if (isSearchedSubformula(e)) count += 1
        if (isSearchedSubformula(e) && count == index) f(e)
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
    
    def existsIn(formula: E): Boolean = {
      try {
        formula !: this
        true
      } catch {
        case e: InexistentPositionException => false
      }
    }
    
    def isPositiveIn(formula: E): Boolean = {
      var count = 0 
      def rec(e:E): Option[Boolean] = {
        if (isSearchedSubformula(e)) count += 1
        
        def propagateResult(r1:Option[Boolean],r2:Option[Boolean]) = (r1,r2) match {
          case (Some(b),None) => Some(b)
          case (None,Some(b)) => Some(b)
          case (None,None) => None
          case (Some(b1),Some(b2)) => throw new Exception("this case should never occur.")
        }
        
        if (isSearchedSubformula(e) && count == index) Some(true)
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
    def ?:(f: E) = unapply(f).isInstanceOf[Some[_]]
  }
  
  
  object Prop {
    def apply(name: String) = Var(name, o)
    def unapply(e: E) = e match {
      case Var(name,t) if t == o => Some(name)
      case _ => None
    }
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
  
  def generate2(depth: Int, vars: Int):Seq[E] = {
    //import scala.collection.mutable.{HashSet => MSet}
    class Tree
    case class L() extends Tree
    case class N(l:Tree,r:Tree) extends Tree 
    
    println("hi!")
    
    var trees : Seq[Tree] = Seq()
    def generateTrees(d: Int):Unit = {
      //println(d)
      //println(trees)
      if (d == 0) {
        trees = L() +: trees
        //println("trees: " + trees)
      }
      else {
        generateTrees(d-1)
        val treesAux : Seq[Tree] = Seq() ++ trees
        for (t1 <- treesAux; t2 <- treesAux) {
          trees = N(t1,t2) +: trees
          //println(trees)
        }
      }
    }
    
    def mapTreeToExpressions(tree:Tree): Seq[E] = {
      //println(tree)
      val atoms = generate(vars)
      var counter = 0
      def getAtoms() = {
        counter += 1
        atoms.take(counter)    
      }
      
      def rec(t:Tree): Seq[E] = t match {
        case L() => getAtoms()
        case N(t1,t2) => for (e1 <- rec(t1); e2 <- rec(t2)) yield Imp(e1,e2)
      }
      val exps = rec(tree)
      println(exps)
      exps
    }
    
    println("hi2")
    generateTrees(depth)
    println("hi3")
    //println(trees)
    trees.map(mapTreeToExpressions).toSeq.flatten
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