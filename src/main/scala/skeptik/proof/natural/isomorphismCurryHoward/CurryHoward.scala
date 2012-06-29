package skeptik.proof.natural
package isomorphismCurryHoward

import skeptik.expression._
import skeptik.expression.formula.{Prop, Imp}
import skeptik.judgment.{NamedE, NaturalSequent}

object CurryHoward {
  def formulaToType(formula: E): T = formula match {
    case Prop(n) => AtomicType(n)
    case Imp(a,b) => Arrow(formulaToType(a),formulaToType(b))
  }

  def typeToFormula(t: T): E = t match {
    case AtomicType(n) => Prop(n) 
    case Arrow(a,b) => Imp(typeToFormula(a),typeToFormula(b))
  }
  
  private def namedEToVar(namedE: NamedE) = Var(namedE.name, formulaToType(namedE.expression))
  
  private def varToNamedE(v: Var) = NamedE(v.name, typeToFormula(v.t))
  
  def apply(p: NaturalDeductionProof): E = p match {
    case a: Assumption => namedEToVar(a.a)
    case ImpIntro(premise, namedE) => Abs(namedEToVar(namedE),apply(premise))
    case ImpElim(leftPremise, rightPremise) => App(apply(rightPremise), apply(leftPremise))
  }

  
  def apply(term: E): NaturalDeductionProof = term match {
    case v: Var => {
      val n = varToNamedE(v)
      new Assumption(Set(n),n) 
    }
    case Abs(v, e) => ImpIntro(apply(e), varToNamedE(v))
    case App(f, a) => ImpElim(apply(a), apply(f))
  }
}