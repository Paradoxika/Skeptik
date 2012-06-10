package skeptik.proof.sequent
package resolution

import scala.collection.mutable.{HashMap => MMap}
import skeptik.judgment.Sequent
import skeptik.expression.{Var,E}
import skeptik.expression.formula.formulaAlgorithms._
import skeptik.algorithm.unifier._


class R(val leftPremise:SequentProof, val rightPremise:SequentProof,
          val auxL:E, val auxR:E)(implicit unifiableVariables: Set[Var])
extends SequentProof("R", leftPremise::rightPremise::Nil,
                      Map(leftPremise -> Sequent(Nil,auxL),
                          rightPremise -> Sequent(auxR,Nil)))
with NoMainFormula {
  //implicit val uV = unifiableVariables 
  val unifier = unify((auxL,auxR)::Nil) match {
    case None => throw new Exception("Resolution: given premise clauses are not resolvable.")
    case Some(u) => u
  }
  private val ancestryMap = new MMap[(E,SequentProof),Sequent]
  override val conclusionContext = {
    def descendant(e:E, p:SequentProof, anc: Sequent) = {val eS = (e/unifier); ancestryMap += ((eS,p) -> anc); eS }
    val antecedent = leftPremise.conclusion.ant.map(e=>descendant(e,leftPremise,Sequent(e,Nil))) ++
                    (rightPremise.conclusion.ant.filter(_ != auxR)).map(e=>descendant(e,rightPremise,Sequent(e,Nil)))
    val succedent = (leftPremise.conclusion.suc.filter(_ != auxL)).map(e=>descendant(e,leftPremise,Sequent(Nil,e))) ++
                    rightPremise.conclusion.suc.map(e=>descendant(e,rightPremise,Sequent(Nil,e)))
    Sequent(antecedent,succedent)
  }
  override def contextAncestry(f:E,premise:SequentProof) = {
    require(conclusion contains f)
    require(premises contains premise)
    ancestryMap.getOrElse((f,premise),Sequent())
  }
}


object R {
  def apply(leftPremise:SequentProof, rightPremise:SequentProof, auxL:E, auxR:E)(implicit unifiableVariables:Set[Var]) = new R(leftPremise, rightPremise, auxL, auxR)// unifiableVariables)
  def apply(leftPremise:SequentProof, rightPremise:SequentProof, findL:E=>Boolean, findR:E=>Boolean)(implicit unifiableVariables:Set[Var]) = {
    new R(leftPremise, rightPremise,
          leftPremise.conclusion.suc.find(findL).get,  //ToDo: Catch Exception
          rightPremise.conclusion.ant.find(findR).get) //ToDo: Catch Exception
  }
  def apply(leftPremise:SequentProof, rightPremise:SequentProof)(implicit unifiableVariables:Set[Var]) = {
    def isUnifiable(p:(E,E)) = unify(p::Nil)(unifiableVariables) match {
        case None => false
        case Some(_) => true
      }
    val unifiablePairs = (for (auxL <- leftPremise.conclusion.suc; auxR <- rightPremise.conclusion.ant) yield (auxL,auxR)).filter(isUnifiable)
    if (unifiablePairs.length > 0) {
      val (auxL,auxR) = unifiablePairs(0)
      new R(leftPremise, rightPremise, auxL, auxR)
    }
    else if (unifiablePairs.length == 0) throw new Exception("Resolution: the conclusions of the given premises are not resolvable.")
    else throw new Exception("Resolution: the resolvent is ambiguous.") // ToDo
  }
  def unapply(p:SequentProof) = p match {
    case p: R => Some((p.leftPremise,p.rightPremise,p.auxL,p.auxR))
    case _ => None
  }
}
