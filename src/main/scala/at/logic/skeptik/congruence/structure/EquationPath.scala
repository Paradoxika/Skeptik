package at.logic.skeptik.congruence.structure

import at.logic.skeptik.expression.formula._
import at.logic.skeptik.expression._
import at.logic.skeptik.proof._
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.judgment._
import at.logic.skeptik.proof.sequent.lk._
import scala.collection.mutable.{HashMap => MMap}
import at.logic.skeptik.proof.Proof.apply
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import scala.collection.mutable.{HashMap => MMap}

case class EqLabel(equation: EqW, deducePaths: Set[EquationPath]) {
  val size: Int = deducePaths.foldLeft(1)({(A,B) => 
    val add = B.pred match {
      case None => 0
      case Some(pr) => pr.label.size
    }
    A + add
  })
}

/**
 * Class EqTreeEdge represents edges in the equation path.
 * In fact this class is not much more than an abbreviation for (EquationTree,(EqW,Option[(EquationPath,EquationPath)]))(nextTree,label)
 * it just adds the functionality of accessing the equality and the optional EquationTree tuple from the label more easily
 * 
 * @param nextTree is an EquationTree, that the current object is pointing to
 * @param label for the edge, which is an instance of EqLabel
 */
case class EqTreeEdge(val nextTree: EquationPath, val label: EqLabel) {
  val eq = label.equation
  val deduceTrees = label.deducePaths
}

/**
 * Case class EquationPath representing the explanation of some equality s = t,
 * i.e. a path (u_1, ..., u_n) such that u_1 = s and u_n = t.
 * 
 * It is implemented like a singly linked list, where edges can point to other lists
 * representing the explanation for deduced equalities 
 * For example if s is App(u1,v1) and t is App(u2,v2); the path looks like this:
 * s <- [s = t] {EqP_1,EqP_2} - t <- None
 * where EqP_1 and EqP_2 are paths representing explanations of u1 = u2 and v1 = v2 resp.
 * 
 * This class is not only responsible for storing/representing explanations,
 * but also to produce proofs from them.
 * A call to the toProof method, should return a resolution proof capturing the semantics of the path
 * 
 * @param v expression in the path
 * @param pred EqTreeEdge pointing to the next element in the path or None if it's the end of an explanation
 * 
 * Not: This class was called PathTree or EquationTree once.
 * If this name pops up somewhere in the comments, this structure is meant.
 * eqReferences are used in this class just like in other classes, but it's not yet clear whether this methodology
 * should really be kept and therefore it's not commented in this class.
 */
case class EquationPath(val v: E, val pred: Option[EqTreeEdge]) {
  
  def symmetricTo(that: EquationPath) = {
    this.firstVert == that.lastVert && this.lastVert == that.firstVert
  }
  
  def isAxiom = pred match {
    case None => false
    case Some(pr) => !pr.nextTree.pred.isDefined && pr.deduceTrees.isEmpty
  }
  
  def isReflexive = pred match {
    case Some(pr) if (pr.nextTree.v == this.v)=> true
    case _ => false
  }
  
  def typeString(node: N)(implicit eqReferences: MMap[(E,E),EqW]) = {
    (node.conclusion.ant.map(EqW(_).l.t) ++ node.conclusion.suc.map(EqW(_).l.t)).mkString(",")
  }
  
  /**
   * the toProof method transforms a EquationPath into a corresponding Resolution proof.
   * To do so, it first calls its buildTransChain method.
   * The size of the returned equalities and deduced equalities differentiate three cases:
   *    Case 1: There is more than one equality (general case)
   *    ---> An instance of an Eq_Transitive Axiom is created, having all the equalities on the left side and
   *         the equality between the first and last term on the right side.
   *         Note: Initially I had a method, which only had Eq_Transitive axioms with exactly two equations on the left
   *         but as I found out that veriT uses not only these, I dropped that method and simplified to use these
   *         "chain" axioms.
   *         
   *    Case 2: There are less than 2 equalities and exactly one deduced equality (for example when proving f(a) = f(b))
   *    ---> the node of the deduced equality is simply taken (because it has the correct equality on the right side anyways)
   *         
   *    Case 3: There are less than 2 equalities and not 1 deduced equality:
   *    ---> the path corresponds either to an input axiom or the request for an explanation,
   *        where there is none. Therefore the returned proof is None
   *  
   *  
   */
  def toProof(implicit eqReferences: MMap[(E,E),EqW], reflMap: MMap[E,N]): Option[Proof[N]] = {
    val (first,last,equations,deduced) = this.buildTransChain
    if (equations.size > 1) {
      val transNode = EqTransitive(equations,first,last)
      val res = deduced.foldLeft(transNode.asInstanceOf[N])({(A,B) => 
        R(A,B)
      })
      if (res.conclusion.ant.exists(_.toString == "((f2 c_5 c_5) = (f2 c_4 c_4))")) println("creating it while making proof for " + this + "\n"+Proof(res))
      if (res.conclusion.suc.size > 1) println("size > 1 in toProof!:\n " + Proof(res))
      Some(res)
    }
    else if (deduced.size == 1) { //Case 2
      Some(deduced.last)
    }
    else { //Case 3
      if (this.isReflexive) Some(EqReflexive(this.firstVert))
      else None  
    }
  }
  
  /**
   * method buildTransChain is required for proof production.
   * It traverses the proof, gathering the equalities of the labels and 
   * calling the buildDeduction method if the optional EquationPath-tuple is set.
   * 
   * The methodology is to recursively call this method of the partial paths 
   * and overwriting the returned values accordingly
   * 
   * @return 4 tuple (u,v,EQ,DED), where
   *         u is the first expression of the path
   *         v is the last expression of the path
   *         EQ are all equations of the labels on the path
   *         DED are all results of calls to buildDeduction, 
   *             collected as a tuple of a SequentProofNode (N) and the equality if proves (as an EqW object)
   */
  def buildTransChain(implicit eqReferences: MMap[(E,E),EqW], reflMap: MMap[E,N]): (E,E,Seq[EqW],Seq[N]) = {
    if (v.toString == "(c_2 = c_3)") println(v + " occurs in trans. chain")
    pred match {
      case Some(pr) => {
        val predEq = pr.label.equation
        val predDed = pr.label.deducePaths
        val (first,last,equations,deduced) = pr.nextTree.buildTransChain
        val resFirst = v
        val resEquations = pr.label.equation +: equations
        val resDeduced = if (predDed.isEmpty) deduced else deduced :+ buildDeduction(predDed,predEq)
        (resFirst,last,resEquations,resDeduced)
      }
      case None => {
        (v,v,Seq(),Seq())
      }
    }
  }
  
  /**
   * method buildDeduction is required for proof production
   * 
   * @param dd1,dd2 are two EquationPaths representing the explanation of some terms (u1,v1) and (u2,v2)
   * @param eq is the equality that the two Paths should prove (i.e. App(u1,u2) = App(v1,v2))
   * 
   * eq can be created from dd1 and dd2, but it's passed for reference reasons.
   * Probably the parameter can be dropped eventually.
   * 
   * This method essentially does all the deduction.
   * First the two EquationPaths are transformed to proofs by calling the toProof method on them.
   * 
   * Then the correct instance of an Eq_Congruent axiom is created, 
   * by calling the correct apply method of the EqCongruent companion object.
   * Which one is the correct one depends upon the equality of the subterms.
   * If no subterm is equal to its respective counterpart, then the correct axiom is (u1 = v1, u2 = v2 |- App(u1,v1) = App(u2,v2))
   * if one of the subterms is trivially equal, then it can be dropped from the left side of this axiom
   * (which happens especially often, because function symbols of the input are viewed as treated like constants, because of currifying).
   * 
   * The proofs for the equalities of the subterms are then resolved with the Eq_Congruent axiom to obtain the final deduction proof
   * 
   * The R(x,y) calls in this method cause troubles, either because equalities happen to be equal only up to symmetry
   * or the correct pivot is not found.
   * 
   * @res a SequentProofNode representing the full proof of the input equality from input axioms only.
   **/
    
  def buildDeduction(dds: Set[EquationPath], eq: EqW) (implicit eqReferences: MMap[(E,E),EqW], reflMap: MMap[E,N]) = {
    val (refl,reflRest) = dds.partition(_.isReflexive)
    val (roots,eqs) = dds.foldLeft((Set[N](),Seq[E]()))({(A,B) => 
      val exSym = A._1.find(node => {
        val nodeEq = EqW(node.conclusion.suc.last)
        nodeEq.l == B.lastVert && nodeEq.r == B.firstVert
      })
      
      exSym match {
        case Some(node) => {
          val s = EqSymmetric(EqW(node.conclusion.suc.last))
          val r = R(s,node)
          (A._1 + r,A._2 :+ r.conclusion.suc.last)
        }
        case None => {
          B.toProof match {
            case Some(proof) => (A._1 + proof.root, A._2 :+ proof.root.conclusion.suc.last)
            case None => (A._1, A._2 :+ EqW(B.firstVert,B.lastVert).equality)
          }
        }
      }
    })
    refl.foreach(p => reflMap.update(EqW(p.v,p.v).equality, EqReflexive(p.v)))
    val congrEqs = eqs ++ refl.map(p => EqW(p.v,p.v).equality)
    val congr = EqCongruent(congrEqs,eq.equality)
    roots.foldLeft(congr.asInstanceOf[N])({(A,B) => 
      try R(A,B)
      catch {
        case e: Exception => {
          A
        }
      }
    })
  }

  /**
   * @return the equality of the next EqTreeEdge or None if there is no more edge
   */
  def eq: Option[EqW] = pred match {
    case Some(pr) => {
      Some(pr.label.equation)
    }
    case None => None
  }
  
   /**
   * @return the first vertex of the path
   */
  def firstVert = v
  
  /**
   * @return the last vertex of the path
   */
  def lastVert: E = pred match {
//    case Some(pr) => pr._1.lastVert
    case Some(pr) => pr.nextTree.lastVert
    case None => v
  }
  
  /**
   * @return predecessor of the current node in the path if present
   */
  def predPath: Option[EquationPath] = pred match {
    case Some(pr) => Some(pr.nextTree)
    case None => None
  }
  
  def isEmpty = !pred.isDefined
  
  /**
   * @return all equalities input equalities used in the whole path including deduce paths
   * 
   * Note that during proof production a node with the conclusion 
   * originalEqs |- eq
   * should occur before resolving against input axioms
   */
  
  def originalEqs: Set[EqW] = pred match {
    case Some(pr) => {
      val predOrig = pr.nextTree.originalEqs
      val extra = if (pr.label.deducePaths.isEmpty) Set(pr.eq)
      else pr.label.deducePaths.foldLeft(Set[EqW]())({(A,B) => A union B.originalEqs})
      predOrig union extra
    }
    case None => Set()
  }
  
  /**
   * @return all equalities equalities used in the path excluding deduce paths
   * 
   * Note that during proof production a node with the conclusion (if the path is longer than 1)
   * pathEqs |- firstVert = lastVert
   * should occur before resolving against deduced eqs
   */
  def pathEqs: Set[EqW] = pred match {
    case Some(pr) => {
      pr.nextTree.pathEqs + pr.label.equation
    }
    case None => {
      Set()
    }
  }
  
  /**
   * @return all original Eqs of the deduce paths of the current edge if present
   */
  def deducedEqs: Set[EqW] = pred match {
    case None => Set()
    case Some(pr) => {
      
      val x = pr.label.deducePaths.foldLeft(Set[EqW]())({(A,B) => 
        println(B + " : " + B.originalEqs)
        A union B.originalEqs})
      x
    }
  }
      
  override def toString: String = toString(false)
  
  def toString(labels: Boolean): String = {
    val pString = pred match {
      case Some(pr) => {
        
      }
      case None => ""
    }
    val predLabel = 
      if (labels) eq match {
        case Some(e) => "-["+e+"]" + "{"+pred.foreach(_.deduceTrees.mkString(";"))+"}"
        case None => ""
      }
      else ""
    val predString = predPath match {
        case Some(pT) => pT.toString(labels)
        case None => ""
      }
    "<~" + v + predLabel + predString
  }
}