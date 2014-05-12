package at.logic.skeptik.algorithm.congruence

import at.logic.skeptik.expression.formula._
import at.logic.skeptik.expression._
import at.logic.skeptik.judgment.immutable._
import at.logic.skeptik.proof._
import at.logic.skeptik.algorithm.congruence._
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.algorithm.compressor._
import at.logic.skeptik.algorithm.dijkstra._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.algorithm.compressor._
import at.logic.skeptik.exporter.Exporter
import at.logic.skeptik.exporter.skeptik.{FileExporter => SkeptikFileExporter}
import at.logic.skeptik.exporter.smt.{FileExporter => SMTFileExporter}
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}

import scala.collection.mutable.{HashMap => MMap}
import scala.collection.immutable.{HashMap => IMap}

/**
 * Object CongruenceCompressor is the actual proof compressing object
 * 
 * it gathers axioms from the whole proof and checks input derived nodes for redundant explanation
 * input derived nodes all are recursive children of the single input node in the proof file
 * to find redundant explanations for a node global axioms are used and 
 * axioms that where resolved with some recursive premise of the node are used
 * 
 * first the node is fixed, just like subsumption or other compression algorithms do
 * then for redundant fixed nodes new subproofs are generated from the EquationTree corresponding to the new explanation
 */
object CongruenceCompressor extends (Proof[N] => Proof[N]) with fixNodes {
  
  /**
   * applies the compression algorithm to a proof
   * first it calls the method buildGlobalCongruence with the proof and a newly created equality references object
   * the result is a congruence structure with all input axioms
   * 
   * in the traversal of the proof
   * it first checks its input derived status
   * then it fixes the current node
   * all equations split in right (suc) and left (ant) in the fixed node are filtered out
   * 
   * if the fixed node is input derived and there are equations on both sides 
   * it is checked whether the explanation (the left side) is redundant for some equation of the right side
   * 
   * to do that it adds the left equalities in the (immutable!) congruence structure
   * and then for all right equations it queries an EquationDijkstra object for a shorter explanation
   * 
   * shorter here means to compare the length of the explanation with the number of equations on the left 
   * and the number of axioms that were already resolved away earlier in the subproof
   * i am not 100% sure if this is the right way to compare sizes or if other things should be taken into account
   * 
   * if there is a shorter explanation it is transformed into a proof and the node is replaced with the root of this proof
   * 
   * @param proof to be compressed
   * @res hopefully shorter proof
   */
  def apply(proof: Proof[N]): Proof[N] = {
    val references = MMap[(E,E),EqW]()
    val (con,eqNodesLeft,eqNodesRight) = buildGlobalCongruence(proof,references)
    println("all references size: " + references.size)
    val premiseAxiomMap = MMap[N,Set[EqW]]()
    
    /**
     * traversal
     */
    def replaceRedundant(node: N, fromPremises: Seq[(N,Set[EqW],Boolean)]): (N,Set[EqW],Boolean) = {
      val inputDerived = 
        if (node.isInstanceOf[Axiom]) true 
        else 
          if (fromPremises.size > 0) fromPremises.map(_._3).max else false
      val premiseNodes = fromPremises.map(_._1)
      
      
      val fixedNodeInit = fixNode(node,premiseNodes)
      val premiseAxioms = premiseAxiomMap.getOrElseUpdate(fixedNodeInit, {
        val premiseAxiomsTmp = fromPremises.foldLeft(Set[EqW]())({(A,B) => A union B._2})
        if (node == fixedNodeInit) premiseAxiomsTmp
        else premiseAxiomsTmp.filter(Proof(fixedNodeInit).nodes.contains(_))
      })
      
      val rightEqs = fixedNodeInit.conclusion.suc.filter(EqW.isEq(_)).map(EqW(_))
      val leftEqs = fixedNodeInit.conclusion.ant.filter(EqW.isEq(_)).map(EqW(_))
      
      val rS = rightEqs.size
      val lS = leftEqs.size
            
      val (resNode,resAxioms) = if (rS > 0 && lS > 0 && inputDerived) {
        
        val localCon = leftEqs.foldLeft(con)({(A,B) => A.addEquality(B)})
        val localConRes = localCon.resolveDeducedQueue
        var tree: Option[EquationTree] = None
        val canBeCompressed = rightEqs.exists(eq => {
          val (l,r) = (eq.l,eq.r)
          val localConFinal = localConRes.addNode(l).addNode(r)
          val path = localConFinal.explain(l,r)
          path match {
            case Some(p) => {
              val newSize = p.originalEqs.size
              val oldSize = leftEqs.size + premiseAxioms.size
              if (newSize < oldSize) {
                tree = path
                true
              }
              else false
            }
            case None => false
          }
        })
        if (canBeCompressed) {
          
          val path = tree.get
          val pathProof = try {
            path.toProof(references)
          }
          catch {
            
            /******************************************************
             * here comes alot of debug stuff, including the exporting of the current node as a proof
             * to also have all them found by this procedure some artificial nodes are added
             * one for each used equality as a node with just that equality on the right side
             * 
             * and one with all equalities on the left side
             *****************************************************/
            
            case e: Exception => {
              val exporter = new SMTFileExporter("experiments/congruence/resolveBug11",true)
              val origEqs = path.originalEqs.toSeq //set produced bugs with EqW contain not delivering correct result
              val rightSideEq = fixedNodeInit.conclusion.suc.find(expr => if (EqW.isEq(expr)) origEqs.contains(EqW(expr)) else false)
              val res1 = rightSideEq match{
                case Some(eq) => {
//                  println(eq + " is rsEq")
                  R(new Axiom(new Sequent(origEqs.map(_.equality).toSeq,Seq())),fixedNodeInit)
                }
                case None => {
                  val leftSideEq = fixedNodeInit.conclusion.ant.find(expr => if (EqW.isEq(expr)) origEqs.contains(EqW(expr)) else false)
                  leftSideEq match{
                    case Some(eq) => {
//                      println(eq + " is lsEq")
                      R(new Axiom(new Sequent(Seq(),origEqs.map(_.equality).toSeq)),fixedNodeInit)
                    }
                    case None => {
//                      fixedNodeInit.conclusion.ant.foreach(p => {
//                        println(p + " contained in map? " + origEqs.contains(EqW(p)))
//                      })
                      println(origEqs.mkString(","))
                      val c7c3_1 = origEqs.find(_.toString == "(c7 = c_3)").get
                      val c7c3_2 = EqW(fixedNodeInit.conclusion.ant.find(_.toString == "(c7 = c_3)").get)
                      println(c7c3_1 + " == " + c7c3_2 + " ~> " + (c7c3_1 == c7c3_2))
                      fixedNodeInit.conclusion.ant.map(EqW(_)).foreach(p => {
                        println(p + " contained in map? " + origEqs.contains(p))
                      })
//                      println(last + " contained in\n " + origEqs.mkString(",") + "\n" +last)
                      throw new Exception("fixedNode empty?\n" + fixedNodeInit)
                    }
                  }
                }
              }
              val res2 = origEqs.foldLeft(res1)({(A,B) =>
                val ax = new Axiom(new Sequent(Seq(),Seq(B.equality)))
                if (A.conclusion.ant.contains(B)) R(A,ax)
                else A
//                try R(A,ax)
//                catch {
//                  case e: Exception => {
//                    A
//                  }
//                }
              })
              exporter.write(Proof(res2.asInstanceOf[N]))            
              
              exporter.flush
              exporter.close
              throw(e)
            }
          }
          
          /******************************************************
           * here the actual replacement is done
           * if a node is in fact replaced it is also resolved with all the which it can be resolved with
           *****************************************************/
          
          val usedEqs = path.originalEqs
          pathProof match  {
            case Some(proof) => {
              if (usedEqs.size > fixedNodeInit.conclusion.ant.size) {
              }
              val (resNode, resAxioms) = usedEqs.foldLeft((proof.root,Set[EqW]()))({(A,B) => 
                eqNodesRight.get(B) match {
                  case Some(node) => (R(A._1,node), A._2 + EqW(node.conclusion.suc.last))
                  case None => A
                }
              })
              println("after  " + resNode)
              if (resNode.conclusion.ant.size > fixedNodeInit.conclusion.ant.size) println("compressing, but clause got bigger")
              (resNode,resAxioms)
            }
            case _ => (fixedNodeInit,premiseAxioms)
          }
        }
        else (fixedNodeInit,premiseAxioms)
      }
      else {
        if (rS == 1 && lS == 0) {
          (fixedNodeInit,premiseAxioms + rightEqs.last)
        }
        else (fixedNodeInit,premiseAxioms)
      }
      (resNode,resAxioms,inputDerived)
    }
    val (newProof, _,_) = proof foldDown replaceRedundant
    val resProof = newProof.conclusion.suc.foldLeft(newProof)({(A,B) => 
      eqNodesLeft.get(EqW(B)) match {
        case Some(node) => {
          R(A,node)
        }
        case None => {
          println("no equality for " + B)
          A
        }
      }
    })

    DAGify(resProof)
  }
  
  /**
   * gathers all the input equality and inequality axioms (i.e. single equalities on the right and left respectively)
   * adds input equalities to a newly created congruence structure
   * 
   * input (in)equalities are only those for which 
   * no node with a single equality on the right (left) was used to derive this node
   * 
   * @param proof to gather equalities and create congruence structure for
   * @param references equality reference map
   * 
   * @res triple: -congruence structure with input equalities added
   *              -map from EqW objects representing input equalities to the respective proof nodes
   *              -map from EqW objects representing input inequalities to the respective proof nodes
   */
  def buildGlobalCongruence(proof: Proof[N], references: MMap[(E,E),EqW]): (Congruence,MMap[EqW,N],MMap[EqW,N]) = {
    var con = new Congruence(references)
    val eqNodesLeft = MMap[EqW,N]()
    val eqNodesRight = MMap[EqW,N]()
    
    
    
    def traverse(node: N, fromPremises: Seq[(Boolean,Boolean,IMap[(E,E),EqW])]): (Boolean,Boolean,IMap[(E,E),EqW]) = {
      
      val premiseMap = 
        if (fromPremises.isEmpty) IMap[(E,E),EqW]()
        else {
          val maps = fromPremises.map(_._3)
          maps.tail.foldLeft(maps.head)({(A,B) => 
            A ++ B
          })
        }
      
      val rightEqs = node.conclusion.suc.filter(EqW.isEq(_)).map(EqW(_))
      val leftEqs = node.conclusion.ant.filter(EqW.isEq(_)).map(EqW(_))
      
      val bothEqs = rightEqs ++ leftEqs
      bothEqs.foreach(eq => {
        val (l,r) = (eq.l,eq.r)
        references += ((l,r) -> eq)
//        references += ((r,l) -> eq)
      })
      val eqMap = bothEqs.foldLeft(premiseMap)({(A,B) => 
        A.updated((B.l,B.r), B)
      })
      
      val freshLeft = if (fromPremises.size > 0) fromPremises.map(_._1).min else true
      val freshRight = if (fromPremises.size > 0) fromPremises.map(_._2).min else true
      val freshLeftOut = if(true) {
        val singleLeft = node.conclusion.suc.size == 0 && node.conclusion.ant.size == 1 && node.conclusion.ant.forall(EqW.isEq(_))
        if (singleLeft) {
          val eq = EqW(node.conclusion.ant.last)
          eqNodesLeft += (eq -> node)
          false
        }
        else true
      }
      else false
      val freshRightOut = if (freshRight) {
        val singleRight = node.conclusion.suc.size == 1 && node.conclusion.ant.size == 0 && node.conclusion.suc.forall(EqW.isEq(_))
        if (singleRight) {
          val eq = EqW(node.conclusion.suc.last)
          con = con.addEquality(eq)
          eqNodesRight += (eq -> node)
          false
        }
        else true
      }
      else false
      (freshLeftOut,freshRightOut,eqMap)
    }
    val (_,_,mapRes) = proof foldDown traverse
    con = con.resolveDeducedQueue
    println("eqNodesLeft in bGC " + eqNodesLeft.mkString(","))
    (con,eqNodesLeft,eqNodesRight)
  }
}