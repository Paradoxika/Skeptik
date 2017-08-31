package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.judgment.immutable.SetSequent
import collection.mutable.{ HashMap => MMap, HashSet => MSet }

import at.logic.skeptik.proof.sequent.resolution.UnifyingResolution
import at.logic.skeptik.proof.sequent.resolution.UnifyingResolutionMRR

abstract class FORecyclePivots
extends FOAbstractRPIAlgorithm with FOCollectEdgesUsingSafeLiterals with FOUnitsCollectingBeforeFixing {

	def apply(proof: Proof[SequentProofNode]) = {
		val unifiableVars = getAllVars(proof);
		val firstPassResults = collectEdgesToDelete(proof)
				val edgesToDelete = firstPassResults._1
				val safeMap = firstPassResults._2 
				val containsFOSubs = firstPassResults._3
				if (edgesToDelete.isEmpty) {
					println("No edges to delete")
					proof
				} else {
					println("Num to delete: " + edgesToDelete.edges.size)
					val out = Proof(proof.foldDown(fixProofNodes(edgesToDelete, unifiableVars, safeMap, containsFOSubs)))
					out
				}

	}

	def apply(proof: Proof[SequentProofNode], name: String) = {
		val unifiableVars = getAllVars(proof);
		val firstPassResults = collectEdgesToDelete(proof)
				val edgesToDelete = firstPassResults._1
				val safeMap = firstPassResults._2 
								val containsFOSubs = firstPassResults._3

				if (edgesToDelete.isEmpty) {
					println("No edges to delete")
					proof
				} else {
					val out = Proof(proof.foldDown(fixProofNodes(edgesToDelete, unifiableVars, safeMap,containsFOSubs)))
							def countResolutionNodes(p: Proof[SequentProofNode]): Int = {
						var count = 0
								for (n <- p.nodes) {
									if (n.isInstanceOf[UnifyingResolution] || n.isInstanceOf[UnifyingResolutionMRR]) {
										count = count + 1
									}
								}
						count
					}
					if (out.size == proof.size && countResolutionNodes(proof) == countResolutionNodes(out)){
						scala.tools.nsc.io.File("edges.txt").appendAll("Possible case found. " + name + " \n")
					}
					out
				}

	}  

}

// Intersection trait is defined in FORPILU.scala

trait FOoutIntersection
extends FOAbstractRPIAlgorithm {

	protected def computeSafeLiterals(node: SequentProofNode,
			childrensSafeLiterals: Seq[(SequentProofNode, SetSequent)],
			edgesToDelete: FOEdgesToDelete): SetSequent =
			if (childrensSafeLiterals.length == 1)
				safeLiteralsFromChild(childrensSafeLiterals.head, node, edgesToDelete)
				else
					SetSequent()

}

trait FOconclusionSequent
extends FOAbstractRPIAlgorithm {

	protected def computeSafeLiterals(node: SequentProofNode,
			childrensSafeLiterals: Seq[(SequentProofNode, SetSequent)],
			edgesToDelete: FOEdgesToDelete): SetSequent =
			if (childrensSafeLiterals.length == 1) {
				safeLiteralsFromChild(childrensSafeLiterals.head, node, edgesToDelete)
			} else {
				node.conclusion.toSetSequent
			}

}

object FORecyclePivots
extends FORecyclePivots with FOoutIntersection

object FORecyclePivotsWithIntersection
extends FORecyclePivots with FOIntersection

object FORecyclePivotsWithConclusionSequent
extends FORecyclePivots with FOconclusionSequent
