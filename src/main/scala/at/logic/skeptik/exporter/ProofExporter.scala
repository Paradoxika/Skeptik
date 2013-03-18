package at.logic.skeptik.exporter

import at.logic.skeptik.judgment.Judgment
import at.logic.skeptik.proof.{Proof,ProofNode}

abstract class ProofExporter[N <: ProofNode[Judgment,N]] { 
  def write(proof:Proof[N], filename: String) : Unit
}