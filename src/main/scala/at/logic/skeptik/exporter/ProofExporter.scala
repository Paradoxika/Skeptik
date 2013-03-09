package at.logic.skeptik.exporter

import at.logic.skeptik.proof.{Proof,ProofNode}

abstract class ProofExporter[N <: ProofNode[_,N]] { 
  def write(proof:Proof[N], filename: String) : Unit
}