package at.logic.skeptik.parser

import at.logic.skeptik.proof.{Proof,ProofNode}
import at.logic.skeptik.judgment.Judgment

abstract class ProofParser[N <: ProofNode[Judgment,N]] {
  def read(filename: String) : Proof[N] 
}

