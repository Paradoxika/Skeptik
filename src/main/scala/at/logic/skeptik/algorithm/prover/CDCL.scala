package at.logic.skeptik.algorithm.prover

import at.logic.skeptik.algorithm.prover.choosing.{LiteralChooser, SimpleLiteralChooser}
import at.logic.skeptik.algorithm.prover.conflict.{ConflictAnalyser, SimpleConflictAnalyser}
import at.logic.skeptik.algorithm.prover.structure.immutable.Literal
import at.logic.skeptik.algorithm.prover.util.DecisionLevel

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

/**
  * @author Daniyar Itegulov
  */
object CDCL {
  def isSatisfiable(immutableCnf: CNF,
                    literalChooser: LiteralChooser = SimpleLiteralChooser,
                    conflictAnalyser: ConflictAnalyser = SimpleConflictAnalyser): Boolean = {
    val cnf = immutableCnf.toMutableCNF
    val levels = ArrayBuffer[DecisionLevel]() // Stack of decision levels
    val unitPropagationQueue = mutable.Queue.empty[Literal] // Queue of literals that should be propagated

    for (clause <- cnf.clauses) if (clause.isUnit) {
      unitPropagationQueue += clause(0) // Unit clauses should be propagated right here
    }

    /**
      * Reverts last decision level for cnf.
      */
    def undo(): Unit = {
      for (literal <- levels.last.varAssessment) {
        cnf.assignment -= literal
      }
      levels.remove(levels.size - 1)
    }

    /**
      * Ensures that provided literal is true.
      *
      * @param literal which should be true
      */
    def assignLiteral(literal: Literal): Unit = {
      levels.lastOption.foreach(_.varAssessment += literal)
      unitPropagationQueue ++= cnf.assignLiteral(literal)
    }

    /**
      * Applies unit propagation technique to elements in unitPropagationQueue.
      *
      * @return true, if there is no conflicts after propagating all unit clauses
      *         false, if there is at least one conflict
      */
    def propagate(): Boolean = {
      while (unitPropagationQueue.nonEmpty) {
        val propagationLiteral = unitPropagationQueue.dequeue()
        if (cnf.assignment contains !propagationLiteral) {
          // Found a conflict
          unitPropagationQueue.clear()
          return false
        } else {
          assignLiteral(propagationLiteral) // Ensure that unit clause literal is true
        }
      }
      true
    }

    if (!propagate()) {
      return false // If there is a conflict from the very start -> CNF is unsatisfiable
    }
    var chosen = literalChooser.chooseLiteral(cnf)
    while (true) {
      chosen = chosen match {
        case Some(literal) =>
          levels += new DecisionLevel(literal)
          assignLiteral(literal)
          if (!propagate()) { // Conflict is derived
            while (levels.last.literal.negated) { // Find first level which hasn't been processed twice
              undo()
              if (levels.isEmpty) {
                return false // All previous levels where processed twice -> CNF is unsatisfiable
              }
            }

            cnf += conflictAnalyser.learnConflictClause(levels)

            val flipLiteral = !levels.last.literal
            undo()
            levels += new DecisionLevel(flipLiteral)
            Some(flipLiteral)
          } else {
            literalChooser.chooseLiteral(cnf)
          }
        case None => return true // There is no literal which can be chose -> CNF is satisfiable
      }
    }
    true
  }
}
