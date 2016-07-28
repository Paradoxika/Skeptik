package at.logic.skeptik.algorithm.FOProofsGenerator

import at.logic.skeptik.expression.{App,E,Var,i}
import at.logic.skeptik.expression.formula.Atom
import at.logic.skeptik.expression.term.FunctionTerm
import at.logic.skeptik.expression.substitution.immutable.Substitution

import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.lk.Axiom
import at.logic.skeptik.proof.sequent.{SequentProofNode => Node}
import at.logic.skeptik.proof.sequent.resolution.{Contraction, UnifyingResolution}

import collection.mutable.{HashMap => MMap ,Set => MSet}
import util.Random

/**
  * The class ProofGenerator implements methods to create
  * first order proofs.
  *
  * @param proofHeight        The height of the proof
  * @param numberOfConstants  The top limit on the number of constants in the proofs generated
  * @param numberOfPredicates The top limit on the number of predicates in the proofs generated
  * @param numberOfFunctions  The top limit on the number of functions in the proofs generated
  *
  */
class ProofGenerator(val proofHeight : Int, val numberOfConstants : Int = 5 , val numberOfPredicates : Int = 15,
                     val numberOfFunctions : Int = 3) extends ProofGeneratorTrait {


  def isEmptyClause(sequent : Sequent) : Boolean = sequent.ant.isEmpty && sequent.suc.isEmpty
  def isVariable(s : String) : Boolean = s.charAt(0).isUpper
  def anyOfTheTwo[A](a : A,b : A) = if(randomGenerator.nextBoolean()) a else b

  def printState = {
    println("Predicates: " + predicates.mkString(","))
    println("Functions: " + functions.mkString(","))
    println("Constants: " + constants.toList.map(_.toString).sorted.mkString(","))
    println("Variables: " + variables.toList.map(_.toString).sorted.mkString(","))
  }

  private val randomGenerator = new Random()

  private var varNumber  = -1
  private var consNumber = -1
  private var funcNumber = -1
  private var predNumber = -1

  def freshVar() : Var = {
    varNumber += 1
    val v = Var("V-" + varNumber,i)
    variables += v
    v
  }

  private val constants  : MSet[Var]        = MSet[Var]()
  private val variables  : MSet[Var]        = MSet[Var]()
  private val functions  : MMap[String,Int] = MMap[String,Int]()
  private val predicates : MMap[String,Int] = MMap[String,Int]()

  def getVariables() = variables.clone()

  def generateContraction(conclusion : Sequent) : Sequent = {
    def generateSubstitution(e : E) : Substitution = {
      val substitution : MMap[Var,E] = MMap[Var,E]()
      def addRepleacement(exp : E) : Unit =
        exp match {
          case FunctionTerm(_,args) => args foreach addRepleacement
          case v @ Var(name,i)  =>
            if(!isVariable(name) && !(substitution contains v))
              substitution += (v -> freshVar())
        }

      e match {
        case Atom(Var(_,_),args) => args foreach addRepleacement
      }
      Substitution(substitution.toList :_*)
    }

    if(isEmptyClause(conclusion))
      throw new IllegalArgumentException("Empty sequent as generateContraction method's parameter")

    val literals =
      if(conclusion.ant.isEmpty) conclusion.suc
      else if(conclusion.suc.isEmpty) conclusion.ant
      else anyOfTheTwo(conclusion.ant,conclusion.suc)

    val literalToExpand : E = literals(randomGenerator.nextInt(literals.size))

    val substitution = generateSubstitution(literalToExpand)

    if(literals == conclusion.ant)
      substitution(literalToExpand) +: Sequent(conclusion.ant :_*)(conclusion.suc :_*)
    else
      Sequent(conclusion.ant :_*)(conclusion.suc :_*) + substitution(literalToExpand)
  }

  private def randomFunctionArity()  : Int = {
    val aritySeed = randomGenerator.nextInt(10)
    if(0 <= aritySeed && aritySeed < 4) 1
    else if(4 <= aritySeed && aritySeed < 9) 2
    else 3
  }

  private def randomPredicateArity() : Int = {
    val aritySeed = randomGenerator.nextInt(10)
    if(0 <= aritySeed && aritySeed < 3) 1
    else if(3 <= aritySeed && aritySeed < 7) 2
    else if(7 <= aritySeed && aritySeed < 9) 3
    else 4
  }

  private def generateOneArgument() : E = {
    def isVariable(t: Int) = 0 <= t && t <= 6
    def isConstant(t: Int) = 7 <= t && t <= 8
    val argumentType: Int = randomGenerator.nextInt(10)
    if (isVariable(argumentType)) {
      val generatedVariable = freshVar()
      variables += generatedVariable
      generatedVariable
    } else if (isConstant(argumentType))
      Var("c" + randomGenerator.nextInt(numberOfConstants), i)
    else {
      val functionId = "f" + randomGenerator.nextInt(numberOfFunctions)
      if(functions contains functionId)
        FunctionTerm(functionId,generateArguments(functions(functionId)))
      else {
        functions += (functionId -> randomFunctionArity())
        FunctionTerm(functionId,generateArguments(functions(functionId)))
      }
    }
  }

  private def generateArguments(amount : Int) : List[E] = {
    require(amount >= 0)
    if (amount == 0) Nil
    else
      generateOneArgument() :: generateArguments(amount - 1)
  }


  def generateRandomLiteral() : E = {
    val predicateId : String = "p" + randomGenerator.nextInt(numberOfPredicates)
    if(predicates contains predicateId)
      Atom(predicateId,generateArguments(predicates(predicateId)))
    else {
      predicates += (predicateId -> randomPredicateArity())
      Atom(predicateId,generateArguments(predicates(predicateId)))
    }
  }

  def generateResolution(conclusion : Sequent) : (Sequent,Sequent) = {
    def devideSequent(sequent: Sequent) : (Sequent,Sequent) =
      if(isEmptyClause(conclusion))
        (Sequent()(),Sequent()())
      else {
        val antSeed : Int = if(conclusion.ant.isEmpty) 1 else conclusion.ant.size
        val sucSeed : Int = if(conclusion.suc.isEmpty) 1 else conclusion.suc.size
        val (leftAnt,rightAnt) = sequent.ant.toList.splitAt(randomGenerator.nextInt(antSeed))
        val (leftSuc,rightSuc) = sequent.suc.toList.splitAt(randomGenerator.nextInt(sucSeed))
        (Sequent(leftAnt:_*)(leftSuc:_*), Sequent(rightAnt:_*)(rightSuc:_*))
      }


    def generateSubstitution(e : E) : Substitution = {
      val substitution : MMap[Var,E] = MMap[Var,E]()
      def addRepleacement(exp : E) : Unit =
        exp match {
          case FunctionTerm(_,args) => args foreach addRepleacement
          case v @ Var(name,i)  =>
            if(!(substitution contains v) && randomGenerator.nextInt(10) < 7)
              substitution += (v -> freshVar())
        }

      e match {
        case Atom(Var(_,_),args) => args foreach addRepleacement
      }
      Substitution(substitution.toList :_*)
    }

    val (leftBaseSequent,rightBaseSequent) = devideSequent(conclusion)
    val newLiteral : E = generateRandomLiteral()
    val newLiteral2 = generateSubstitution(newLiteral)(newLiteral)

    if(randomGenerator.nextBoolean())
      if(randomGenerator.nextBoolean())
        (newLiteral +: leftBaseSequent,rightBaseSequent + newLiteral2)
      else
        (leftBaseSequent + newLiteral, newLiteral2 +: rightBaseSequent)
    else if(randomGenerator.nextBoolean())
      (newLiteral2 +: leftBaseSequent,rightBaseSequent + newLiteral)
    else
      (leftBaseSequent + newLiteral2, newLiteral +: rightBaseSequent)
  }


  def generateResolutionSharingPremise(leftParent : Sequent, rightParent : Sequent) : (Sequent,Sequent) = ???


  /**
    * The method saveSymbols explores a literal and saves the constants, predicates,
    * variables and function symbols found in the respective registers.
    *
    * @param e the literal to explore
    */
  def saveSymbols(e : E) : Unit = {
    e match {
      case Atom(Var(name,_),args) =>
        predicates += (name -> args.size)
        args foreach saveSymbols _
      case FunctionTerm(Var(name,_),args) =>
        functions  += (name -> args.size)
        args foreach saveSymbols _
      case Var(name,_) =>
        if(isVariable(name))
          variables += Var(name,i)
        else
          constants += Var(name,i)
    }
  }

  def generateProof(baseNode : Sequent) : Proof[Node] = {
    def convertNodeIntoProof(root : Node) : Proof[Node] = Proof(root)
    def resolutionStep(sequent : Sequent, height : Int) : Node = {
      val (leftSequent,rightSequent) = generateResolution(sequent)
      val leftPremise  : Node        = generatePremises(height - 1,leftSequent)
      val rightPremise : Node        = generatePremises(height - 1,rightSequent)
      UnifyingResolution.resolve(leftPremise,rightPremise,sequent,variables)
    }
    def contractionStep(sequent: Sequent, height : Int) : Node = {
      val premise : Sequent = generateContraction(sequent)
      Contraction(generatePremises(height-1,premise),sequent)(variables)
    }

    def generatePremises(height : Int ,sequent : Sequent) : Node = {
      if(isEmptyClause(sequent))
        resolutionStep(sequent,height)
      else if(height == 0)
          Axiom(sequent)
      else {
        if(randomGenerator.nextInt(100) < 95)
          resolutionStep(sequent,height)
        else
          contractionStep(sequent,height)
      }
    }
    if(!isEmptyClause(baseNode)) {
      baseNode.ant foreach saveSymbols
      baseNode.suc foreach saveSymbols
    }
    convertNodeIntoProof(generatePremises(proofHeight,baseNode))
  }
}

/**
  * The trait ProofGeneratorTrait should be use as the interface of the client to generate random proofs
  */
trait ProofGeneratorTrait {
  def generateProof(root : Sequent): Proof[Node]

  def generateProof() : Proof[Node] = generateProof(Sequent()())
}