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
  *
  */
class ProofGenerator(val proofHeight : Int) extends ProofGeneratorTrait {


  var numberOfPredicates: Int = proofHeight * 2
  val numberOfConstants: Int  = numberOfPredicates * 3
  val numberOfFunctions: Int  = numberOfPredicates

  def isEmptyClause(sequent: Sequent): Boolean = sequent.ant.isEmpty && sequent.suc.isEmpty

  def isVariable(s: String): Boolean = s.charAt(0).isUpper

  def anyOfTheTwo[A](a: A, b: A) = if (randomGenerator.nextBoolean()) a else b

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

  def resetState(): Unit = {
    numberOfPredicates = proofHeight * 2
    varNumber  = -1
    consNumber = -1
    funcNumber = -1
    predNumber = -1
    constants.clear()
    functions.clear()
    predicates.clear()
    variables.clear()
    sequentIndex = 0
    sequentsOfSizeOne.clear()
  }


  def freshVar(): Var = {
    varNumber += 1
    val v = Var("V" + varNumber, i)
    variables += v
    v
  }

  private val constants: MSet[Var] = MSet[Var]()
  private val variables: MSet[Var] = MSet[Var]()
  private val functions: MMap[String, Int] = MMap[String, Int]()
  private val predicates: MMap[String, Int] = MMap[String, Int]()

  private var varCopy = variables.clone()
  def getVariables() = varCopy.clone()

  def generateContraction(conclusion: Sequent): Sequent = {
    def generateSubstitutionForContraction(e: E): Substitution = {
      val substitution: MMap[Var, E] = MMap[Var, E]()
      def addRepleacement(exp: E): Unit =
        exp match {
          case FunctionTerm(_, args) => args foreach addRepleacement
          case v@Var(name, i)        =>
            if (!(substitution contains v))
              substitution += (v -> freshVar())
        }

      e match {
        case Atom(Var(_, _), args) => args foreach addRepleacement
      }
      Substitution(substitution.toList: _*)
    }

    if (isEmptyClause(conclusion))
      throw new IllegalArgumentException("Empty sequent as generateContraction method's parameter")

    val literals =
      if (conclusion.ant.isEmpty) conclusion.suc
      else if (conclusion.suc.isEmpty) conclusion.ant
      else anyOfTheTwo(conclusion.ant, conclusion.suc)

    val literalToExpand: E = literals(randomGenerator.nextInt(literals.size))

    val substitution = generateSubstitutionForContraction(literalToExpand)

    if (literals == conclusion.ant)
      substitution(literalToExpand) +: Sequent(conclusion.ant: _*)(conclusion.suc: _*)
    else
      Sequent(conclusion.ant: _*)(conclusion.suc: _*) + substitution(literalToExpand)
  }

  private def randomFunctionArity() : Int = {
    val aritySeed = randomGenerator.nextInt(10)
    if (0 <= aritySeed && aritySeed < 4) 1
    else if (4 <= aritySeed && aritySeed < 9) 2
    else 3
  }

  private def randomPredicateArity() : Int = {
    val aritySeed = randomGenerator.nextInt(10)
    if (0 <= aritySeed && aritySeed < 3) 1
    else if (3 <= aritySeed && aritySeed < 7) 2
    else if (7 <= aritySeed && aritySeed < 9) 3
    else 4
  }

  private def generateOneArgument() : E = {
    def isAVariable(t: Int) = false //0 <= t && t < 0
    def isAConstant(t: Int) = 0 <= t && t <= 7
    val argumentType: Int = randomGenerator.nextInt(10)
    if (isAVariable(argumentType)) {
      val generatedVariable = freshVar()
      variables += generatedVariable
      generatedVariable
    } else if (isAConstant(argumentType))
      Var("c" + randomGenerator.nextInt(numberOfConstants), i)
    else {
      val functionId = "f" + randomGenerator.nextInt(numberOfFunctions)
      if (functions contains functionId)
        FunctionTerm(functionId, generateArguments(functions(functionId)))
      else {
        functions += (functionId -> randomFunctionArity())
        FunctionTerm(functionId, generateArguments(functions(functionId)))
      }
    }
  }

  private def generateArguments(amount: Int) : List[E] = {
    require(amount >= 0)
    if (amount == 0) Nil
    else
      generateOneArgument() :: generateArguments(amount - 1)
  }


  def generateRandomLiteral(): E = {
    val predicateId: String = "p" + randomGenerator.nextInt(numberOfPredicates)
    if (predicates contains predicateId)
      Atom(predicateId, generateArguments(predicates(predicateId)))
    else {
      predicates += (predicateId -> randomPredicateArity())
      Atom(predicateId, generateArguments(predicates(predicateId)))
    }
  }


  private def generateSubstitution(e: E) : Substitution = {
    val substitution: MMap[Var, E] = MMap[Var, E]()
    def addRepleacement(exp: E): Unit =
      exp match {
        case FunctionTerm(_, args) => args foreach addRepleacement
        case v@Var(name, i) =>
          if (!(substitution contains v) && randomGenerator.nextInt(10) < 7)
            substitution += (v -> freshVar())
      }

    e match {
      case Atom(Var(_, _), args) => args foreach addRepleacement
    }
    Substitution(substitution.toList: _*)
  }

  def generateResolution(conclusion: Sequent) : (Sequent, Sequent) = {
    def generateSubstitutionForEmpryCase(e: E): Substitution = {
      val substitution: MMap[Var, E] = MMap[Var, E]()
      def addRepleacement(exp: E): Unit =
        exp match {
          case FunctionTerm(_, args) => args foreach addRepleacement
          case v@Var(name, i) =>
            if (!(substitution contains v) && randomGenerator.nextInt(10) < 1)
              substitution += (v -> freshVar())
        }

      e match {
        case Atom(Var(_, _), args) => args foreach addRepleacement
      }
      Substitution(substitution.toList: _*)
    }


    def devideSequent(sequent: Sequent) : (Sequent, Sequent) =
      if (isEmptyClause(sequent))
        (Sequent()(), Sequent()())
      else {
        val antSeed: Int = if (sequent.ant.isEmpty) 1 else sequent.ant.size / 2
        val sucSeed: Int = if (sequent.suc.isEmpty) 1 else sequent.suc.size / 2
        val (leftAnt, rightAnt) = sequent.ant.toList.splitAt(antSeed)//randomGenerator.nextInt(antSeed))
        val (leftSuc, rightSuc) = sequent.suc.toList.splitAt(sucSeed)//randomGenerator.nextInt(sucSeed))
        (Sequent(leftAnt: _*)(leftSuc: _*), Sequent(rightAnt: _*)(rightSuc: _*))
      }

    def newPredicateName(arity : Int) : String = {
      numberOfPredicates += 1
      val name = "p" + numberOfPredicates
      if (predicates contains name)
        newPredicateName(arity)
      predicates += name -> arity
      name
    }
    def getInverseSubstitution(sequent : Sequent) : Substitution = {
      def isConstant(name : String) : Boolean = name.charAt(0).isLower || name.charAt(0).isDigit
      def isVari1able(name : String) : Boolean = name.charAt(0).isUpper
      val maxSize      = 1 + randomGenerator.nextInt(2)
      var currentSize  = 0
      val substitution = MMap[Var,E]()
      def addRepleacement(exp: E): Unit =
        if(currentSize <= maxSize) {
          currentSize += 1
          exp match {
            case FunctionTerm(_, args) => args foreach addRepleacement
            case v@Var(name, i) =>
              if (!(substitution contains v) && isConstant(name) && randomGenerator.nextInt(100) < 80)
                substitution += (v -> freshVar())
              if (!(substitution contains v) && isVariable(name))
                substitution += (v -> v)
          }
        }

      def exploreLiteral(exp : E) : Unit =
        exp match {
          case Atom(Var(_, _), args) => args foreach addRepleacement
        }

      sequent.ant foreach exploreLiteral
      sequent.suc foreach exploreLiteral

      Substitution(substitution.toList : _*)
    }

    def generateLiteral(leftSequent : Sequent, rightSequent : Sequent) : (Sequent,E,Sequent,E) =
      if(isEmptyClause(leftSequent) && isEmptyClause(rightSequent)) {
        val literal = generateRandomLiteral()
        (leftSequent,literal,rightSequent,generateSubstitutionForEmpryCase(literal)(literal))
      } else {
        val sub1 = getInverseSubstitution(leftSequent)
        val sub2 = getInverseSubstitution(rightSequent)
        val (e2, v1) = sub1.toList.unzip
        val (e1, v2) = sub2.toList.unzip
        val arg1 = v1 ++ e1
        val arg2 = e2 ++ v2
        require(arg1.size == arg2.size)
        if(arg1.isEmpty) {
          val literal = generateRandomLiteral()
          (leftSequent,literal,rightSequent,generateSubstitutionForEmpryCase(literal)(literal))
        } else {
          val literalName: String = newPredicateName(arg1.size)
          val newLeftSeq = Sequent(leftSequent.ant map { x => sub1(x) }: _*)(leftSequent.suc map { x => sub1(x) }: _*)
          val newRightSeq = Sequent(rightSequent.ant map { x => sub2(x) }: _*)(rightSequent.suc map { x => sub2(x) }: _*)
          (newLeftSeq, Atom(literalName, arg1), newRightSeq, Atom(literalName, arg2))
        }
      }


    val (leftBaseSequent, rightBaseSequent) = devideSequent(conclusion)
    val (newLeftSeq,leftResolvedLiteral,newRightSeq,rightResolvedLiteral) : (Sequent,E,Sequent,E) = generateLiteral(leftBaseSequent,rightBaseSequent)

    if (randomGenerator.nextBoolean())
      (leftResolvedLiteral +: newLeftSeq, newRightSeq + rightResolvedLiteral)
    else
      (newLeftSeq + leftResolvedLiteral, rightResolvedLiteral +: newRightSeq)
  }

  private var sequentIndex      = 0
  private val sequentsOfSizeOne = MMap[Int, Sequent]()
  private def addToUnitSequents(sequent : Sequent): Unit = {
    sequentsOfSizeOne += (sequentIndex -> sequent)
    sequentIndex += 1
  }
  private def getUnitSequent() : Sequent = {
    if(randomGenerator.nextInt(100) < 10)
      sequentsOfSizeOne(randomGenerator.nextInt(sequentIndex))
    else
      if (randomGenerator.nextBoolean()) {
        val s = Sequent(generateRandomLiteral())()
        addToUnitSequents(s)
        s
      } else {
        val s = Sequent()(generateRandomLiteral())
        addToUnitSequents(s)
        s
      }
  }

  def generateResolutionSharingPremise(leftParent : Sequent, rightParent : Sequent) : (Sequent,Sequent,Sequent) = {
    def getSequentAndLiterals() : (E,Sequent,E) = {
      val newSequent : Sequent = getUnitSequent()
      require(newSequent.ant.size + newSequent.suc.size == 1)
      val newLiteral1 : E = if(newSequent.ant.isEmpty) newSequent.suc.head else newSequent.ant.head
      val newLiteral2 : E = generateSubstitution(newLiteral1)(newLiteral1)
      val newLiteral3 : E = generateSubstitution(newLiteral1)(newLiteral1)

      (newLiteral2,newSequent,newLiteral3)
    }

    val (leftLiteral,centralSequent,rightLiteral) = getSequentAndLiterals()

    if(centralSequent.ant.isEmpty)
      (leftLiteral +: leftParent, centralSequent, rightLiteral +: rightParent)
    else
      (leftParent + leftLiteral, centralSequent, rightParent + rightLiteral)
  }


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

  private def heightReduction() : Int = 1 + randomGenerator.nextInt(1)

  def generateProof(baseNode : Sequent) : Proof[Node] = {
    def convertNodeIntoProof(root : Node) : Proof[Node] = Proof(root)
    def resolutionStep(sequent : Sequent, height : Int) : Node = {
      val (leftSequent,rightSequent) = generateResolution(sequent)
      val leftPremise  : Node        = generatePremises(height - heightReduction(),leftSequent)
      val rightPremise : Node        = generatePremises(height - heightReduction(),rightSequent)
      UnifyingResolution.resolve(leftPremise,rightPremise,sequent,variables)
    }
    def contractionStep(sequent: Sequent, height : Int) : Node = {
      val premise : Sequent = generateContraction(sequent)
      Contraction(generatePremises(height - heightReduction(),premise),sequent)(variables)
    }

    def irregularResolutionStep(sequent: Sequent, height : Int) : Node = {
      val (left,right) = generateResolution(sequent)
      val (leftGrand,common,rightGrand) = generateResolutionSharingPremise(left,right)
      val commonNode     : Node = generatePremises(height - heightReduction(),common)
      val leftGrandNode  : Node = generatePremises(height - heightReduction(),leftGrand)
      val rightGrandNode : Node = generatePremises(height - heightReduction(),rightGrand)
      val leftPremise    : Node = UnifyingResolution.resolve(leftGrandNode,commonNode,left,variables)
      val rightPremise   : Node = UnifyingResolution.resolve(commonNode,rightGrandNode,right,variables)
      UnifyingResolution.resolve(leftPremise,rightPremise,sequent,variables)
    }

    def generatePremises(height : Int ,sequent : Sequent) : Node = {
      if(sequent.ant.size + sequent.suc.size == 1)
        addToUnitSequents(sequent)

      if(isEmptyClause(sequent))
        resolutionStep(sequent,height)
      else if(height <= 0)
          Axiom(sequent)
      else {
        if(randomGenerator.nextInt(100) < 90)
          if(randomGenerator.nextInt(100) < 80)
            resolutionStep(sequent,height)
          else
            irregularResolutionStep(sequent,height)
        else
          contractionStep(sequent,height)
      }
    }

    if(!isEmptyClause(baseNode)) {
      baseNode.ant foreach saveSymbols
      baseNode.suc foreach saveSymbols
    }
    val p = convertNodeIntoProof(generatePremises(proofHeight,baseNode))
    varCopy = variables.clone()
    resetState()
    p
  }

  def generateFolder(destinationPath : String = "" , numberOfProofs : Int, rootSequent : Sequent) : Unit = {
    def generateProofWrapper(node : Sequent) : Proof[Node] =
      try {
        generateProof(node)
      } catch {
        case e : Exception =>
          resetState()
          generateProofWrapper(node)
      }

    import java.nio.file._

    try {
      val directoryName = "GeneratedProofs"
      val path : Path   = Paths.get(destinationPath, directoryName)
      Files.createDirectory(path)
      for (i <- 1 to numberOfProofs) {
        val filePath    = Paths.get(destinationPath, directoryName, "Proof" + i)
        val file        = Files.createFile(filePath)
        val nextProof = generateProofWrapper(rootSequent)
        Files.write(file,ProofToTPTPFile(nextProof).getBytes())
      }
    } catch  {
      case e : FileAlreadyExistsException => println("Files already exists")
      case e : NoSuchFileException        => println("The directory selected does not exist")
      case e : Throwable                  => println("Unexpected problem\n" + e)
    }
  }


}

/**
  * The trait ProofGeneratorTrait should be use as the interface of the client to generate random proofs
  */
trait ProofGeneratorTrait {
  def generateProof()               : Proof[Node] = generateProof(Sequent()())
  def generateProof(root : Sequent) : Proof[Node]
}

object ProofToTPTPFile {
  def apply(proof : Proof[Node]) : String = {
    var formulaName : Int    = 0
    var tptpProof   : String = ""
    def addFormula(annotatedFormula : String) : Unit =
      tptpProof += annotatedFormula + "\n"

    proof foldDown { (node : Node, premises : Seq[String]) =>
      node match {
        case Axiom(_)                    =>
          require(premises.isEmpty)
          val name = "c" + formulaName
          addFormula("cnf(" + name + ",axiom," + sequentToString(node.conclusion) + ").")
          formulaName += 1
          name
        case Contraction(_,_)            =>
          require(premises.length == 1)
          val name = "c" + formulaName
          addFormula("cnf(" + name + ",plain," + sequentToString(node.conclusion) + ",inference(cn,[status(thm)],[" + premises.head + "])).")
          formulaName += 1
          name
        case UnifyingResolution(_,_,_,_) =>
          require(premises.length == 2)
          val name = "c" + formulaName
          addFormula("cnf(" + name + ",plain," + sequentToString(node.conclusion) + ",inference(sr,[status(thm)],[" + premises(0) + "," + premises(1) + "])).")
          formulaName += 1
          name
      }
    }
    tptpProof
  }

  private def sequentToString(sequent : Sequent) : String = {
    def literalToString(literal : E) : String =
      literal match {
        case Atom(Var(name,_),args) => name + "(" + (args map termToString).mkString(",") + ")"
      }

    def termToString(term : E) : String =
      term match {
        case Var(name,_)                    => name
        case FunctionTerm(Var(name,_),args) => name + "(" + (args map termToString).mkString(",") + ")"
      }

    val antString = (sequent.ant map ((x : E) => "~" + literalToString(x))).mkString(" | ")
    val sucString = (sequent.suc map literalToString).mkString(" | ")
    if(sequent.ant.isEmpty && sequent.suc.isEmpty) "$false"
    else if(sequent.ant.isEmpty) sucString
    else if(sequent.suc.isEmpty) antString
    else antString + " | " + sucString
  }
}