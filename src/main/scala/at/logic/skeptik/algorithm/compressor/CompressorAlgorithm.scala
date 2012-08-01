package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof._

/* I've put everything in the same file for now. I think it'll be easier for
 * you to review. Comments explain where I plan to dispatch some parts later.
 *
 * Compared to what we discussed together there is one major difference. For a
 * long time I thought ProofNodeCollection were calculated too often for the
 * same proof (mostly because we need to know the size of the proof). On the
 * other hand, I can hardly imagine a compression algorithm which can't profit
 * having a ProofNodeCollection instead of a bare SequentProof. Hence I state
 * that compression algorithm have to be implemented as (ProofNodeCollection[P]
 * => P) instead of (P => P). I use a TimedProofWithCache structure to compute
 * the node collection corresponding to a proof once and on demand (using
 * lazyness).
 */





/* All this conversions should of course be moved to package object file
 * algorithm/compressor/package.scala.
 */
object conversions {
  
  /* Proof to TimedProofWithCache. Measures time needed to build the proof in
   * the meanwhile.                                                         */
  implicit def proof2timedProofWithCache[P <: Proof[_,P]](p: => P) = {
    System.gc()
    val now = System.nanoTime
    val result = p
    val time = (System.nanoTime.toDouble - now) / 1000000 // in milliseconds
    new TimedProofWithCache(result, time)
  }

  /* TimedProofWithCache to Proof */
  implicit def timedProofWithCache2proof[P <: Proof[_,P]](t: TimedProofWithCache[P]) = t.proof

  /* (Proof => Boolean) to Guard[Proof] */
  implicit def proofFct2guard[P <: Proof[_,P]](fct: P => Boolean) = new Guard[P] { def apply(r: TimedProofWithCache[P]) = fct(r.proof) }

  /* (() => Boolean) to Guard[_] */
  implicit def fct2guard[P <: Proof[_,P]](fct: () => Boolean) = new Guard[P] { def apply(r: TimedProofWithCache[P]) = fct() }

  /* Scala forbids to inherit from different fucntion traits. As a workaround,
   * some implicit conversion are provided.
   */

  /* AbstractCompressorAlgorithm to (Proof => Proof) */
  implicit def compressorAlgorithm2functionProof[P <: Proof[_,P]](a: AbstractCompressorAlgorithm[P]) =
    { (p: P) => a(new TimedProofWithCache(p,0.)) }

  /* AbstratcCompressorAlgorithm to ((Proof, Guard[Proof]) => Proof) */
  implicit def compressorAlgorithm2functionProofWithGuard[P <: Proof[_,P]](a: AbstractCompressorAlgorithm[P]) =
    { (p: P, g: Guard[P]) => a(new TimedProofWithCache(p,0), g).proof }

  /* AbstratcCompressorAlgorithm to ((TimedProofWithCache[P], Guard[P]) => TimedProofWithCache[P]) */
  implicit def compressorAlgorithm2functionTimedProofWithCacheWithGuard[P <: Proof[_,P]](a: AbstractCompressorAlgorithm[P]) =
    { (p: TimedProofWithCache[P], g: Guard[P]) => a(p,g) }

}

import conversions._





/* Base trait for CompressorAlgorithm. Concrete algorithms should inherit it
 * directly only if they want to profit from TimedProofWithCache. If only node
 * collection is needed, please use CompressorAlgorithm instead.
 */
trait AbstractCompressorAlgorithm [P <: Proof[_,P]]
{

  def apply(proof: TimedProofWithCache[P]):P

  def apply(proof: TimedProofWithCache[P], guard: Guard[P]):TimedProofWithCache[P]

}

/* Most concrete algorithm should inherit this trait and implement
 * apply(ProofNodeCollection[P]).
 */
trait CompressorAlgorithm [P <: Proof[_,P]]
extends AbstractCompressorAlgorithm[P]
{

  def apply(nodeCollection: ProofNodeCollection[P]):P

  def apply(proof: TimedProofWithCache[P]):P = apply(proof.collection)

}

/** An adaptator to transform a (P => P) algorithm into a CompressorAlgorithm.
 *
 * I'm not sure it'll be usefull, but it's easy to write.
 */
trait LegacyCompressorAlgorithm [P <: Proof[_,P]]
extends (P => P) with AbstractCompressorAlgorithm[P] {
  
  def apply(proof: TimedProofWithCache[P]):P = apply(proof.proof)

}

/* Every algorithm that should never be called iteratively should inherit that
 * trait.
 */
trait IdempotentAlgorithm [P <: Proof[_,P]]
extends AbstractCompressorAlgorithm[P] {

  def apply(proof: TimedProofWithCache[P], guard: Guard[P]):TimedProofWithCache[P] = {
    val compressedProof = proof2timedProofWithCache(apply(proof))
    guard(compressedProof)
    compressedProof
  }

}

/* Every algorithm that could be called iteratively should inherit that trait.
 */
trait RepeatableAlgorithm [P <: Proof[_,P]]
extends AbstractCompressorAlgorithm[P] {

  def apply(proof: TimedProofWithCache[P], guard: Guard[P]):TimedProofWithCache[P] = {
    val compressedProof = proof2timedProofWithCache(apply(proof))
    if (guard(compressedProof)) apply(compressedProof, guard) else compressedProof
  }

}

/* Algorithms which does compress the proof during a finite number of iterations
 * but become idempotent thereafter.
 */
trait RepeatableWhileCompressingAlgorithm [P <: Proof[_,P]]
extends RepeatableAlgorithm[P] {

  private def internalGuard(initialProof: TimedProofWithCache[P]) = new Guard[P] {
    var lastSize = initialProof.collection.size
    def apply(r: TimedProofWithCache[P]) = (lastSize > r.collection.size) && { lastSize = r.collection.size ; true }
  }

  override def apply(proof: TimedProofWithCache[P], guard: Guard[P]):TimedProofWithCache[P] = 
    super.apply(proof, internalGuard(proof) & guard)

}

/* Non-deterministic algorithms which might produce proof bigger than the
 * original.
 */
trait RandomCompressionRepeatableAlgorithm [P <: Proof[_,P]]
extends RepeatableAlgorithm[P] {

  override def apply(initialProof: TimedProofWithCache[P], guard: Guard[P]):TimedProofWithCache[P] = {
    val compressedProof = proof2timedProofWithCache(apply(initialProof))
    val resultProof = if (compressedProof.collection.size < initialProof.collection.size) compressedProof else initialProof
    if (guard(resultProof)) apply(resultProof, guard) else resultProof
  }

}





/* Class TimedProofWithCache serves two purposes. First it computes the node collection for
 * a proof once for all. This is a big improvement as node collection might be
 * computed up to 4 times for the same proof. Second it measures and stores
 * time spend to produce the proof.
 *
 * I'm wandering if it would be usefull to extend this class to store arbitrary
 * cached data. The implementation could be something like that :
 *
 * abstract class PropertyData
 *
 * abstract class Property[X, P <: Proof[_,P]] {
 *   val get: PartialFunction[PropertyData,X]
 *   def compute(p: TimedProofWithCache[P]): PropertyData
 *   def set(x:X): PropertyData = throw new Exception("Read-Only property")
 * }
 *
 * in class TimedProofWithCache [P] {
 *
 *   val properties = LinkedList[PropertyData]()
 *
 *   def get[X](prop: Property[X,P]):X = {
 *     def searchProp(l: LinkedList[PropertyData]):X =
 *       if (l.next eq l) { l.elem = prop.compute(this) ; l.next = LinkedList[PropertyData]() ; prop.get(l.elem) } else
 *       if (prop.get.isDefinedAt(l.elem)) prop.get(l.elem) else
 *       searchProp(l.next)
 *     }
 *     searchProp(properties)
 *   }
 *
 *   def set[X](prop: Property[X,P], x: X) = {
 *     def searchProp(l: LinkedList[PropertyData]):Unit =
 *       if (l.next eq l) { l.elem = prop.set(x) ; l.next = LinkedList[PropertyData]() } else
 *       if (prop.get.isDefinedAt(l.elem)) l.elem = set(l.elem) else
 *       searchProp(l.next)
 *     }
 *     searchProp(properties)
 *   }
 *       
 * }
 *
 * It could be used for instance to cache computed weights.
 *
 * in a Split class {
 *
 *   def apply(proof: TimedProofWithCache[SequentProof]) = {
 *     object computedWeights extends Property[(Map[E,Long],Long), SequentProof] {
 *       case class Data (map: Map[E,Long], sum: Long) extends PropertyData
 *       val get = { case Data(m,s) => (m,s) }
 *       val compute(r: TimedProofWithCache) = { val (m,s) = computeLiteralWeight(r.collection) ; Data(m,s) }
 *     }
 *     val (literalWeight, totalWeight) = proof.get(computedWeights)
 *     ...
 *
 * If this idea is implemented I'll move TimedProofWithCache to its own file. Otherwise, I
 * think we could keep it here.
 *
 */
class TimedProofWithCache [P <: Proof[_,P]] (val proof: P, val time: Double) {
  lazy val collection = ProofNodeCollection(proof)
}





/* Class Guard is quite terse. It could be implemented as a type alias too (as
 * you prefer).
 *
 * If kept as is, I plan to move it to algorithm/compressor/guard/Guard.scala.
 */
abstract class Guard [P <: Proof[_,P]] extends (TimedProofWithCache[P] => Boolean) {
  def &(other: Guard[P]) = new Guard[P] { def apply(r: TimedProofWithCache[P]) = this(r) & other(r) }
}

/* I find it more convenient to implement the default guards as functions and
 * anonymous classes. If you find it ugly it could of course be implemented as
 * classes and objects.
 *
 * If kept as is, I plan to move this functions to package object file
 * algorithm/compressor/guard/package.scala.
 */
object Guard {
  def once[P <: Proof[_,P]]    = new Guard[P] { def apply(r: TimedProofWithCache[P]) = false }
  def forever[P <: Proof[_,P]] = new Guard[P] { def apply(r: TimedProofWithCache[P]) = true }

  def timeout[P <: Proof[_,P]](howLong: Double) = new Guard[P] {
    var totalTime = 0.
    def apply(r: TimedProofWithCache[P]) = {
      totalTime += r.time
      totalTime < howLong
    }
  }

  def count[P <: Proof[_,P]](howMany: Long) = new Guard[P] {
    var count = 0
    def apply(r: TimedProofWithCache[P]) = {
      count += 1
      count < howMany
    }
  }
}
