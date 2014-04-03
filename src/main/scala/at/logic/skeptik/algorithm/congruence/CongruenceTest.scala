//package at.logic.skeptik.algorithm.congruence
//
//import at.logic.skeptik.proof.Proof
//import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
//import at.logic.skeptik.expression.formula._
//import at.logic.skeptik.proof.sequent.lk._
//import at.logic.skeptik.expression._
//import scala.collection.mutable.{HashMap => MMap}
//import at.logic.skeptik.proof.Proof.apply
//import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
//import scala.collection.mutable.{HashMap => MMap}
//
//object CongruenceTest extends (Proof[N] => Proof[N]) {
//  
//  def visit (node: N, fixedPremises: Seq[N]) = {
////    println(node.conclusion)
//    if (isEqHorn(node)) {
//      val con = new Congruence()
//      node.conclusion.ant.foreach(lit => {
//        con.addEquality(lit.asInstanceOf[Equation])
//      })
//      val concludes =  (node.conclusion.suc.forall(lit => {
//        lit match {
//          case Eq(l,r) => {
//            con.find.query(l) == con.find.query(r)
//          }
//          case _ => true
//        }
//      }))
//      if (concludes) {
//        (node.conclusion.ant.foreach(lit => {
//          val con2 = new Congruence()
//          node.conclusion.ant.foreach(lit2 => {
//            if (lit2 != lit) con2.addEquality(lit2.asInstanceOf[Equation])
//          })
//          val shorterConcludes = (node.conclusion.suc.forall(lit3 => {
//              lit3 match {
//                case Eq(l,r) => {
//                  con2.find.query(l) == con2.find.query(r)
//                }
//                case _ => true
//              }
//            }))
//            if (shorterConcludes) {
//              println("original: " + node.conclusion)
//              node.conclusion.suc.foreach(cLit => {
//                cLit match {
//                  case Eq(l,r) => println(con2.find.query(l) + " =?= " + con2.find.query(r))
//                }
//              })
//              println("can be dropped: " + lit)
//            }
//        }))
//      }
//    }
//    node
//  }
//    
//  def mightDeduct(node: N): Boolean = {
//    val depths = MMap[E,Int]()
//    node.conclusion.ant.exists(lit => {
//      lit match {
//        case Eq(l0) => {
//          val left = l0._1
//          val right = l0._2
//          val l = left match {
//            case App(f,l0) => {
//              if (!(depths.getOrElseUpdate(l0, 1) == 1)){
//                true
//              }
//              else false
//            }
//            case Var(_,_) => {
//              if (!(depths.getOrElseUpdate(left, 0) == 0)){
//                true
//              }
//              else false
//            }
//            case _ => false
//          }
//          val r = right match {
//            case App(f,l0) => {
//              if (!(depths.getOrElseUpdate(l0, 1) == 1)){
//                true
//              }
//              else false
//            }
//            case Var(_,_) => {
//              if (!(depths.getOrElseUpdate(left, 0) == 0)){
//                true
//              }
//              else false
//            }
//            case _ => false
//          }
//          r || l
//        }
//      }
//    })
//  }
//  
//  def isEqHorn(node: N): Boolean = {
//    val conc = node.conclusion
//    conc.ant.forall(lit => {
////      println(Eq.?:(lit) + " ~a " + And.?:(lit) + " ~ " + lit)
//      Eq.?:(lit)
////      lit.isInstanceOf[App[eqC(o)]]
//    }) && 
//    conc.suc.forall(lit => {
////      println(Eq.?:(lit) + " ~s " + And.?:(lit) + " ~ " + lit)
//      Eq.?:(lit)
////      lit.isInstanceOf[App[eqC(o)]]
//    }) && (conc.suc.size == 1) //&& // <= 1 is technically correct
////    node.isInstanceOf[R]
//  }
//  
//  def apply(proof: Proof[N]) = {
//    proof foldDown visit
//  }
//}