package at.logic.skeptik.algorithm

import at.logic.skeptik.expression._
import at.logic.skeptik.algorithm.congruence.EqW

/**
 * type EqLabel is the types of labels used for Graphs in the Congruence procedure and 
 * the type defined in the package object is an abbreviation
 * 
 * the label between two vertices is (u,v) is the equation u = v
 * the optional EquationPath tuple represents explanations for the equality of two compound terms App(u,v) and App(s,t)
 * i.e. the first element of the tuple is an explanation for u = s and the second for v = t
 */
//package object dijkstra {
//  type EqLabel = (EqW,Option[(EquationPath,EquationPath)])
//}