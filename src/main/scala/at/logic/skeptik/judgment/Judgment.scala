package at.logic.skeptik.judgment 
  
abstract class Judgment {
  def logicalSize: Int
  
  def subsumes(j : Judgment): Boolean 
}
