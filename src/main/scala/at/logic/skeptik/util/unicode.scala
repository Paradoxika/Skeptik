package at.logic.skeptik.util

object unicode {
  def unicodeOrElse(unicode: String, alternative: String) = 
    if (System.getProperty("file.encoding") == "UTF-8") unicode
    else alternative
}
    
