package at.logic.skeptik.util

import scalax.io.{Resource,Seekable}
//import scalax.io.Codec
import scalax.io.JavaConverters._



object io {
  abstract class Output {
    def write(s: Any): Unit
  }
  object Output {
    def apply(path: String) = if (path contains "stdout://") StandardOutput
                    else if (path contains "void://") NoOutput
                    else new FileOutput(path)
  }
  
  object NoOutput extends Output { def write(s:Any) = {} }
  
  object StandardOutput extends Output {
    def write(s:Any) = print(s.toString)  
  }
  
  class FileOutput(path: String) extends Output {
    private val w = Resource.fromFile(path)
    def isEmpty = w.lines().isEmpty
    def write(s:Any) = w.append(s.toString) 
  }
  
  
  class Input(path: String) {
    private val r = Resource.fromFile(path)
    
    def lines = r.lines()
  }
  object Input {
    def apply(path: String) = new Input(path)
  }
  
}