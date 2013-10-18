import sbt._
import Keys._
import sys.process._
import com.github.retronym.SbtOneJar._

object SkeptikBuild extends Build {
  
  private def major(version: String) = version.split("[.]").take(2).mkString(".")
  
  // Extension of "one-jar" to copy jar file to the root folder
  val jarS = oneJar <<= (oneJar,scalaVersion,version) map { (file,s,v) =>
    val m = major(s)
    sys.process.stringToProcess("cp ./target/scala-" + m + "/skeptik_" + m + "-" + v + "-one-jar.jar skeptik.jar") !;
    file
  }
  val jarSettings = oneJarSettings ++ 
                    Seq(jarS,
                        mainClass in oneJar := Some("at.logic.skeptik.ProofCompressionCLI"))
  
                        
  // Extension of "make-pom" to copy pom file to the root folder
  val pomS = makePom <<= (makePom,scalaVersion,version) map { (file, s,v) =>
    val m = major(s)
    sys.process.stringToProcess("cp ./target/scala-" + m + "/skeptik_" + m + "-" + v + ".pom pom.xml") !;
    file
  }
  val pomSettings = Seq(pomS)
  
 
  // Custom Run Tasks
  val compress = InputKey[Unit]("compress", "bla")
  val compressSettings = Seq(fullRunInputTask(compress,Runtime,"at.logic.skeptik.ProofCompressionCLI"),
                             trapExit in compress := true ,
                             fork in compress := false, 
                             traceLevel in compress := 0)
  
  
  val skeptikSettings = Defaults.defaultSettings ++ 
                        jarSettings ++
                        pomSettings ++
                        compressSettings
                        

  lazy val project = Project("project", file("."), settings = skeptikSettings)
}