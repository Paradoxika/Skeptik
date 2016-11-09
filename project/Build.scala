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
  val skeptik = InputKey[Unit]("skeptik", "bla")
  val skeptikProve = InputKey[Unit]("skeptik-prove", "Skeptik prove CLI")
  val skeptikSettings = Seq(fullRunInputTask(skeptik,Runtime,"at.logic.skeptik.ProofCompressionCLI"),
                            fullRunInputTask(skeptikProve,Runtime,"at.logic.skeptik.ProveCLI"),
                             trapExit in skeptik := true ,
                             fork in skeptik := false,
                             traceLevel in skeptik := 0)
  
  
  val allSettings = Defaults.defaultSettings ++ 
                    jarSettings ++
                    pomSettings ++
                    skeptikSettings
                        

  lazy val project = Project("project", file("."), settings = allSettings)
}