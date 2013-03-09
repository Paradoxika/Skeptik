import sbt._
import Keys._
import sys.process._

object SkeptikBuild extends Build {

  val jar = TaskKey[Unit]("jar", "Copies the jar file produced by one-jar into the root directory.")
  val jarTask = jar <<= (scalaVersion,version) map { (s,v) =>
    val command = "cp ./target/scala-" + s + 
                  "/skeptik_" + s + "-" + v + "-one-jar.jar skeptik.jar"
    println(command)
    command !;
  }

  val pom = TaskKey[Unit]("update-pom", "Copies the pom file produced by make-pom into the root directory.")
  val pomTask = pom <<= (scalaVersion,version) map { (s,v) =>
    val command = "cp ./target/scala-" + s + 
                  "/skeptik_" + s + "-" + v + ".pom pom.xml"
    println(command)
    command !;
  }
  
  
  val skeptikSettings = Defaults.defaultSettings ++ Seq(jarTask, pomTask)

  lazy val project = Project("project", file("."), settings = skeptikSettings)
}