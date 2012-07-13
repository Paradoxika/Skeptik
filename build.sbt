name := "Skeptik"

version := "0.1"

scalaVersion := "2.9.1"

scalacOptions ++= Seq("-unchecked", "-deprecation")

libraryDependencies ++= Seq(
  "org.scalatest" %% "scalatest" % "1.7.2",
  "org.specs2" %% "specs2" % "1.10",
  "org.scalacheck" %% "scalacheck" % "1.9"
)
