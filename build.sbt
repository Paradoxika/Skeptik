name := "ResK"

version := "0.1"

scalaVersion := "2.9.1"


resolvers += "GridGain" at "http://www.gridgainsystems.com/maven2"

libraryDependencies ++= Seq(
  "org.gridgain" % "gridgain" % "4.0.2c",
  "org.scalatest" %% "scalatest" % "1.7.2",
  "org.specs2" %% "specs2" % "1.10",
  "org.scalacheck" %% "scalacheck" % "1.9"
)
