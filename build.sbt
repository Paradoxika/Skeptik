name := "Skeptik"

organization := "at.logic"

version := "0.2-SNAPSHOT"

scalaVersion := "2.10.0-M7"

scalacOptions ++= Seq("-unchecked", "-deprecation", "-feature", "-optimize")

scalacOptions in (Compile, doc) ++= Seq("-diagrams","-implicits")


libraryDependencies ++= Seq(
  "org.scalatest" %% "scalatest" % "1.9-2.10.0-M7-B1",
  "org.specs2" %% "specs2" % "1.12.1",
  "org.scalacheck" %% "scalacheck" % "1.10.0",
  "junit" % "junit" % "4.10",
  "commons-lang" % "commons-lang" % "2.6"
)

// Uncomment the following line to use one-jar (https://github.com/sbt/sbt-onejar)
//seq(com.github.retronym.SbtOneJar.oneJarSettings: _*)

licenses := Seq("GNU GPL v3" -> url("http://www.gnu.org/licenses/gpl.html"))

homepage := Some(url("http://github.com/Paradoxika/Skeptik"))


publishMavenStyle := true

publishTo <<= version { (v: String) =>
  val nexus = "https://oss.sonatype.org/"
  if (v.trim.endsWith("SNAPSHOT")) 
    Some("snapshots" at nexus + "content/repositories/snapshots") 
  else
    Some("releases"  at nexus + "service/local/staging/deploy/maven2")
}

publishArtifact in Test := false

pomIncludeRepository := { _ => false }

pomExtra := (
  <scm>
    <url>git@github.com:Paradoxika/Skeptik.git</url>
    <connection>scm:git:git@github.com:Paradoxika/Skeptik.git</connection>
  </scm>
  <developers>
    <developer>
      <id>bruno.wp</id>
      <name>Bruno Woltzenlogel Paleo</name>
      <url>http://www.logic.at/People/Bruno/</url>
    </developer>
  </developers>
  <contributors>
  </contributors>
  	<properties>
		<encoding>UTF-8</encoding>
	</properties>
  	<build>
    <plugins>
			<plugin>
				<groupId>net.alchim31.maven</groupId>
				<artifactId>scala-maven-plugin</artifactId>
				<version>3.0.2</version>
				<configuration>
                	<args>
                    	<arg>-diagrams</arg>
                    	<arg>-implicits</arg>
                	</args>
                </configuration>
				<executions>
					<execution>
						<goals>
							<goal>compile</goal>
							<goal>testCompile</goal>
						</goals>
					</execution>
				</executions>
			</plugin>
		</plugins>
	</build>	
	<reporting>
		<plugins>
			<plugin>
				<groupId>net.alchim31.maven</groupId>
				<artifactId>scala-maven-plugin</artifactId>
				<version>3.0.2</version>
			</plugin>
		</plugins>
	</reporting>
)
