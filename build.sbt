name := "Skeptik"

organization := "at.logic"

version := "1.0"

scalaVersion := "2.11.1"

scalacOptions ++= Seq("-unchecked", "-deprecation", "-feature", "-optimize")

scalacOptions in (Compile, doc) ++= Seq("-diagrams","-implicits")

libraryDependencies ++= Seq(
  "org.specs2" %% "specs2" % "2.3.12",
  "com.github.scopt" %% "scopt" % "3.2.0",
  "org.scala-lang" % "scala-actors" % "2.10.2",
  "org.scala-lang" % "scala-library" % "2.11.1",
  "org.scala-lang.modules" %% "scala-parser-combinators" % "1.0.1",
  "org.scala-lang.plugins" %% "scala-continuations-library" % "1.0.1", // apparently needed because of timeout and deprecated actors library
  "com.github.scala-incubator.io" %% "scala-io-file" % "0.4.3", // seems inactive
  "org.scalaz" %% "scalaz-core" % "7.0.6"
)

licenses := Seq("CC BY-NC-SA" -> url("http://creativecommons.org/licenses/by-nc-sa/3.0/"))

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
	<sourceDirectory>src/main/scala</sourceDirectory>
	<testSourceDirectory>src/test/scala</testSourceDirectory>
    <plugins>
			<plugin>
				<groupId>net.alchim31.maven</groupId>
				<artifactId>scala-maven-plugin</artifactId>
				<version>3.1.0</version>
				<executions>
					<execution>
						<goals>
							<goal>compile</goal>
							<goal>testCompile</goal>
						</goals>
					</execution>
				</executions>
			</plugin>
			<plugin>
				<groupId>org.apache.maven.plugins</groupId>
				<artifactId>maven-surefire-plugin</artifactId>
				<version>2.7</version>
				<configuration>
					<useFile>false</useFile>
					<disableXmlReport>true</disableXmlReport>
					<!-- If you have classpath issue like NoDefClassError,... -->
					<!-- useManifestOnlyJar>false</useManifestOnlyJar -->
					<includes>
						<include>**/*</include>
					</includes>
					<excludes>
						<exclude>**/*.off</exclude>
					</excludes>
				</configuration>
			</plugin>
		</plugins>
	</build>	
	<reporting>
		<plugins>
			<plugin>
				<groupId>net.alchim31.maven</groupId>
				<artifactId>scala-maven-plugin</artifactId>
				<version>3.1.0</version>
			</plugin>
		</plugins>
	</reporting>
)
