name := "Skeptik"

organization := "at.logic"

version := "1.0"

scalaVersion := "2.10.0"

scalacOptions ++= Seq("-unchecked", "-deprecation", "-feature", "-optimize")

scalacOptions in (Compile, doc) ++= Seq("-diagrams","-implicits")


libraryDependencies ++= Seq(
  "org.specs2" % "_2.10.0-RC5" % "1.12.3",
  "junit" % "junit" % "4.11" % "test",
  "commons-lang" % "commons-lang" % "2.6",
  "org.scala-lang" % "scala-actors" % "2.10.0"
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

// OneJar Settings
seq(com.github.retronym.SbtOneJar.oneJarSettings: _*)