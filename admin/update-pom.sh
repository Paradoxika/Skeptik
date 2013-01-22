#! /bin/bash

# Updates pom.xml to reflect changes in build.sbt

cd ..
sbt make-pom 
cp target/scala-2.10/skeptik_2.10-0.2-SNAPSHOT.pom pom.xml
cd admin