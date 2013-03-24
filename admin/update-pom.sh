#! /bin/bash

# Updates pom.xml to reflect changes in build.sbt

cd ..
sbt make-pom 
cp target/scala-2.10/skeptik_2.10-1.0.pom pom.xml
cd admin