#! /bin/bash

# Updates pom.xml to reflect changes in build.sbt

root_dir=".."
admin_dir="admin"

scala_version="2.10.1-RC2"
skeptik_version="1.0"

cd $root_dir
sbt make-pom 
cp target/scala-${scala_version}/skeptik_${scala_version}-${skeptik_version}.pom pom.xml
cd $admin_dir