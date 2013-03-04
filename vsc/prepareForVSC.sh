# Prepares Skeptik for running in the Vienna Scientific Cluster.
# Creates jar executable and moves it to "vsc" folder.

cd ..
sbt one-jar
SCALA_VERSION="2.10.1-RC2"
cp ./target/scala-${SCALA_VERSION}/skeptik_${SCALA_VERSION}-1.0-one-jar.jar vsc/skeptik.jar