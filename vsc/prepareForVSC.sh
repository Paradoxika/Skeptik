cp ../build.sbt ../buildNotForVSC.sbt
cp buildVSC.sbt ../build.sbt
cd ..
sbt one-jar
cp ./target/scala-2.10.0-M7/skeptik_2.10.0-M7-0.2-SNAPSHOT-one-jar.jar vsc/skeptik.jar