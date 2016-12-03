package at.logic.skeptik.experiments

import java.io.File
import java.util.Scanner
import scala.io.Source
import java.io.PrintWriter
import collection.mutable.{ HashMap => MMap, HashSet => MSet }

object DataCollector {

  def getListOfFiles(dir: String): List[File] = {
    val d = new File(dir)
    if (d.exists && d.isDirectory) {
      d.listFiles.filter(_.isFile).toList
    } else {
      List[File]()
    }
  }

  def copyIntoFinal(originalFile: File, finalFileWriter: PrintWriter, count: Int, numCommas: Int): Int = {

    val originalFileName = originalFile.getAbsoluteFile
    println("Copying " + originalFileName)
    val lines = Source.fromFile(originalFileName).getLines

    var fileCount = 0
    for (line <- lines) {
      if (line.count(_ == ',') == numCommas) {
        finalFileWriter.print((count + fileCount) + ",")
        finalFileWriter.print(originalFileName + ",")
        finalFileWriter.println(line)
        finalFileWriter.flush()
        fileCount = fileCount + 1
      }
    }

    fileCount
  }

  def main(arfs: Array[String]): Unit = {
    //makeBigList()

    makeTPTPCountFiles()

  }

  def makeBigList() = {
    val dataDir = "D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\1 Dec 2016\\Stats"
    val finalFileName = "D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\1 Dec 2016\\Collected\\random-all-data-dec1.txt"

    val dataFile = new File(finalFileName)
    if (!dataFile.exists()) {
      dataFile.createNewFile()
    }

    val files = getListOfFiles(dataDir)
    val finalWriter = new PrintWriter(finalFileName)
    //h+",
    //size + "," + resSize + "," + cSize + "," + cResSize + "," + cRatio + "," + cResRatio 
    //+ "," + nFO + "," + nCFO + "," + time
    finalWriter.print("num,originalFile," + "originalNum,")
    finalWriter.print(
      "rpiProofsize,rpiNumRes,rpiCompressedSize,"
        + "rpiNumResCompressed,rpiCompressRatio,"
        + "rpiCompressRatioRes,rpiFO,rpiCFO,rpiCompressTime,")
    finalWriter.print(
      "luProofsize,luNumRes,luCompressedSize,"
        + "luNumResCompressed,luCompressRatio,"
        + "luCompressRatioRes,luFO,luCFO,luCompressTime,")
    finalWriter.print(
      "rpiluProofsize,rpiluNumRes,rpiluCompressedSize,"
        + "rpiluNumResCompressed,rpiluCompressRatio,"
        + "rpiluCompressRatioRes,rpiluFO,rpiluCFO,rpiluCompressTime,")
    finalWriter.print(
      "lurpiProofsize,lurpiNumRes,lurpiCompressedSize,"
        + "lurpiNumResCompressed,lurpiCompressRatio,"
        + "lurpiCompressRatioRes,lurpiFO,lurpiCFO,lurpiCompressTime,")
    finalWriter.println("totalTime,RPIfailAfterLU,LUfailAfterRPI,proofFile")

    val numCommas = 40

    var count = 0
    for (file <- files) {
      count = count + copyIntoFinal(file, finalWriter, count, numCommas)
    }

  }
  
  //used to make data for num_stacked charts
  def makeTPTPCountFiles() {
    makeTPTPCountFile("D:\\Research Scripts\\GSoC14\\November 2016 - Charts - R\\cade-folu.txt", 
        "D:\\Research Scripts\\GSoC14\\November 2016 - Charts - R\\cade-folu-nc.txt")
        
    makeTPTPCountFile("D:\\Research Scripts\\GSoC14\\November 2016 - Charts - R\\cade-forpi.txt", 
        "D:\\Research Scripts\\GSoC14\\November 2016 - Charts - R\\cade-forpi-nc.txt")
        
    makeTPTPCountFile("D:\\Research Scripts\\GSoC14\\November 2016 - Charts - R\\cade-folurpi.txt", 
        "D:\\Research Scripts\\GSoC14\\November 2016 - Charts - R\\cade-folurpi-nc.txt")
        
    makeTPTPCountFile("D:\\Research Scripts\\GSoC14\\November 2016 - Charts - R\\cade-forpilu.txt", 
        "D:\\Research Scripts\\GSoC14\\November 2016 - Charts - R\\cade-forpilu-nc.txt")     
        
    makeTPTPCountFileAll("D:\\Research Scripts\\GSoC14\\November 2016 - Charts - R\\cade-forpilu.txt", 
        "D:\\Research Scripts\\GSoC14\\November 2016 - Charts - R\\cade-folurpi.txt", 
        "D:\\Research Scripts\\GSoC14\\November 2016 - Charts - R\\cade-folu.txt", 
        "D:\\Research Scripts\\GSoC14\\November 2016 - Charts - R\\cade-forpi.txt", 
        "D:\\Research Scripts\\GSoC14\\November 2016 - Charts - R\\cade-all-nc.txt")

   makeTPTPCountFileAllSeparate("D:\\Research Scripts\\GSoC14\\November 2016 - Charts - R\\cade-forpilu.txt", 
        "D:\\Research Scripts\\GSoC14\\November 2016 - Charts - R\\cade-folurpi.txt", 
        "D:\\Research Scripts\\GSoC14\\November 2016 - Charts - R\\cade-folu.txt", 
        "D:\\Research Scripts\\GSoC14\\November 2016 - Charts - R\\cade-forpi.txt", 
        "D:\\Research Scripts\\GSoC14\\November 2016 - Charts - R\\cade-all-nc-sep.txt", "forpilu", "folurpi", "folu", "forpi")
        
  }
  
  
  def makeTPTPCountFile(inFileName: String, outFileName: String) {

    //make the outfile
    val dataFile = new File(outFileName)
    if (!dataFile.exists()) {
      dataFile.createNewFile()
    }
    val finalWriter = new PrintWriter(outFileName)
    finalWriter.println("length,numCompressed,numNotCompressed,total")
    
    //process the data
    val lines = Source.fromFile(inFileName).getLines
    lines.next() //skip header
    
    val countMap = new MMap[Int, Int]()
    val compMap = new MMap[Int, Int]()
    
    for(line <- lines){
      val lineScanner = new Scanner(line)
      lineScanner.useDelimiter(",")
      
      val fileName = lineScanner.next()
      val isCompressed = lineScanner.next().toInt //0 or 1
      val len = lineScanner.next().toInt
      updateMap(countMap, len)
      if(isCompressed > 0){
         updateMap(compMap, len)
      }
      
    }
    
    val sortedKeys = collection.immutable.SortedSet[Int]() ++ countMap.keySet
    
    for(k <- sortedKeys){
      val numCompressed = if(compMap.keySet.contains(k)){
        compMap.get(k).get
      } else {
        0
      }
      val count = countMap.get(k).get
      val numUncompressed = count - numCompressed
      finalWriter.println(k + "," + numCompressed + "," + numUncompressed + "," + count)
    }
    finalWriter.flush()
    finalWriter.close()
   
  }
  
  def updateMap(map: MMap[Int,Int], key: Int){
    if(map.keySet.contains(key)){
      val oldValue = map.get(key).get //it should always return if the key is in the keyset.
      map.update(key, oldValue + 1)
    } else {
      map.put(key, 1)
    }
  }
  
 def makeTPTPCountFileAll(aIn: String, bIn: String, cIn: String, dIn: String, outFileName: String) {

    //make the outfile
    val dataFile = new File(outFileName)
    if (!dataFile.exists()) {
      dataFile.createNewFile()
    }
    val finalWriter = new PrintWriter(outFileName)
    finalWriter.println("length,numCompressed,numNotCompressed,total")
    
    val lines = Source.fromFile(aIn).getLines    
    
    //process the data
    val alines = Source.fromFile(aIn).getLines
    alines.next() //skip header
    val blines = Source.fromFile(bIn).getLines
    blines.next() //skip header
    val clines = Source.fromFile(cIn).getLines
    clines.next() //skip header
    val dlines = Source.fromFile(dIn).getLines
    dlines.next() //skip header
    
    val countMap = new MMap[Int, Int]()
    val compMap = new MMap[Int, Int]()
    
    for(i <- 0 to lines.size - 2){
      val (aLen, aComp, aName) = wasCompressed(alines)
      val (bLen, bComp, bName) = wasCompressed(blines)
      val (cLen, cComp, cName) = wasCompressed(clines)
      val (dLen, dComp, dName) = wasCompressed(dlines)
      
      assert(aName.equals(bName) && aName.equals(cName) && aName.equals(dName))
      val len = aLen
      
      val isCompressed = aComp || bComp || cComp || dComp
      
      updateMap(countMap, len)
      if(isCompressed){
         updateMap(compMap, len)
      }
    }
    
    val sortedKeys = collection.immutable.SortedSet[Int]() ++ countMap.keySet
    
    for(k <- sortedKeys){
      val numCompressed = if(compMap.keySet.contains(k)){
        compMap.get(k).get
      } else {
        0
      }
      val count = countMap.get(k).get
      val numUncompressed = count - numCompressed
      finalWriter.println(k + "," + numCompressed + "," + numUncompressed + "," + count)
    }
    finalWriter.flush()
    finalWriter.close()
   
  }  
 
 def wasCompressed(i: Iterator[String]): (Int, Boolean, String) = {
      val line = i.next()
      val lineScanner = new Scanner(line)
      lineScanner.useDelimiter(",")
      
      val fileName = lineScanner.next()
      val isCompressed = lineScanner.next().toInt //0 or 1
      val len = lineScanner.next().toInt
      val isCompressedBool = if(isCompressed == 0){
        false
      } else {
        true
      }
      lineScanner.close()
      return (len, isCompressedBool, fileName)
 }
 
def makeTPTPCountFileAllSeparate(aIn: String, bIn: String, cIn: String, dIn: String, outFileName: String,
    aName: String, bName: String, cName: String, dName: String) {

    //make the outfile
    val dataFile = new File(outFileName)
    if (!dataFile.exists()) {
      dataFile.createNewFile()
    }
    val finalWriter = new PrintWriter(outFileName)
    finalWriter.println("length,numCompressed"+aName+",numCompressed" + bName+",numCompressed" + cName+
        ",numCompressed" + dName+",numCompressedNonUnique,numCompressedByAll,numNotCompressed,total")
    
    val lines = Source.fromFile(aIn).getLines    
    
    //process the data
    val alines = Source.fromFile(aIn).getLines
    alines.next() //skip header
    val blines = Source.fromFile(bIn).getLines
    blines.next() //skip header
    val clines = Source.fromFile(cIn).getLines
    clines.next() //skip header
    val dlines = Source.fromFile(dIn).getLines
    dlines.next() //skip header
    
    val countMap = new MMap[Int, Int]()
    val compMapA = new MMap[Int, Int]()
    val compMapB = new MMap[Int, Int]()
    val compMapC = new MMap[Int, Int]()
    val compMapD = new MMap[Int, Int]()
    val compMapAll = new MMap[Int, Int]()
    val uncompMapAll = new MMap[Int, Int]()
    
    
    for(i <- 0 to lines.size - 2){
      val (aLen, aComp, aName) = wasCompressed(alines)
      val (bLen, bComp, bName) = wasCompressed(blines)
      val (cLen, cComp, cName) = wasCompressed(clines)
      val (dLen, dComp, dName) = wasCompressed(dlines)
      
      assert(aName.equals(bName) && aName.equals(cName) && aName.equals(dName))
      val len = aLen
      
      val isCompressedAll = aComp && bComp && cComp && dComp
      val unCompAll = !aComp && !bComp && !cComp && !dComp
      
      
      updateMap(countMap, len)
      if(isCompressedAll){
         updateMap(compMapAll, len)
      }
      if(aComp && (!bComp && !cComp && !dComp)){
        updateMap(compMapA,len)
      }
      if(bComp && (!aComp && !cComp && !dComp)){
        updateMap(compMapB,len)
      }
      if(cComp && (!bComp && !aComp && !dComp)){
        updateMap(compMapC,len)
      }
      if(dComp && (!bComp && !cComp && !aComp)){
        updateMap(compMapD,len)
      }      
      
      if(unCompAll){
        updateMap(uncompMapAll,len)
      }
      
    }
    
    val sortedKeys = collection.immutable.SortedSet[Int]() ++ countMap.keySet
    
    for(k <- sortedKeys){
      val numCompressedA = getCompCount(compMapA, k)
      val numCompressedB = getCompCount(compMapB, k)
      val numCompressedC = getCompCount(compMapC, k)
      val numCompressedD = getCompCount(compMapD, k)
      val numCompressedAll = getCompCount(compMapAll, k)
      
      val count = countMap.get(k).get
      val numUncompressed = getCompCount(uncompMapAll,k)
      val numCompNonunique = count - numUncompressed - numCompressedAll
      finalWriter.println(k + "," + numCompressedA + "," + numCompressedB + ","+ numCompressedC + ","+ numCompressedD + "," + 
         numCompNonunique + "," + numCompressedAll + "," + numUncompressed + "," +  count)
    }
    finalWriter.flush()
    finalWriter.close()
   
  }   

def getCompCount(map: MMap[Int,Int], k: Int): Int = {
  if(map.keySet.contains(k)){
        map.get(k).get
      } else {
        0
      }
}
}