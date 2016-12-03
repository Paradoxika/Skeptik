package at.logic.skeptik.experiments

import java.io.File
import java.util.Scanner
import scala.io.Source
import java.io.PrintWriter
import collection.mutable.{ HashMap => MMap, HashSet => MSet }
import collection.SortedSet

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

    //makeTPTPCountFiles()

    makeRandomCountFiles()
    
    
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
  def makeRandomCountFiles() {
    val numBinsToUse = 16 //0 or negative for no binning
        
    makeRandomCountFiles("D:\\Research Scripts\\GSoC14\\November 2016 - Charts - R\\random-all-data-dec1.txt",
      "D:\\Research Scripts\\GSoC14\\November 2016 - Charts - R\\random-forpi-nc-data-dec1.txt",
      "D:\\Research Scripts\\GSoC14\\November 2016 - Charts - R\\random-folu-nc-data-dec1.txt",
      "D:\\Research Scripts\\GSoC14\\November 2016 - Charts - R\\random-forpilu-nc-data-dec1.txt",
      "D:\\Research Scripts\\GSoC14\\November 2016 - Charts - R\\random-folurpi-nc-data-dec1.txt",
      numBinsToUse)
      
      
    makeRandomCountFilesCombined("D:\\Research Scripts\\GSoC14\\November 2016 - Charts - R\\random-all-data-dec1.txt",
      "D:\\Research Scripts\\GSoC14\\November 2016 - Charts - R\\random-all-nc-data-dec1.txt",
      numBinsToUse)   
      
   makeRandomCountFilesSeparate("D:\\Research Scripts\\GSoC14\\November 2016 - Charts - R\\random-all-data-dec1.txt",
      "D:\\Research Scripts\\GSoC14\\November 2016 - Charts - R\\random-all-nc-sep-data-dec1.txt",
      numBinsToUse)         
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

    for (line <- lines) {
      val lineScanner = new Scanner(line)
      lineScanner.useDelimiter(",")

      val fileName = lineScanner.next()
      val isCompressed = lineScanner.next().toInt //0 or 1
      val len = lineScanner.next().toInt
      updateMap(countMap, len)
      if (isCompressed > 0) {
        updateMap(compMap, len)
      }

    }

    val sortedKeys = collection.immutable.SortedSet[Int]() ++ countMap.keySet

    for (k <- sortedKeys) {
      val numCompressed = if (compMap.keySet.contains(k)) {
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

  def updateMap(map: MMap[Int, Int], key: Int) {
    if (map.keySet.contains(key)) {
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

    for (i <- 0 to lines.size - 2) {
      val (aLen, aComp, aName) = wasCompressed(alines)
      val (bLen, bComp, bName) = wasCompressed(blines)
      val (cLen, cComp, cName) = wasCompressed(clines)
      val (dLen, dComp, dName) = wasCompressed(dlines)

      assert(aName.equals(bName) && aName.equals(cName) && aName.equals(dName))
      val len = aLen

      val isCompressed = aComp || bComp || cComp || dComp

      updateMap(countMap, len)
      if (isCompressed) {
        updateMap(compMap, len)
      }
    }

    val sortedKeys = collection.immutable.SortedSet[Int]() ++ countMap.keySet

    for (k <- sortedKeys) {
      val numCompressed = if (compMap.keySet.contains(k)) {
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
    val isCompressedBool = if (isCompressed == 0) {
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
    finalWriter.println("length,numCompressed" + aName + ",numCompressed" + bName + ",numCompressed" + cName +
      ",numCompressed" + dName + ",numCompressedNonUnique,numCompressedByAll,numNotCompressed,total")

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

    for (i <- 0 to lines.size - 2) {
      val (aLen, aComp, aName) = wasCompressed(alines)
      val (bLen, bComp, bName) = wasCompressed(blines)
      val (cLen, cComp, cName) = wasCompressed(clines)
      val (dLen, dComp, dName) = wasCompressed(dlines)

      assert(aName.equals(bName) && aName.equals(cName) && aName.equals(dName))
      val len = aLen

      val isCompressedAll = aComp && bComp && cComp && dComp
      val unCompAll = !aComp && !bComp && !cComp && !dComp

      updateMap(countMap, len)
      if (isCompressedAll) {
        updateMap(compMapAll, len)
      }
      if (aComp && (!bComp && !cComp && !dComp)) {
        updateMap(compMapA, len)
      }
      if (bComp && (!aComp && !cComp && !dComp)) {
        updateMap(compMapB, len)
      }
      if (cComp && (!bComp && !aComp && !dComp)) {
        updateMap(compMapC, len)
      }
      if (dComp && (!bComp && !cComp && !aComp)) {
        updateMap(compMapD, len)
      }

      if (unCompAll) {
        updateMap(uncompMapAll, len)
      }

    }

    val sortedKeys = collection.immutable.SortedSet[Int]() ++ countMap.keySet

    for (k <- sortedKeys) {
      val numCompressedA = getCompCount(compMapA, k)
      val numCompressedB = getCompCount(compMapB, k)
      val numCompressedC = getCompCount(compMapC, k)
      val numCompressedD = getCompCount(compMapD, k)
      val numCompressedAll = getCompCount(compMapAll, k)

      val count = countMap.get(k).get
      val numUncompressed = getCompCount(uncompMapAll, k)
      val numCompNonunique =(count - numUncompressed) - (numCompressedA + numCompressedB + numCompressedC + numCompressedD + numCompressedAll) 
        //count - numUncompressed - numCompressedAll
      finalWriter.println(k + "," + numCompressedA + "," + numCompressedB + "," + numCompressedC + "," + numCompressedD + "," +
        numCompNonunique + "," + numCompressedAll + "," + numUncompressed + "," + count)
    }
    finalWriter.flush()
    finalWriter.close()

  }

  def getCompCount(map: MMap[Int, Int], k: Int): Int = {
    if (map.keySet.contains(k)) {
      map.get(k).get
    } else {
      0
    }
  }

  def makeFileIfNecessaryAndReturnWriter(outFileName: String): PrintWriter = {
    //make the outfile
    val dataFile = new File(outFileName)
    if (!dataFile.exists()) {
      dataFile.createNewFile()
    }
    val finalWriter = new PrintWriter(outFileName)
    return finalWriter
  }

  def makeRandomCountFiles(inFileName: String, outFileRPIName: String,
                           outFileLUName: String, outFileRPILUName: String, outFileLURPIName: String, numBins: Int) {
    
    val bin = if (numBins > 0) { true } else { false }

    val rpiFileWriter = makeFileIfNecessaryAndReturnWriter(outFileRPIName)
    val luFileWriter = makeFileIfNecessaryAndReturnWriter(outFileLUName)
    val rpiluFileWriter = makeFileIfNecessaryAndReturnWriter(outFileRPILUName)
    val lurpiFileWriter = makeFileIfNecessaryAndReturnWriter(outFileLURPIName)

    val header = if (!bin){
      "length,numCompressed,numNotCompressed,total"
    } else {
      "length,numCompressed,numNotCompressed,total,binDescription"
    }
    
    rpiFileWriter.println(header)
    luFileWriter.println(header)
    rpiluFileWriter.println(header)
    lurpiFileWriter.println(header)

    //process the data
    val lines = Source.fromFile(inFileName).getLines
    lines.next() //skip header

    val countMap = new MMap[Int, Int]()
    val compMapRPI = new MMap[Int, Int]()
    val compMapLU = new MMap[Int, Int]()
    val compMapLURPI = new MMap[Int, Int]()
    val compMapRPILU = new MMap[Int, Int]()

    for (line <- lines) {
      val lineScanner = new Scanner(line)
      lineScanner.useDelimiter(",")

      //example line:
      //14,D:\Research Data\GSoC14\November 2016 Random Proof Data\Generated\1 Dec 2016\Stats\random-retest-results-Wed Nov 30 23-43-08 EST 2016.txt,14,385,199,385,199,1.0,1.0,0,0,31877479,385,199,-2,-2,-2,-2,0,-2,1658448468,385,199,385,199,1.0,1.0,0,0,1689651306,385,199,385,199,1.0,1.0,0,0,1706574572,3396225878,false,true,D:\Research Data\GSoC14\November 2016 Random Proof Data\Generated\21 Nov 2016\Retest\random-results-Mon Nov 21 22-28-48 EST 2016-proof-9.txt

      //14,D:\Research Data\GSoC14\November 2016 Random Proof Data\Generated\1 Dec 2016\Stats\random-retest-results-Wed Nov 30 23-43-08 EST 2016.txt,14,
      val proofNum = lineScanner.next()
      val fileName = lineScanner.next()
      val oldProofNum = lineScanner.next()

      //385,199,
      val len = lineScanner.next().toInt //len is the same for all measured executions
      val numRes = lineScanner.next().toInt //same for all measured executions

      updateMap(countMap, len)

      //385,199,1.0,1.0,0,0,31877479,
      //RPI data
      val rpiCompSize = lineScanner.next().toInt
      val rpiCompResSize = lineScanner.next().toInt
      if ((rpiCompSize != len || rpiCompResSize != numRes) && rpiCompSize > 0) {
        //RPI compressed
        updateMap(compMapRPI, len)
      }
      lineScanner.next() //skip comp ratio
      lineScanner.next() //skip res comp ratio
      lineScanner.next() //skip FO count
      lineScanner.next() //skip compressed FO count
      lineScanner.next() //skip time

      //LU data
      //385,199,-2,-2,-2,-2,0,-2,1658448468,
      lineScanner.next() //skip proof length (hasn't changed)
      lineScanner.next() //skip proof res length (hasn't changed)
      val luCompSize = lineScanner.next().toInt
      val luCompResSize = lineScanner.next().toInt
      //      println("len: " + len + " numRes: " + numRes + " luCSize: " + luCompSize + " luRCsize: " + luCompResSize)

      if ((luCompSize != len || luCompResSize != numRes) && luCompSize > 0) {
        //LU compressed
        updateMap(compMapLU, len)
      }
      lineScanner.next() //skip comp ratio
      lineScanner.next() //skip res comp ratio
      lineScanner.next() //skip FO count
      lineScanner.next() //skip compressed FO count
      lineScanner.next() //skip time

      //RPILU data
      //385,199,385,199,1.0,1.0,0,0,1689651306,
      lineScanner.next() //skip proof length (hasn't changed)
      lineScanner.next() //skip proof res length (hasn't changed)      
      val rpiluCompSize = lineScanner.next().toInt
      val rpiluCompResSize = lineScanner.next().toInt
      if ((rpiluCompSize != len || rpiluCompResSize != numRes) && rpiluCompSize > 0) {
        //RPILU compressed
        updateMap(compMapRPILU, len)
      }
      lineScanner.next() //skip comp ratio
      lineScanner.next() //skip res comp ratio
      lineScanner.next() //skip FO count
      lineScanner.next() //skip compressed FO count
      lineScanner.next() //skip time

      //LURPI data
      //385,199,385,199,1.0,1.0,0,0,1706574572,
      lineScanner.next() //skip proof length (hasn't changed)
      lineScanner.next() //skip proof res length (hasn't changed)      
      val lurpiCompSize = lineScanner.next().toInt
      val lurpiCompResSize = lineScanner.next().toInt
      if ((lurpiCompSize != len || lurpiCompResSize != numRes) && lurpiCompSize > 0) {
        //LURPI compressed
        updateMap(compMapLURPI, len)
      }
      //Don't technically need to do this, but we do it so I don't forget to do it later.
      lineScanner.next() //skip comp ratio
      lineScanner.next() //skip res comp ratio
      lineScanner.next() //skip FO count
      lineScanner.next() //skip compressed FO count
      lineScanner.next() //skip time      

      //And the rest (ignored)
      //3396225878,false,true,D:\Research Data\GSoC14\November 2016 Random Proof Data\Generated\21 Nov 2016\Retest\random-results-Mon Nov 21 22-28-48 EST 2016-proof-9.txt

    }

    val sortedKeys = collection.immutable.SortedSet[Int]() ++ countMap.keySet

    if (!bin) {
      writeDataToFile(sortedKeys, compMapRPI, countMap, rpiFileWriter)
      writeDataToFile(sortedKeys, compMapLU, countMap, luFileWriter)
      writeDataToFile(sortedKeys, compMapRPILU, countMap, rpiluFileWriter)
      writeDataToFile(sortedKeys, compMapLURPI, countMap, lurpiFileWriter)
    } else {
      val numPerBin = countMap.keySet.size / numBins //make sure it divides evenly! 
      println("Num per bin: " + numPerBin + " (Make sure this is a good value, or try a new number of bins)")
      writeDataToFileBins(sortedKeys, compMapLU, countMap, luFileWriter, numBins)
      writeDataToFileBins(sortedKeys, compMapRPI, countMap, rpiFileWriter, numBins)
      writeDataToFileBins(sortedKeys, compMapRPILU, countMap, rpiluFileWriter, numBins)
      writeDataToFileBins(sortedKeys, compMapLURPI, countMap, lurpiFileWriter, numBins)
    }
    rpiFileWriter.flush()
    rpiFileWriter.close()
    luFileWriter.flush()
    luFileWriter.close()
    rpiluFileWriter.flush()
    rpiluFileWriter.close()
    lurpiFileWriter.flush()
    lurpiFileWriter.close()

  }

  def writeDataToFile(sortedKeys: SortedSet[Int], compMap: MMap[Int, Int], countMap: MMap[Int, Int], writer: PrintWriter) = {
    for (k <- sortedKeys) {
      val numCompressed = if (compMap.keySet.contains(k)) {
        compMap.get(k).get
      } else {
        0
      }
      val count = countMap.get(k).get
      val numUncompressed = count - numCompressed
      writer.println(k + "," + numCompressed + "," + numUncompressed + "," + count)
    }
  }

  def writeDataToFileBins(sortedKeys: SortedSet[Int], compMap: MMap[Int, Int], countMap: MMap[Int, Int],
                          writer: PrintWriter, numBins: Int) = {
    val numPerBin = countMap.keySet.size / numBins //make sure it divides evenly!
  
    var binIndex = 0;
    val binKeys = sortedKeys.grouped(numPerBin)
    val binKeysB = sortedKeys.grouped(numPerBin)
    
    //      for(i <- binKeys){
    //      println(i)
    //      }

    val mins = for (i <- binKeysB) yield i.min
    val minsList = mins.toList
    
    for (i <- binKeys) {
      var numCompressedBin = 0;
      var countBin = 0;
      for (k <- i) {
        val numCompressed = if (compMap.keySet.contains(k)) {
          compMap.get(k).get
        } else {
          0
        }
        val count = countMap.get(k).get
        countBin = countBin + count
        numCompressedBin = numCompressedBin + numCompressed

      }
      val numUncompressedBin = countBin - numCompressedBin
      
      val keyMin = i.min
      val keyMax = if(binIndex < numBins - 1){
        minsList(binIndex + 1)-1
      } else {
        i.max
      }

      val binDescription = keyMin + "-" + keyMax
      
      writer.println(binIndex + "," + numCompressedBin + "," + numUncompressedBin + "," + countBin +"," + binDescription)
      binIndex = binIndex + 1
    }
  }
  
  //countMap, uncompMapAll, compMapRPI, compMapLU, compMapRPILU, compMapLURPI
  def writeDataToFileBins(sortedKeys: SortedSet[Int], countMap: MMap[Int, Int], uncompMap: MMap[Int, Int],
                          compMapRPI: MMap[Int, Int], compMapLU: MMap[Int, Int],
                          compMapLURPI: MMap[Int, Int], compMapRPILU: MMap[Int, Int],
                          compMapAll: MMap[Int, Int], writer: PrintWriter, numBins: Int) = {
    val numPerBin = countMap.keySet.size / numBins //make sure it divides evenly!
  
    var numProofs = 0
    
    var binIndex = 0;
    val binKeys = sortedKeys.grouped(numPerBin)
    val binKeysB = sortedKeys.grouped(numPerBin)
    
    //      for(i <- binKeys){
    //      println(i)
    //      }

    val mins = for (i <- binKeysB) yield i.min
    val minsList = mins.toList
    
    for (i <- binKeys) {
      
      var numCompressedRPIbin = 0
      var numCompressedLUbin = 0
      var numCompressedRPILUbin = 0
      var numCompressedLURPIbin = 0
      var numCompressedAllbin = 0
       
      var numUncompressedbin = 0; 
      var countBin = 0; 
      
      for (k <- i) {
          val numCompressedRPI = getCompCount(compMapRPI, k)
          val numCompressedLU = getCompCount(compMapLU, k)
          val numCompressedRPILU = getCompCount(compMapRPILU, k)
          val numCompressedLURPI = getCompCount(compMapLURPI, k)
          val numCompressedAll = getCompCount(compMapAll, k) 
          val numUncompressed = getCompCount(uncompMap, k)
          val numCount = getCompCount(countMap,k)
          
          numCompressedRPIbin = numCompressedRPIbin + numCompressedRPI
          numCompressedLUbin = numCompressedLUbin + numCompressedLU
          numCompressedRPILUbin = numCompressedRPILUbin + numCompressedRPILU
          numCompressedLURPIbin = numCompressedLURPIbin + numCompressedLURPI
          numCompressedAllbin = numCompressedAllbin + numCompressedAll
          numUncompressedbin = numUncompressedbin + numUncompressed
          countBin = countBin + numCount
      }
            
      val keyMin = i.min
      val keyMax = if(binIndex < numBins - 1){
        minsList(binIndex + 1)-1
      } else {
        i.max
      }
      
      var numCompNonuniquebin = (countBin - numUncompressedbin) - (numCompressedAllbin + numCompressedRPIbin + numCompressedLUbin + numCompressedRPILUbin + numCompressedLURPIbin)
      //

      val binDescription = keyMin + "-" + keyMax
      
      writer.println(binIndex + "," + numCompressedRPIbin + "," + numCompressedLUbin + "," + numCompressedRPILUbin + "," + numCompressedLURPIbin + "," +
         numCompNonuniquebin + "," + numCompressedAllbin + "," + numUncompressedbin + "," + countBin + "," + binDescription)        
      binIndex = binIndex + 1
      numProofs = numProofs + countBin
    }
    println("Total proofs: " + numProofs)
  }  
  
  def writeDataToFileB(sortedKeys: SortedSet[Int], countMap: MMap[Int, Int], uncompMap: MMap[Int, Int],
                          compMapRPI: MMap[Int, Int], compMapLU: MMap[Int, Int],
                          compMapLURPI: MMap[Int, Int], compMapRPILU: MMap[Int, Int],
                          compMapAll: MMap[Int, Int], writer: PrintWriter) = {

      for (k <- sortedKeys) {
          val numCompressedRPI = getCompCount(compMapRPI, k)
          val numCompressedLU = getCompCount(compMapLU, k)
          val numCompressedRPILU = getCompCount(compMapRPILU, k)
          val numCompressedLURPI = getCompCount(compMapLURPI, k)
          val numCompressedAll = getCompCount(compMapAll, k) 
          val numUncompressed = getCompCount(uncompMap, k)
          val numCount = getCompCount(countMap,k)
      
          val numCompNonunique = (numCount - numUncompressed) - (numCompressedAll + numCompressedRPI + numCompressedLU + numCompressedRPILU + numCompressedLURPI)

          writer.println(k + "," + numCompressedRPI + "," + numCompressedLU + "," + numCompressedRPILU + "," + numCompressedLURPI + "," +
         numCompNonunique + "," + numCompressedAll + "," + numUncompressed + "," + numCount)        

      }
      
    
  }    

 def makeRandomCountFilesCombined(inFileName: String, outFileName: String, numBins: Int) {

    val bin =  if(numBins > 0) { true } else { false }

   
    val fileWriter = makeFileIfNecessaryAndReturnWriter(outFileName)


    val header = if (!bin){
      "length,numCompressed,numNotCompressed,total"
    } else {
      "length,numCompressed,numNotCompressed,total,binDescription"
    }
    
    fileWriter.println(header)


    //process the data
    val lines = Source.fromFile(inFileName).getLines
    lines.next() //skip header

    val countMap = new MMap[Int, Int]()
    val compMap = new MMap[Int, Int]()
    
    for (line <- lines) {
      val lineScanner = new Scanner(line)
      lineScanner.useDelimiter(",")

      var rpiCompressed = false
      var luCompressed = false
      var rpiluCompressed = false
      var lurpiCompressed = false
      
      //example line:
      //14,D:\Research Data\GSoC14\November 2016 Random Proof Data\Generated\1 Dec 2016\Stats\random-retest-results-Wed Nov 30 23-43-08 EST 2016.txt,14,385,199,385,199,1.0,1.0,0,0,31877479,385,199,-2,-2,-2,-2,0,-2,1658448468,385,199,385,199,1.0,1.0,0,0,1689651306,385,199,385,199,1.0,1.0,0,0,1706574572,3396225878,false,true,D:\Research Data\GSoC14\November 2016 Random Proof Data\Generated\21 Nov 2016\Retest\random-results-Mon Nov 21 22-28-48 EST 2016-proof-9.txt

      //14,D:\Research Data\GSoC14\November 2016 Random Proof Data\Generated\1 Dec 2016\Stats\random-retest-results-Wed Nov 30 23-43-08 EST 2016.txt,14,
      val proofNum = lineScanner.next()
      val fileName = lineScanner.next()
      val oldProofNum = lineScanner.next()

      //385,199,
      val len = lineScanner.next().toInt //len is the same for all measured executions
      val numRes = lineScanner.next().toInt //same for all measured executions

      updateMap(countMap, len)

      //385,199,1.0,1.0,0,0,31877479,
      //RPI data
      val rpiCompSize = lineScanner.next().toInt
      val rpiCompResSize = lineScanner.next().toInt
      if ((rpiCompSize != len || rpiCompResSize != numRes) && rpiCompSize > 0) {
        //RPI compressed
        rpiCompressed = true
      }
      lineScanner.next() //skip comp ratio
      lineScanner.next() //skip res comp ratio
      lineScanner.next() //skip FO count
      lineScanner.next() //skip compressed FO count
      lineScanner.next() //skip time

      //LU data
      //385,199,-2,-2,-2,-2,0,-2,1658448468,
      lineScanner.next() //skip proof length (hasn't changed)
      lineScanner.next() //skip proof res length (hasn't changed)
      val luCompSize = lineScanner.next().toInt
      val luCompResSize = lineScanner.next().toInt
      //      println("len: " + len + " numRes: " + numRes + " luCSize: " + luCompSize + " luRCsize: " + luCompResSize)

      if ((luCompSize != len || luCompResSize != numRes) && luCompSize > 0) {
        //LU compressed
        luCompressed = true
      }
      lineScanner.next() //skip comp ratio
      lineScanner.next() //skip res comp ratio
      lineScanner.next() //skip FO count
      lineScanner.next() //skip compressed FO count
      lineScanner.next() //skip time

      //RPILU data
      //385,199,385,199,1.0,1.0,0,0,1689651306,
      lineScanner.next() //skip proof length (hasn't changed)
      lineScanner.next() //skip proof res length (hasn't changed)      
      val rpiluCompSize = lineScanner.next().toInt
      val rpiluCompResSize = lineScanner.next().toInt
      if ((rpiluCompSize != len || rpiluCompResSize != numRes) && rpiluCompSize > 0) {
        //RPILU compressed
        rpiluCompressed = true
      }
      lineScanner.next() //skip comp ratio
      lineScanner.next() //skip res comp ratio
      lineScanner.next() //skip FO count
      lineScanner.next() //skip compressed FO count
      lineScanner.next() //skip time

      //LURPI data
      //385,199,385,199,1.0,1.0,0,0,1706574572,
      lineScanner.next() //skip proof length (hasn't changed)
      lineScanner.next() //skip proof res length (hasn't changed)      
      val lurpiCompSize = lineScanner.next().toInt
      val lurpiCompResSize = lineScanner.next().toInt
      if ((lurpiCompSize != len || lurpiCompResSize != numRes) && lurpiCompSize > 0) {
        //LURPI compressed
        lurpiCompressed = true
      }
      //Don't technically need to do this, but we do it so I don't forget to do it later.
      lineScanner.next() //skip comp ratio
      lineScanner.next() //skip res comp ratio
      lineScanner.next() //skip FO count
      lineScanner.next() //skip compressed FO count
      lineScanner.next() //skip time      

      //And the rest (ignored)
      //3396225878,false,true,D:\Research Data\GSoC14\November 2016 Random Proof Data\Generated\21 Nov 2016\Retest\random-results-Mon Nov 21 22-28-48 EST 2016-proof-9.txt

      if(rpiCompressed || luCompressed || lurpiCompressed || rpiluCompressed) {
        updateMap(compMap, len)
      }
    }

    val sortedKeys = collection.immutable.SortedSet[Int]() ++ countMap.keySet

    if (!bin) {
      writeDataToFile(sortedKeys, compMap, countMap, fileWriter)
    } else {
      val numPerBin = countMap.keySet.size / numBins //make sure it divides evenly! 
      println("Num per bin: " + numPerBin + " (Make sure this is a good value, or try a new number of bins)")
      writeDataToFileBins(sortedKeys, compMap, countMap, fileWriter, numBins)
    }
    fileWriter.flush()
    fileWriter.close()


  }  
 
  def makeRandomCountFilesSeparate(inFileName: String, outFileName: String, numBins: Int) {

    val bin =  if(numBins > 0) { true } else { false }
    
    val fileWriter = makeFileIfNecessaryAndReturnWriter(outFileName)

    //the thing being printed (from the function), for reference
    //binIndex + "," + numCompressedRPIbin + "," + numCompressedLUbin + "," + numCompressedRPILUbin + "," + numCompressedLURPIbin + "," +
    //numCompNonuniquebin + "," + numCompressedAllbin + "," + numUncompressedbin + "," + countBin + "," + binDescription)    
    
    val header = if (!bin){
      "length,numCompressedforpi,numCompressedfolu,numCompressedforpilu,numCompressedfolurpi,numCompressedNonUnique,numCompressedByAll,numNotCompressed,total"
    } else {
      //length should be binIndex, but that would require changing the R scripts
      "length,numCompressedforpi,numCompressedfolu,numCompressedforpilu,numCompressedfolurpi,numCompressedNonUnique,numCompressedByAll,numNotCompressed,total,binDescription"
    }
    
    fileWriter.println(header)

    //process the data
    val lines = Source.fromFile(inFileName).getLines
    lines.next() //skip header

    val countMap = new MMap[Int, Int]()
    val compMapRPI = new MMap[Int, Int]()
    val compMapLU = new MMap[Int, Int]()
    val compMapLURPI = new MMap[Int, Int]()
    val compMapRPILU = new MMap[Int, Int]()
    val compMapAll = new MMap[Int, Int]()
    val uncompMapAll = new MMap[Int, Int]()
    
    

    for (line <- lines) {
      val lineScanner = new Scanner(line)
      lineScanner.useDelimiter(",")

      var rpiCompressed = false
      var luCompressed = false
      var rpiluCompressed = false
      var lurpiCompressed = false      
      
      //example line:
      //14,D:\Research Data\GSoC14\November 2016 Random Proof Data\Generated\1 Dec 2016\Stats\random-retest-results-Wed Nov 30 23-43-08 EST 2016.txt,14,385,199,385,199,1.0,1.0,0,0,31877479,385,199,-2,-2,-2,-2,0,-2,1658448468,385,199,385,199,1.0,1.0,0,0,1689651306,385,199,385,199,1.0,1.0,0,0,1706574572,3396225878,false,true,D:\Research Data\GSoC14\November 2016 Random Proof Data\Generated\21 Nov 2016\Retest\random-results-Mon Nov 21 22-28-48 EST 2016-proof-9.txt

      //14,D:\Research Data\GSoC14\November 2016 Random Proof Data\Generated\1 Dec 2016\Stats\random-retest-results-Wed Nov 30 23-43-08 EST 2016.txt,14,
      val proofNum = lineScanner.next()
      val fileName = lineScanner.next()
      val oldProofNum = lineScanner.next()

      //385,199,
      val len = lineScanner.next().toInt //len is the same for all measured executions
      val numRes = lineScanner.next().toInt //same for all measured executions

      updateMap(countMap, len)

      //385,199,1.0,1.0,0,0,31877479,
      //RPI data
      val rpiCompSize = lineScanner.next().toInt
      val rpiCompResSize = lineScanner.next().toInt
      if ((rpiCompSize != len || rpiCompResSize != numRes) && rpiCompSize > 0) {
        //RPI compressed
        rpiCompressed = true
      }
      lineScanner.next() //skip comp ratio
      lineScanner.next() //skip res comp ratio
      lineScanner.next() //skip FO count
      lineScanner.next() //skip compressed FO count
      lineScanner.next() //skip time

      //LU data
      //385,199,-2,-2,-2,-2,0,-2,1658448468,
      lineScanner.next() //skip proof length (hasn't changed)
      lineScanner.next() //skip proof res length (hasn't changed)
      val luCompSize = lineScanner.next().toInt
      val luCompResSize = lineScanner.next().toInt
      //      println("len: " + len + " numRes: " + numRes + " luCSize: " + luCompSize + " luRCsize: " + luCompResSize)

      if ((luCompSize != len || luCompResSize != numRes) && luCompSize > 0) {
        //LU compressed
        luCompressed = true
      }
      lineScanner.next() //skip comp ratio
      lineScanner.next() //skip res comp ratio
      lineScanner.next() //skip FO count
      lineScanner.next() //skip compressed FO count
      lineScanner.next() //skip time

      //RPILU data
      //385,199,385,199,1.0,1.0,0,0,1689651306,
      lineScanner.next() //skip proof length (hasn't changed)
      lineScanner.next() //skip proof res length (hasn't changed)      
      val rpiluCompSize = lineScanner.next().toInt
      val rpiluCompResSize = lineScanner.next().toInt
      if ((rpiluCompSize != len || rpiluCompResSize != numRes) && rpiluCompSize > 0) {
        //RPILU compressed
        rpiluCompressed = true
      }
      lineScanner.next() //skip comp ratio
      lineScanner.next() //skip res comp ratio
      lineScanner.next() //skip FO count
      lineScanner.next() //skip compressed FO count
      lineScanner.next() //skip time

      //LURPI data
      //385,199,385,199,1.0,1.0,0,0,1706574572,
      lineScanner.next() //skip proof length (hasn't changed)
      lineScanner.next() //skip proof res length (hasn't changed)      
      val lurpiCompSize = lineScanner.next().toInt
      val lurpiCompResSize = lineScanner.next().toInt
      if ((lurpiCompSize != len || lurpiCompResSize != numRes) && lurpiCompSize > 0) {
        //LURPI compressed
        lurpiCompressed = true
      }
      //Don't technically need to do this, but we do it so I don't forget to do it later.
      lineScanner.next() //skip comp ratio
      lineScanner.next() //skip res comp ratio
      lineScanner.next() //skip FO count
      lineScanner.next() //skip compressed FO count
      lineScanner.next() //skip time      

      //And the rest (ignored)
      //3396225878,false,true,D:\Research Data\GSoC14\November 2016 Random Proof Data\Generated\21 Nov 2016\Retest\random-results-Mon Nov 21 22-28-48 EST 2016-proof-9.txt

      val isCompressedressedAll = rpiCompressed && luCompressed && rpiluCompressed && lurpiCompressed
      val unCompressedAll = !rpiCompressed && !luCompressed && !rpiluCompressed && !lurpiCompressed

      if (isCompressedressedAll) {
        updateMap(compMapAll, len)
      }
      if (rpiCompressed && (!luCompressed && !rpiluCompressed && !lurpiCompressed)) {
        updateMap(compMapRPI, len)
      }
      if (luCompressed && (!rpiCompressed && !rpiluCompressed && !lurpiCompressed)) {
        updateMap(compMapLU, len)
      }
      if (rpiluCompressed && (!luCompressed && !rpiCompressed && !lurpiCompressed)) {
        updateMap(compMapRPILU, len)
      }
      if (lurpiCompressed && (!luCompressed && !rpiluCompressed && !rpiCompressed)) {
        updateMap(compMapLURPI, len)
      }

      if (unCompressedAll) {
        updateMap(uncompMapAll, len)
      }  
      
    }

    val sortedKeys = collection.immutable.SortedSet[Int]() ++ countMap.keySet

    if (!bin) {
      writeDataToFileB(sortedKeys, countMap, uncompMapAll, compMapRPI, compMapLU, compMapRPILU, compMapLURPI, compMapAll, fileWriter)
    } else {
      val numPerBin = countMap.keySet.size / numBins //make sure it divides evenly! 
      println("Num per bin: " + numPerBin + " (Make sure this is a good value, or try a new number of bins)")
      writeDataToFileBins(sortedKeys, countMap, uncompMapAll, compMapRPI, compMapLU, compMapRPILU, compMapLURPI, compMapAll, fileWriter, numBins)
    }
    fileWriter.flush()
    fileWriter.close()

  } 
 
}