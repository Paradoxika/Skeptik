package at.logic.skeptik.experiments

import java.io.File
import scala.io.Source
import java.io.PrintWriter

object DataCollector {
  
 def getListOfFiles(dir: String):List[File] = {
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
   for(line <- lines){
    if(line.count(_ == ',') == numCommas){
      finalFileWriter.print((count+fileCount) + ",")
      finalFileWriter.print(originalFileName + ",")
      finalFileWriter.println(line)
      finalFileWriter.flush()
      fileCount = fileCount + 1
    }
   }
   
   fileCount
 }
 
  def main(arfs : Array[String]) : Unit = {
    
//    val dataDir = "D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\10 Nov 2016\\FOLU"
//    val dataDir = "D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\10 Nov 2016\\FOLU-FORPI"
//    val dataDir = "D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\10 Nov 2016\\FORPI-FOLU"
    val dataDir = "D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\1 Dec 2016\\Stats"
//    val finalFileName = "D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\10 Nov 2016\\Collected\\folu-all-data.txt"
//    val finalFileName = "D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\10 Nov 2016\\Collected\\folu-forpi-all-data.txt"
//    val finalFileName = "D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\10 Nov 2016\\Collected\\forpi-folu-all-data.txt"
    val finalFileName = "D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\1 Dec 2016\\Collected\\random-all-data-dec1.txt"
    
    val dataFile = new File(finalFileName)
    if (!dataFile.exists()){
      dataFile.createNewFile()
    }
    
    val files = getListOfFiles(dataDir)
//    val finalFile = new File(finalFileName)
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
    for(file <- files){
      count = count + copyIntoFinal(file, finalWriter, count, numCommas)
    }
    
    
  }
  
}