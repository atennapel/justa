import common.Util.time

object Main:
  @main
  def run(): Unit =
    try
      val file = "test.txt"
      val src = io.Source.fromFile(file, "utf-8")
      val text =
        try src.getLines.mkString("\n")
        finally src.close
      val tm = time("parse")(surface.Parser.parse("test", text))
      println(tm)
    catch case e: Exception => e.printStackTrace()
