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
      val mod = time("parse")(surface.Parser.parseModule("test", text))
      println(mod)
    catch case e: Exception => e.printStackTrace()
