import scala.io.StdIn.readLine

object Main:
  @main
  def run(): Unit =
    while true do
      val text = readLine()
      try
        val tm = surface.Parser.parse(text)
        println(tm)
      catch case e: Exception => e.printStackTrace()
