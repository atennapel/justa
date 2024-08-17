import surface.Parser.parse
import common.Debug.*

import scala.io.Source
import scala.util.Using
import parsley.{Success, Failure}

object Main:
  @main def run(): Unit =
    val filename = "test.txt"
    setDebug(false)
    val text = Using(Source.fromFile(filename)) { source =>
      source.mkString
    }.get
    parse(text) match
      case Success(sdefs) => println(sdefs)
      case Failure(err)   => println(s"syntax error at $err")
