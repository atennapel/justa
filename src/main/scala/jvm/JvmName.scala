package jvm

import scala.collection.mutable

object JvmName:
  opaque type Name = String

  extension (x: Name)
    inline def escape: String = escapeName(x)
    inline def escapePath: String = escapeNameInPath(x)

  final case class MName(module: Name, name: Name)

  def apply(x: String): Name = x
  def apply(mod: String, x: String): MName = MName(mod, x)

  // naming
  private val nameCache: mutable.Map[String, String] = mutable.Map.empty
  private val chars: Map[String, String] = Map(
    "`" -> "GRAVE",
    "~" -> "TILDE",
    "!" -> "EXCL",
    "@" -> "AT",
    "#" -> "HASH",
    // "$" -> "DOLLAR",
    "%" -> "PERCENT",
    "^" -> "HAT",
    "&" -> "AMPER",
    "*" -> "STAR",
    "-" -> "DASH",
    "+" -> "PLUS",
    "=" -> "EQUALS",
    "|" -> "PIPE",
    "\\" -> "BACK",
    ":" -> "COLON",
    ";" -> "SEMI",
    "," -> "COMMA",
    "<" -> "LT",
    // "." -> "PERIOD",
    ">" -> "GT",
    "?" -> "QUESTION",
    "/" -> "SLASH"
  )

  private def escapeName(x: String): String =
    nameCache.get(x) match
      case Some(y) => y
      case None    =>
        // if x == "main" then
        //  val y = "main$"
        //  nameCache += (x -> y)
        //  y
        // else
        val y = x
          .split("")
          .map(c => chars.get(c).fold(c)(y => s"_$y"))
          .mkString("")
        nameCache += (x -> y)
        y

  private def escapeNameInPath(x: String): String =
    x.split('.').map(escapeName).mkString("/")
