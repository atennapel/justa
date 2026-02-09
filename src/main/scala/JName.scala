import Common.Name
import scala.collection.mutable

// escape a name to avoid issues in JVM bytecode
object JName:
  extension (x: Name) inline def escape: String = JName(x)

  def module(x: String): String =
    x.split("\\.").map(escapeName(_, false)).mkString(".")

  def apply(x: Name): String =
    x match
      case Name.Nm(x) => escapeName(x, false)
      case Name.Op(x) => escapeName(x, true)

  // naming
  private val nameCache: mutable.Map[String, String] = mutable.Map.empty
  private val chars: Map[Char, String] = Map(
    '`' -> "GRAVE",
    '~' -> "TILDE",
    '!' -> "EXCL",
    '@' -> "AT",
    '#' -> "HASH",
    '$' -> "DOLLAR",
    '%' -> "PERCENT",
    '^' -> "HAT",
    '&' -> "AMPER",
    '*' -> "STAR",
    '-' -> "DASH",
    '+' -> "PLUS",
    '=' -> "EQUALS",
    '|' -> "PIPE",
    '\\' -> "BACK",
    ':' -> "COLON",
    ';' -> "SEMI",
    ',' -> "COMMA",
    '<' -> "LT",
    '.' -> "PERIOD",
    '>' -> "GT",
    '?' -> "QUESTION",
    '/' -> "SLASH"
  )

  private def escapeName(x: String, escapeDollar: Boolean): String =
    nameCache.get(x) match
      case Some(y) => y
      case None =>
        val y = x.toCharArray
          .map { c =>
            if !escapeDollar && c == '$' then c
            else chars.get(c).fold(c)(y => s"_$y")
          }
          .mkString("")
        nameCache += (x -> y)
        y
