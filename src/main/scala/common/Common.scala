package common

import scala.collection.mutable

object Common:
  inline def impossible(): Nothing =
    throw new RuntimeException("impossible")

  final case class PosInfo(line: Int, column: Int): // 1-based
    override def toString: String = s"$line:$column"
    def subCol(n: Int): PosInfo = PosInfo(line, column - n)
  object PosInfo:
    def start: PosInfo = PosInfo(1, 1)

  // names
  enum Name:
    case Nm(name: String)
    case Op(name: String)

    override def toString: String = this match
      case Nm(x) => x
      case Op(x) => s"($x)"

    def expose: String = this match
      case Nm(x) => x
      case Op(x) => x

  object Name:
    private val namestore: mutable.Map[String, Name] = mutable.Map.empty
    private val opstore: mutable.Map[String, Name] = mutable.Map.empty
    def apply(name: String): Name = namestore.getOrElseUpdate(name, Nm(name))
    def op(name: String): Name = opstore.getOrElseUpdate(name, Op(name))

  enum Bind:
    case Dont
    case Do(name: Name)

    override def toString: String = this match
      case Dont  => "_"
      case Do(x) => s"$x"

    def toName: Name = this match
      case Dont  => Name("_")
      case Do(x) => x

    def expose: String = this match
      case Dont  => "_"
      case Do(x) => x.expose

  // icit
  enum Icit:
    case Expl
    case Impl

    def wrap(x: Any): String = this match
      case Expl => s"($x)"
      case Impl => s"{$x}"
