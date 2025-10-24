package common

import scala.collection.mutable

object Common:
  inline def impossible(): Nothing =
    throw new RuntimeException("impossible")

  // names
  enum Name:
    case Nm(name: String)
    case Op(name: String)

    override def toString: String = this match
      case Nm(x) => x
      case Op(x) => s"($x)"
  object Name:
    private val namestore: mutable.Map[String, Name] = new mutable.HashMap()
    private val opstore: mutable.Map[String, Name] = new mutable.HashMap()
    def apply(name: String): Name = namestore.getOrElseUpdate(name, Nm(name))
    def op(name: String): Name = opstore.getOrElseUpdate(name, Op(name))

  enum Bind:
    case Dont
    case Do(name: Name)

    override def toString: String = this match
      case Dont  => "_"
      case Do(x) => s"$x"

  // icit
  enum Icit:
    case Expl
    case Impl

    def wrap(x: Any): String = this match
      case Expl => s"($x)"
      case Impl => s"{$x}"
