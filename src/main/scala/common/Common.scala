package common

import scala.annotation.targetName

object Common:
  inline def impossible(): Nothing = throw new RuntimeException("impossible")

  type PosInfo = (Int, Int) // (line, col)

  // deBruijn indeces
  opaque type Ix = Int
  inline def ix0: Ix = 0
  inline def mkIx(i: Int): Ix = i
  extension (i: Ix)
    inline def expose: Int = i
    inline def +(o: Int): Ix = i + o
    inline def -(o: Int): Ix = i - o

  // deBruijn levels
  opaque type Lvl = Int
  inline def lvl0: Lvl = 0
  inline def mkLvl(i: Int): Lvl = i
  extension (l: Lvl)
    @targetName("addLvl")
    inline def +(o: Int): Lvl = l + o
    @targetName("subLvl")
    inline def -(o: Int): Lvl = l - o
    inline def <(o: Lvl): Boolean = l < o
    @targetName("exposeLvl")
    inline def expose: Int = l
    inline def toIx(implicit k: Lvl): Ix = k - l - 1

  // names
  case class Name(x: String):
    override def toString: String =
      if !isOperator || (x.head == '(' || x.head == '[') then x else s"($x)"
    inline def isOperator: Boolean = !x.head.isLetter && x.head != '_'
    inline def expose: String = x
    inline def toBind: Bind = DoBind(this)

  object Name:
    val underscore = Name("_")

  enum Bind:
    case DontBind
    case DoBind(name: Name)

    override def toString: String = this match
      case DontBind  => "_"
      case DoBind(x) => x.toString

    def toName: Name = this match
      case DontBind  => Name.underscore
      case DoBind(x) => x
  export Bind.*

  // icit
  enum Icit:
    case Expl
    case Impl

    def wrap(x: Any): String = this match
      case Expl => s"($x)"
      case Impl => s"{$x}"
  export Icit.*

  // pruning
  enum PruneEntry:
    case PESkip
    case PEBind0
    case PEBind1(icit: Icit)
  export PruneEntry.*
  type Pruning = List[PruneEntry]

  opaque type RevPruning = Pruning
  extension (r: RevPruning)
    @targetName("exposeRevPruning")
    inline def expose: Pruning = r
  object RevPruning:
    inline def apply(p: Pruning): RevPruning = p.reverse

  // meta ids
  opaque type MetaId = Int
  inline def metaId(id: Int): MetaId = id
  extension (id: MetaId)
    @targetName("exposeMetaId")
    inline def expose: Int = id
