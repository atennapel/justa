import scala.annotation.targetName
import scala.collection.mutable

object Common:
  inline def impossible(): Nothing =
    throw new RuntimeException("impossible")

  final case class PosInfo(line: Int, column: Int): // 1-based
    override def toString: String = s"$line:$column"
    def subCol(n: Int): PosInfo = PosInfo(line, column - n)
  object PosInfo:
    def start: PosInfo = PosInfo(1, 1)

  // debruijn indeces
  opaque type Ix = Int
  inline def ix0: Ix = 0
  inline def mkIx(i: Int): Ix = i
  extension (i: Ix)
    @targetName("exposeIx")
    inline def expose: Int = i
    @targetName("addIx")
    inline def +(o: Int): Ix = i + o
    @targetName("subIx")
    inline def -(o: Int): Ix = i - o

  // debruijn levels
  opaque type Lvl = Int
  inline def lvl0: Lvl = 0
  inline def mkLvl(i: Int): Lvl = i
  extension (l: Lvl)
    @targetName("exposeLvl")
    inline def expose: Int = l
    @targetName("addLvl")
    inline def +(o: Int): Lvl = l + o
    @targetName("subLvl")
    inline def -(o: Int): Lvl = l - o
    @targetName("ltLvl")
    inline def <(o: Lvl): Boolean = l < o
    inline def toIx(using k: Lvl): Ix = k - l - 1

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

    def toBind: Bind = Bind.DoBind(this)

  object Name:
    private val namestore: mutable.Map[String, Name] = mutable.Map.empty
    private val opstore: mutable.Map[String, Name] = mutable.Map.empty
    def apply(name: String): Name = namestore.getOrElseUpdate(name, Nm(name))
    def op(name: String): Name = opstore.getOrElseUpdate(name, Op(name))
    val Underscore = Name("_")

  type Assoc[T] = List[(Name, T)]

  enum Bind:
    case DontBind
    case DoBind(name: Name)

    override def toString: String = this match
      case DontBind  => "_"
      case DoBind(x) => x.toString

    def toName: Name = this match
      case DontBind  => Name.Underscore
      case DoBind(x) => x

    def toOption: Option[Name] = this match
      case DontBind  => None
      case DoBind(x) => Some(x)

    def orElse(b: Bind): Bind = this match
      case DontBind  => b
      case DoBind(_) => this
  object Bind:
    def fromString(x: String): Bind =
      if x.startsWith("_") then Bind.DontBind else Bind.DoBind(Name(x))

  // icit
  enum Icit:
    case Expl
    case Impl

    def wrap(x: Any): String = this match
      case Expl => s"($x)"
      case Impl => s"{$x}"

  // pruning
  enum PruneEntry:
    case Skip
    case Bind0
    case Bind1(icit: Icit)
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

  // primitives
  enum Primitive:
    case Meta
    case Type
    case CV
    case Comp
    case Val

    case Bool
    case True
    case False

    case Int
    case Lt
    case Add
    case Sub
    case Mul

    case IO
    case ReturnIO
    case BindIO

    override def toString: String = this match
      case Meta     => "meta"
      case Type     => "type"
      case CV       => "cv"
      case Comp     => "comp"
      case Val      => "val"
      case Bool     => "Bool"
      case True     => "True"
      case False    => "False"
      case Int      => "Int"
      case Lt       => "lt"
      case Add      => "add"
      case Sub      => "sub"
      case Mul      => "mul"
      case IO       => "IO"
      case ReturnIO => "returnIO"
      case BindIO   => "bindIO"

  enum RuntimePrimitive:
    case Lt
    case Add
    case Sub
    case Mul

    override def toString: String = this match
      case Lt  => "lt"
      case Add => "add"
      case Sub => "sub"
      case Mul => "mul"
