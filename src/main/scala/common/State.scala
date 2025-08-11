package common

import common.Common.*
import core.Core.*

import scala.collection.mutable

object State:
  enum GlobalEntry:
    case Def0(
        public: Boolean,
        x: Name,
        tm: Tm0,
        ty: Ty,
        cv: Ty,
        value: Val0,
        vty: VTy,
        vcv: VTy
    )
    case Def1(
        public: Boolean,
        x: Name,
        tm: Tm1,
        ty: Ty,
        value: Val1,
        vty: VTy
    )
    case Primitive(
        public: Boolean,
        x: Name,
        ty: Ty,
        vty: VTy
    )
    case Data(
        kind: DataKind,
        public: Boolean,
        x: Name,
        cons: List[Name],
        tm: Tm1,
        ty: Val1,
        unitCon: Option[Name]
    )
    case DataCon(
        kind: DataKind,
        public: Boolean,
        x: Name,
        params: List[(Bind, Ty, VTy)],
        dx: Name,
        ix: Int,
        tm: Tm1,
        ty: Ty,
        vty: VTy
    )

    def name: Name = this match
      case Def0(_, x, _, _, _, _, _, _)       => x
      case Def1(_, x, _, _, _, _)             => x
      case Primitive(_, x, _, _)              => x
      case Data(_, _, x, _, _, _, _)          => x
      case DataCon(_, _, x, _, _, _, _, _, _) => x

    def isPublic: Boolean = this match
      case Def0(p, _, _, _, _, _, _, _)       => p
      case Def1(p, _, _, _, _, _)             => p
      case Primitive(p, _, _, _)              => p
      case Data(_, p, _, _, _, _, _)          => p
      case DataCon(_, p, _, _, _, _, _, _, _) => p

  private final case class ModuleCtx(
      name: Name,
      modules: mutable.Map[Name, Name] = mutable.Map.empty,
      imports: mutable.Map[Name, (Name, Name)] = mutable.Map.empty
  )

  private val globals: mutable.Map[Name, mutable.ArrayBuffer[GlobalEntry]] =
    mutable.Map.empty

  private var moduleCtx: Option[ModuleCtx] = None

  def currentModule: Name = moduleCtx.get.name

  private def module(mod: Name): mutable.ArrayBuffer[GlobalEntry] =
    globals.get(mod) match
      case None =>
        val a = mutable.ArrayBuffer.empty[GlobalEntry]
        globals += (mod -> a)
        a
      case Some(a) => a

  def addGlobal(entry: GlobalEntry): Unit =
    module(currentModule) += entry

  def moduleExists(mod: Name): Boolean = globals.contains(mod)
  def moduleHasName(mod: Name, x: Name): Boolean =
    moduleExists(mod) && globals(mod).findLast(e => e.name == x).isDefined
  def currentModuleHasName(x: Name): Boolean =
    moduleHasName(currentModule, x)

  def getGlobal(mod: Name, x: Name): Option[GlobalEntry] =
    globals.get(mod) match
      case None    => None
      case Some(a) => a.findLast(e => e.name == x)

  def enterModule(mod: Name): Unit =
    moduleCtx = Some(ModuleCtx(mod))

  def addModuleRenaming(globalName: Name, innerName: Name): Unit =
    moduleCtx.get.modules += innerName -> globalName

  def addImport(m: Name, x: Name, r: Name): Unit =
    moduleCtx.get.imports += r -> (m, x)

  enum GlobalLookupFailure:
    case ModuleNotFound
    case GlobalNotFound
    case GlobalIsNotAccessible
  import GlobalLookupFailure.*

  def checkAccessibility(m: Name, x: Name): Boolean =
    getGlobal(m, x) match
      case None    => true
      case Some(e) => e.isPublic

  def getGlobal(
      mod: Option[Name],
      px: Name
  ): Either[(Name, Name, GlobalLookupFailure), (Name, GlobalEntry)] =
    val ctx = moduleCtx.get
    def next(m: Name, x: Name) =
      getGlobal(m, x) match
        case None    => Left((m, x, GlobalNotFound))
        case Some(e) =>
          if !(m == ctx.name || e.isPublic) then
            Left((m, x, GlobalIsNotAccessible))
          else Right((m, e))
    mod match
      case Some(pm) =>
        ctx.modules.get(pm) match
          case None    => Left((pm, px, ModuleNotFound))
          case Some(m) => next(m, px)
      case None =>
        val (m, x) = ctx.imports.getOrElse(px, (ctx.name, px))
        next(m, x)
