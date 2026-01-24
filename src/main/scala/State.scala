import Common.*
import Core.*
import Surface.PiIcit

import scala.collection.mutable

object State:
  // metas
  enum MetaEntry:
    case Unsolved(ty: VTy)
    case Solved(value: Val1, ty: VTy)

  private var metas: mutable.ArrayBuffer[MetaEntry] = mutable.ArrayBuffer.empty
  private var frozen: MetaId = metaId(0)

  private val metaStack: mutable.ArrayBuffer[mutable.ArrayBuffer[MetaEntry]] =
    mutable.ArrayBuffer.empty

  def pushMetas(): Unit = metaStack += metas.clone()
  def discardMetas(): Unit = metaStack.dropRightInPlace(1)
  def rollbackMetas(): Unit =
    metas = metaStack.last
    metaStack.dropRightInPlace(1)

  type PostponedAutoEntry = (Ctx, Tm1, VTy)
  private var postponedAutos: mutable.ArrayBuffer[PostponedAutoEntry] =
    mutable.ArrayBuffer.empty
  private var postponedAutosStack
      : mutable.ArrayBuffer[mutable.ArrayBuffer[PostponedAutoEntry]] =
    mutable.ArrayBuffer.empty

  def postponeAuto(ctx: Ctx, m: Tm1, ty: VTy): Unit =
    postponedAutos += ((ctx, m, ty))

  def getPostponedAutos(): List[PostponedAutoEntry] =
    val l = postponedAutos.toList
    postponedAutos.clear()
    l

  def pushPostponedAutos(): Unit = postponedAutosStack += postponedAutos.clone()
  def discardPostponedAutos(): Unit = postponedAutosStack.dropRightInPlace(1)
  def rollbackPostponedAutos(): Unit =
    postponedAutos = postponedAutosStack.last
    postponedAutosStack.dropRightInPlace(1)

  def newMeta(ty: VTy): MetaId =
    val id = metaId(metas.size)
    metas += MetaEntry.Unsolved(ty)
    id

  def getMeta(id: MetaId): MetaEntry = metas(id.expose)

  def getMetaUnsolved(id: MetaId): MetaEntry.Unsolved = getMeta(id) match
    case u @ MetaEntry.Unsolved(_) => u
    case MetaEntry.Solved(_, _)    => impossible()

  def unsolvedMetaType(id: MetaId): VTy = getMetaUnsolved(id).ty

  def getMetaSolved(id: MetaId): MetaEntry.Solved = getMeta(id) match
    case MetaEntry.Unsolved(_)      => impossible()
    case s @ MetaEntry.Solved(_, _) => s

  def modifyMeta(id: MetaId)(fn: MetaEntry => MetaEntry): Unit =
    metas(id.expose) = fn(metas(id.expose))

  def solveMeta(id: MetaId, v: Val1): Unit =
    val u = getMetaUnsolved(id)
    metas(id.expose) = MetaEntry.Solved(v, u.ty)

  def getMetas(): List[(MetaId, VTy, Option[Val1])] =
    metas.zipWithIndex.collect {
      case (MetaEntry.Solved(v, ty), ix) => (metaId(ix), ty, Some(v))
      case (MetaEntry.Unsolved(ty), ix)  => (metaId(ix), ty, None)
    }.toList

  def unsolvedMetas(): List[(MetaId, VTy)] =
    metas.zipWithIndex.collect { case (MetaEntry.Unsolved(ty), ix) =>
      (metaId(ix), ty)
    }.toList

  def isMetaUnsolved(id: MetaId): Boolean = getMeta(id) match
    case MetaEntry.Unsolved(ty)      => true
    case MetaEntry.Solved(value, ty) => false

  def freezeMetas(): Unit =
    frozen = metaId(metas.size)

  def isMetaFrozen(id: MetaId): Boolean = id.expose < frozen.expose

  // globals
  enum GlobalEntry:
    case Def0(
        pub: Boolean,
        x: Name,
        tm: Tm0,
        ty: Ty,
        cv: Ty,
        value: Val0,
        vty: VTy,
        vcv: VTy
    )
    case Def1(
        pub: Boolean,
        x: Name,
        tm: Tm1,
        ty: Ty,
        value: Val1,
        vty: VTy
    )
    case Data0(
        pub: Boolean,
        x: Name,
        params: List[Name],
        cons: List[Name],
        tm: Tm1,
        ty: Val1,
        unitCon: Option[Name],
        singleCon: Option[Name]
    )
    case Con0(
        pub: Boolean,
        x: Name,
        typarams: List[Name],
        params: List[(Bind, Ty)],
        dx: Name,
        ix: Int,
        tm: Tm1,
        ty: Ty,
        vty: VTy
    )
    case Data1(
        pub: Boolean,
        x: Name,
        params: List[(Name, Icit, Ty)],
        cons: List[Name],
        tm: Tm1,
        ty: Val1,
        unitCon: Option[Name],
        singleCon: Option[Name]
    )
    case Con1(
        pub: Boolean,
        x: Name,
        typarams: List[(Name, Icit, Ty)],
        params: List[(Bind, PiIcit, Ty)],
        dx: Name,
        ix: Int,
        tm: Tm1,
        ty: Ty,
        vty: VTy
    )

    def name: Name = this match
      case Def0(_, x, _, _, _, _, _, _)    => x
      case Def1(_, x, _, _, _, _)          => x
      case Data0(_, x, _, _, _, _, _, _)   => x
      case Con0(_, x, _, _, _, _, _, _, _) => x
      case Data1(_, x, _, _, _, _, _, _)   => x
      case Con1(_, x, _, _, _, _, _, _, _) => x

    def isPublic: Boolean = this match
      case Def0(p, _, _, _, _, _, _, _)    => p
      case Def1(p, _, _, _, _, _)          => p
      case Data0(p, _, _, _, _, _, _, _)   => p
      case Con0(p, _, _, _, _, _, _, _, _) => p
      case Data1(p, _, _, _, _, _, _, _)   => p
      case Con1(p, _, _, _, _, _, _, _, _) => p

  // modules
  private final case class ModuleCtx(
      name: Name,
      modules: mutable.Map[Name, Name] = mutable.Map.empty,
      imports: mutable.Map[Name, (Name, Name)] = mutable.Map.empty
  )

  private val globals: mutable.Map[Name, mutable.ArrayBuffer[GlobalEntry]] =
    mutable.Map.empty

  private val reexports: mutable.Map[Name, mutable.Map[Name, (Name, Name)]] =
    mutable.Map.empty

  private val autos
      : mutable.Map[(Name, Name), mutable.ArrayBuffer[(Name, Name)]] =
    mutable.Map.empty

  private var moduleCtx: Option[ModuleCtx] = None

  def currentModule: Name = moduleCtx.get.name

  def addReexport(
      fromMod: Name,
      fromName: Name,
      targetMod: Name,
      targetName: Name
  ): Unit =
    val map = reexports.get(fromMod) match
      case Some(map) => map
      case None =>
        val map = mutable.Map.empty[Name, (Name, Name)]
        reexports += (fromMod -> map)
        map
    map += (fromName -> (targetMod, targetName))

  private def getReexport(m: Name, x: Name): Option[(Name, Name)] =
    reexports.get(m) match
      case None => None
      case Some(rexs) =>
        rexs.get(x) match
          case None               => None
          case e @ Some((m2, x2)) => getReexport(m2, x2).orElse(e)

  private def module(mod: Name): mutable.ArrayBuffer[GlobalEntry] =
    globals.get(mod) match
      case None =>
        val a = mutable.ArrayBuffer.empty[GlobalEntry]
        globals += (mod -> a)
        a
      case Some(a) => a

  def addGlobal(entry: GlobalEntry): Unit =
    module(currentModule) += entry

  def addAuto(m: Name, x: Name, am: Name, adx: Name): Unit =
    val k = (am, adx)
    val arr = autos.getOrElseUpdate((am, adx), mutable.ArrayBuffer.empty)
    arr += ((m, x))

  def getAutos(m: Name, dx: Name): List[(Name, Name)] =
    autos.get((m, dx)) match
      case None    => Nil
      case Some(a) => a.toList

  def moduleExists(mod: Name): Boolean = globals.contains(mod)
  def moduleHasName(mod: Name, x: Name): Boolean =
    moduleExists(mod) && (globals(mod)
      .findLast(e => e.name == x)
      .isDefined || getReexport(mod, x).isDefined)
  def currentModuleHasName(x: Name): Boolean =
    moduleHasName(currentModule, x)

  def getGlobalDirect(mod: Name, x: Name): Option[GlobalEntry] =
    globals.get(mod) match
      case None    => None
      case Some(a) => a.findLast(e => e.name == x)

  def getGlobal(m: Name, x: Name): Option[(Name, Name, GlobalEntry)] =
    getReexport(m, x) match
      case Some((m2, x2)) => getGlobalDirect(m2, x2).map(e => (m2, x2, e))
      case None           => getGlobalDirect(m, x).map(e => (m, x, e))

  def conIndex(mod: Name, dx: Name, cx: Name): Int =
    getGlobal(mod, dx) match
      case Some((_, _, GlobalEntry.Data0(_, _, _, xs, _, _, _, _))) =>
        xs.indexOf(cx)
      case Some((_, _, GlobalEntry.Data1(_, _, _, xs, _, _, _, _))) =>
        xs.indexOf(cx)
      case _ => impossible()
  inline def conIndex(dx: Name, cx: Name): Int = conIndex(currentModule, dx, cx)

  def allGlobals(): Map[Name, List[GlobalEntry]] =
    globals.mapValues(_.toList).toMap

  def allGlobalsForModule(mod: Name = currentModule): List[GlobalEntry] =
    globals(mod).toList

  def enterModule(mod: Name): Unit =
    moduleCtx = Some(ModuleCtx(mod))
    globals.get(mod) match
      case None => globals += (mod -> mutable.ArrayBuffer.empty[GlobalEntry])
      case _    => ()

  def addModuleRenaming(globalName: Name, innerName: Name): Unit =
    moduleCtx.get.modules += innerName -> globalName

  def hasImport(x: Name): Boolean =
    moduleCtx.get.imports.contains(x)

  def addImport(m: Name, x: Name, r: Name): Unit =
    moduleCtx.get.imports += r -> (m, x)

  def isAccessibleGlobal(m: Name, x: Name): Boolean =
    m == currentModule ||
      moduleCtx.get.imports.values.exists((m2, x2) => m2 == m && x2 == x)

  enum GlobalLookupFailure derives CanEqual:
    case ModuleNotFound
    case GlobalNotFound
    case GlobalIsNotAccessible
  import GlobalLookupFailure.*

  def checkAccessibility(m: Name, x: Name): Boolean =
    getGlobal(m, x) match
      case Some((_, _, e)) => e.isPublic
      case _               => impossible()

  def getGlobal(
      mod: Option[Name],
      px: Name
  ): Either[(Name, Name, GlobalLookupFailure), (Name, Name, GlobalEntry)] =
    val ctx = moduleCtx.get
    def next(m: Name, x: Name) =
      getGlobal(m, x) match
        case None => Left((m, x, GlobalNotFound))
        case Some((m2, x2, e)) =>
          if !(m == ctx.name || e.isPublic) then
            Left((m, x, GlobalIsNotAccessible))
          else Right((m2, x2, e))
    mod match
      case Some(pm) =>
        ctx.modules.get(pm) match
          case None    => Left((pm, px, ModuleNotFound))
          case Some(m) => next(m, px)
      case None =>
        val (m, x) = ctx.imports.getOrElse(px, (ctx.name, px))
        next(m, x)

  // monomorphization
  type MonoEnv = Map[Lvl, IR.VTy]
  private val monomap
      : mutable.Map[(Name, Name, Name), MonoEnv => List[(Bind, IR.VTy)]] =
    mutable.Map.empty

  def setMono(mod: Name, dx: Name, cx: Name)(
      k: MonoEnv => List[(Bind, IR.VTy)]
  ): Unit =
    monomap += ((mod, dx, cx) -> k)

  def getMonoConParams(
      mod: Name,
      dx: Name,
      cx: Name,
      menv: MonoEnv
  ): List[(Bind, IR.VTy)] =
    monomap((mod, dx, cx))(menv)
