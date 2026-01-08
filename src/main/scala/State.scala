import Common.*
import Core.*

import scala.collection.mutable.ArrayBuffer

object State:
  // metas
  enum MetaEntry:
    case Unsolved(ty: VTy)
    case Solved(value: Val1, ty: VTy)

  private val metas: ArrayBuffer[MetaEntry] = ArrayBuffer.empty
  private var frozen: MetaId = metaId(0)

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
        x: Name,
        tm: Tm0,
        ty: Ty,
        cv: VTy,
        value: Val0,
        vty: VTy,
        vcv: VTy
    )
    case Def1(
        x: Name,
        tm: Tm1,
        ty: Ty,
        value: Val1,
        vty: VTy
    )
    def name: Name = this match
      case Def0(x, _, _, _, _, _, _) => x
      case Def1(x, _, _, _, _)       => x

  private val globals: ArrayBuffer[GlobalEntry] = ArrayBuffer.empty

  def setGlobal(entry: GlobalEntry): Unit = globals += entry
  def getGlobal(x: Name): Option[GlobalEntry] =
    globals.findLast(e => e.name == x)

  def allGlobals: List[GlobalEntry] = globals.toList
