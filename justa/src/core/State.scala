package core

import common.Common.*
import Value.*
import Syntax.*

import scala.collection.mutable.ArrayBuffer

class State:
  import State.*
  import State.MetaEntry.*

  // metas
  private val metas: ArrayBuffer[MetaEntry] = ArrayBuffer.empty
  private var frozen: MetaId = metaId(0)

  def newMeta(ty: VTy): MetaId =
    val id = metaId(metas.size)
    metas += Unsolved(ty)
    id

  def getMeta(id: MetaId): MetaEntry = metas(id.expose)

  def getMetaUnsolved(id: MetaId): Unsolved = getMeta(id) match
    case u @ Unsolved(_) => u
    case Solved(_, _)    => impossible()

  def unsolvedMetaType(id: MetaId): VTy = getMetaUnsolved(id).ty

  def getMetaSolved(id: MetaId): Solved = getMeta(id) match
    case Unsolved(_)      => impossible()
    case s @ Solved(_, _) => s

  def modifyMeta(id: MetaId)(fn: MetaEntry => MetaEntry): Unit =
    metas(id.expose) = fn(metas(id.expose))

  def solveMeta(id: MetaId, v: Val1): Unit =
    val u = getMetaUnsolved(id)
    metas(id.expose) = Solved(v, u.ty)

  def getMetas(): List[(MetaId, VTy, Option[Val1])] =
    metas.zipWithIndex.collect {
      case (Solved(v, ty), ix) => (metaId(ix), ty, Some(v))
      case (Unsolved(ty), ix)  => (metaId(ix), ty, None)
    }.toList

  def unsolvedMetas(): List[(MetaId, VTy)] =
    metas.zipWithIndex.collect { case (Unsolved(ty), ix) =>
      (metaId(ix), ty)
    }.toList

  def isMetaUnsolved(id: MetaId): Boolean = getMeta(id) match
    case Unsolved(ty)      => true
    case Solved(value, ty) => false

  def freezeMetas(): Unit =
    frozen = metaId(metas.size)

  def isMetaFrozen(id: MetaId): Boolean = id.expose < frozen.expose

  // globals
  private val globals: ArrayBuffer[GlobalEntry] = ArrayBuffer.empty

  def setGlobal(entry: GlobalEntry): Unit = globals += entry
  def getGlobal(x: Name): Option[GlobalEntry] =
    globals.findLast(e => e.name == x)

  def allGlobals: List[GlobalEntry] = globals.toList

object State:
  enum MetaEntry:
    case Unsolved(ty: VTy)
    case Solved(value: Val1, ty: VTy)

  enum GlobalEntry:
    case GlobalEntry0(
        x: Name,
        tm: Tm0,
        ty: Ty,
        cv: CV,
        value: Val0,
        vty: VTy,
        vcv: VTy
    )
    case GlobalEntry1(
        x: Name,
        tm: Tm1,
        ty: Ty,
        value: Val1,
        vty: VTy
    )
    case GlobalEntryNative(x: Name, ty: Ty, vty: VTy)
    def name: Name = this match
      case GlobalEntry0(x, _, _, _, _, _, _) => x
      case GlobalEntry1(x, _, _, _, _)       => x
      case GlobalEntryNative(x, _, _)        => x
