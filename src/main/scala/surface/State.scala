package surface

import common.Common.*
import core.Core.*

import scala.collection.mutable

class State:
  import State.GlobalEntry

  private val globals: mutable.Map[Name, mutable.ArrayBuffer[GlobalEntry]] =
    mutable.Map.empty

  private def module(mod: Name): mutable.ArrayBuffer[GlobalEntry] =
    globals.get(mod) match
      case None =>
        val a = mutable.ArrayBuffer.empty[GlobalEntry]
        globals += (mod -> a)
        a
      case Some(a) => a

  def addGlobal(mod: Name, entry: GlobalEntry): Unit =
    module(mod) += entry

  def getGlobal(mod: Name, x: Name): Option[GlobalEntry] =
    globals.get(mod) match
      case None    => None
      case Some(a) => a.findLast(e => e.name == x)

object State:
  enum GlobalEntry:
    case GlobalEntry0(
        x: Name,
        tm: Tm0,
        ty: Ty,
        cv: Ty,
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

    def name: Name = this match
      case GlobalEntry0(x, _, _, _, _, _, _) => x
      case GlobalEntry1(x, _, _, _, _)       => x
