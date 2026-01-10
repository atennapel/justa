import Common.*
import IR.*
import Debug.debug

import scala.annotation.tailrec
import scala.collection.mutable

// lift out local functions, create join points, rename with unique names
object Lifting:
  // the passed definitions should be simplified!
  def liftDefs(ds: Defs): JVM.Defs =
    JVM.Defs(ds.toList.flatMap(liftDef))

  private final class Emit(val defs: mutable.ArrayBuffer[JVM.Def])

  private final class Supply(var id: LocalName):
    def next(): LocalName =
      val cur = id
      id += 1
      cur

  private type Ren = Map[LocalName, LocalName]

  private def liftDef(d: Def): List[JVM.Def] =
    debug(s"liftDef ${d.name}")
    given emit: Emit = new Emit(mutable.ArrayBuffer.empty)
    given Supply = new Supply(0)
    given Ren = Map.empty
    // TODO: rename parameters as well!
    val value = go(removeLams(d.ty, d.value))
    val cdef = JVM.Def(d.name, d.ty.params.map(goVTy), goVTy(d.ty.ret), value)
    emit.defs.toList ++ List(cdef)

  private def go(t: Tm)(using Ren, Emit, Supply): JVM.Tm =
    t match
      case Tm.Lam(_, _, _, _)        => impossible()
      case Tm.Local(ix, _)           => ???
      case Tm.Global(x)              => JVM.Tm.Global(x, Nil)
      case Tm.Prim(p)                => JVM.Tm.Prim(p, Nil)
      case Tm.BoolLit(v)             => ???
      case Tm.IntLit(v)              => ???
      case Tm.Let(x, _, ty, v, b)    => ???
      case Tm.LetRec(x, _, ty, v, b) => ???
      case Tm.App(_, _) =>
        val (f, a) = t.flattenApps
        ???
      case Tm.If(_, c, t, f) => JVM.Tm.If(go(c), go(t), go(f))

  private def goVTy(t: VTy): JVM.Ty =
    t match
      case VTy.Bool => JVM.Ty.Bool
      case VTy.Int  => JVM.Ty.Int

  private def removeLams(ty: CTy, t: Tm): Tm =
    @tailrec
    def go(n: Int, t: Tm): Tm =
      (n, t) match
        case (n, Tm.Lam(_, _, _, b)) if n > 0 => go(n - 1, b)
        case (0, tm)                          => tm
        case _                                => impossible()
    go(ty.params.size, t)
