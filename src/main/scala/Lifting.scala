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

  private final class Emit(
      name: Name,
      private val defs: mutable.ArrayBuffer[JVM.Def] = mutable.ArrayBuffer.empty
  ):
    def emit(k: Name => JVM.Def): Name =
      val x = Name(s"${name}$$${defs.size}")
      defs += k(x)
      x

    def toList: List[JVM.Def] = defs.toList

  private final class Supply(var id: LocalName):
    def next(): LocalName =
      val cur = id
      id += 1
      cur

  private type Ren = Map[LocalName, RenEntry]
  private enum RenEntry:
    case RenVar(newname: LocalName)
    case LiftedFun(name: Name, extraParams: List[LocalName])
  import RenEntry.*

  private def liftDef(d: Def): List[JVM.Def] =
    debug(s"liftDef ${d.name}")
    given emit: Emit = new Emit(d.name)
    given Supply = new Supply(0)
    given Ren = renParams(d.ty)
    val value = go(removeLams(d.ty, d.value))
    val retty = goVTy(d.ty.ret)
    val cdef =
      if d.ty.params.isEmpty then JVM.Def.Value(d.name, retty, value)
      else
        val ps = d.ty.params.zipWithIndex.map((ty, ix) => (ix, goVTy(ty)))
        JVM.Def.Function(d.name, ps, retty, value)
    emit.toList ++ List(cdef)

  private def renParams(ty: CTy, ren: Ren = Map.empty)(using
      supply: Supply
  ): Ren =
    @tailrec
    def go(ps: List[VTy], i: Int, ren: Ren): Ren =
      ps match
        case Nil       => ren
        case _ :: rest => go(rest, i + 1, ren + (i -> RenVar(supply.next())))
    go(ty.params, 0, ren)

  private def go(t: Tm)(using
      ren: Ren,
      emit: Emit,
      supply: Supply
  ): JVM.Tm =
    t match
      case Tm.Lam(_, _, _, _) => impossible()
      case Tm.Local(ix, ty) =>
        ren(ix) match
          case RenVar(x) => JVM.Tm.Local(x, goCTy(ty))
          case LiftedFun(_, _) =>
            impossible() // TODO: is this really impossible?
      case Tm.Global(x)      => JVM.Tm.Global(x, Nil)
      case Tm.Prim(p)        => JVM.Tm.Prim(p, Nil)
      case Tm.BoolLit(v)     => JVM.Tm.bool(v)
      case Tm.IntLit(v)      => JVM.Tm.IntLit(v)
      case Tm.If(_, c, t, f) => JVM.Tm.If(go(c), go(t), go(f))

      case Tm.App(_, _) =>
        val (f, a) = t.flattenApps
        f match
          // case Tm.Local(ix, ty) => ??? // TODO: join point or lifted function
          case Tm.Global(x) => JVM.Tm.Global(x, a.map(go))
          case Tm.Prim(p)   => JVM.Tm.Prim(p, a.map(go))
          case _            => impossible()

      case Tm.Let(x, _, CTy(Nil, ty), v, b) =>
        val y = supply.next()
        JVM.Tm.Let(y, goVTy(ty), go(v), go(b)(using ren = ren + (x -> y)))

      case Tm.Let(x, _, ty, v, b) =>
        val freeps = free(v)
        val freen = freeps.size
        val y = emit.emit { y =>
          val ps = freeps.map((x, ty) =>
            (x, goCTy(ty))
          ) ++ ty.params.zipWithIndex.map((ty, x) => (x + freen, goVTy(ty)))
          println(ps)
          val renamed = v
          val body = go(removeLams(ty, renamed))
          JVM.Def.Function(y, ps, goVTy(ty.ret), body)
        }
        // TODO: replace var refs with call to lifted function
        go(b)(using ren = ren + (x -> LiftedFun(y, ???)))
      case Tm.LetRec(x, _, ty, v, b) =>
        ???

  private inline def goCTy(t: CTy): JVM.Ty =
    if t.params.nonEmpty then impossible() else goVTy(t.ret)

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

  private def free(t: Tm): List[(LocalName, CTy)] =
    def merge(
        a: List[(LocalName, CTy)],
        b: List[(LocalName, CTy)]
    ): List[(LocalName, CTy)] =
      (a, b) match
        case (Nil, b)                                         => b
        case (a, Nil)                                         => a
        case (a, (x, ty) :: tl) if a.exists((y, _) => x == y) => merge(a, tl)
        case (a, e :: tl) => merge(a ++ List(e), tl)
    def remove(
        x: LocalName,
        a: List[(LocalName, CTy)]
    ): List[(LocalName, CTy)] =
      a.filterNot((y, _) => x == y)
    t match
      case Tm.Local(ix, ty) => List(ix -> ty)

      case Tm.App(f, a)      => merge(free(f), free(a))
      case Tm.If(_, c, t, f) => merge(free(c), merge(free(t), free(f)))

      case Tm.Lam(x, _, _, b) => remove(x, free(b))

      case Tm.Let(x, _, _, v, b) => merge(free(v), remove(x, free(b)))
      case Tm.LetRec(x, _, _, v, b) =>
        merge(remove(x, free(v)), remove(x, free(b)))

      case _ => Nil
