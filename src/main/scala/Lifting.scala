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
    case LiftedFun(name: Name, extraArgs: List[(LocalName, CTy)])
  import RenEntry.*

  private def liftDef(d: Def): List[JVM.Def] =
    debug(s"liftDef ${d.name}")
    given emit: Emit = new Emit(d.name)
    given Supply = new Supply(0)
    given Ren = renParams(d.ty)
    given Name = d.name
    val value = go(removeLams(d.ty, d.value), Some(lamTypes(d.value)))
    val retty = goVTy(d.ty.ret)
    val cdef =
      if d.ty.params.isEmpty then JVM.Def.Value(d.name, retty, value)
      else
        val ps = d.ty.params.zipWithIndex.map((ty, ix) => (ix, goVTy(ty)))
        JVM.Def.Function(d.name, ps, retty, value)
    emit.toList ++ List(cdef)

  private inline def renParams(ty: CTy, ren: Ren = Map.empty)(using
      supply: Supply
  ): Ren = renParamsN(ty.params.size, ren)

  @tailrec
  private def renParamsN(n: Int, ren: Ren = Map.empty, start: Int = 0)(using
      supply: Supply
  ): Ren =
    start match
      case _ if start >= n => ren
      case start =>
        renParamsN(n, ren + (start -> RenVar(supply.next())), start + 1)

  // TODO: detect join points
  private def go(t: Tm, toplevel: Option[List[(Int, CTy)]] = None)(using
      ren: Ren,
      emit: Emit,
      supply: Supply,
      defName: Name
  ): JVM.Tm =
    t match
      case Tm.Lam(_, _, _, _) => impossible()
      case Tm.Local(ix, ty) =>
        ren(ix) match
          case RenVar(x)       => JVM.Tm.Local(x, goCTy(ty))
          case LiftedFun(_, _) => impossible()
      case Tm.Global(x)      => JVM.Tm.Global(x, Nil)
      case Tm.Prim(p)        => JVM.Tm.Prim(p, Nil)
      case Tm.BoolLit(v)     => JVM.Tm.bool(v)
      case Tm.IntLit(v)      => JVM.Tm.IntLit(v)
      case Tm.If(_, c, t, f) => JVM.Tm.If(go(c), go(t), go(f))

      case Tm.App(_, _) =>
        val (f, a) = t.flattenApps
        f match
          case Tm.Global(x) => JVM.Tm.Global(x, a.map(a => go(a)))
          case Tm.Prim(p)   => JVM.Tm.Prim(p, a.map(a => go(a)))
          case Tm.Local(ix, ty) =>
            ren(ix) match
              case RenVar(x) => impossible()
              case LiftedFun(x, args) =>
                val extraArgs = args.map((x, ty) => go(Tm.Local(x, ty)))
                JVM.Tm.Global(x, extraArgs ++ a.map(a => go(a)))
          case _ => impossible()

      case Tm.Let(x, _, CTy(Nil, ty), v, b) =>
        val y = supply.next()
        JVM.Tm.Let(
          y,
          goVTy(ty),
          go(v),
          go(b)(using ren = ren + (x -> RenVar(y)))
        )

      case Tm.Let(x, _, ty, v, b) =>
        val freeps = free(v)
        val y = emit.emit { y =>
          val freen = freeps.size
          val ps = freeps.map((x, ty) =>
            (x, goCTy(ty))
          ) ++ ty.params.zipWithIndex.map((ty, x) => (x + freen, goVTy(ty)))
          given Supply = new Supply(0)
          given ren: Ren = renLifted(freeps ++ lamTypes(v))
          given Name = y
          val body = go(removeLams(ty, v))
          JVM.Def.Function(y, ps, goVTy(ty.ret), body)
        }
        go(b)(using ren = ren + (x -> LiftedFun(y, freeps)))

      case Tm.LetRec(x, _, ty, v, b) if shouldNotBeLifted(toplevel, x, b) =>
        val newbody = removeLams(ty, v)
        given Ren = renToplevel(
          lamTypes(v),
          toplevel.get,
          ren + (x -> LiftedFun(defName, Nil))
        )
        go(newbody)
      case Tm.LetRec(x, _, ty, v, b) =>
        val freeps = free(v).filterNot((y, _) => x == y)
        val y = emit.emit { y =>
          val freen = freeps.size
          val ps = freeps.map((x, ty) =>
            (x, goCTy(ty))
          ) ++ ty.params.zipWithIndex.map((ty, x) => (x + freen, goVTy(ty)))
          given Supply = new Supply(0)
          given ren: Ren =
            renLifted(freeps ++ lamTypes(v)) + (x -> LiftedFun(y, freeps))
          given Name = y
          val body = go(removeLams(ty, v))
          JVM.Def.Function(y, ps, goVTy(ty.ret), body)
        }
        go(b)(using ren = ren + (x -> LiftedFun(y, freeps)))

  @tailrec
  private def renLifted(ps: List[(Int, CTy)], ren: Ren = Map.empty)(using
      supply: Supply
  ): Ren =
    ps match
      case Nil            => ren
      case (i, _) :: rest => renLifted(rest, ren + (i -> RenVar(supply.next())))

  private def lamTypes(tm: Tm): List[(Int, CTy)] =
    tm match
      case Tm.Lam(x, _, ty, b) => (x, CTy(ty)) :: lamTypes(b)
      case _                   => Nil

  private def renToplevel(
      lams: List[(Int, CTy)],
      top: List[(Int, CTy)],
      ren: Ren
  ): Ren =
    (lams, top) match
      case ((x, _) :: rest1, (y, _) :: rest2) =>
        renToplevel(rest1, rest2, ren + (x -> RenVar(y)))
      case _ => impossible()

  private def shouldNotBeLifted(
      toplevel: Option[List[(Int, CTy)]],
      x: LocalName,
      body: Tm
  ): Boolean =
    toplevel match
      case Some(ps) =>
        body match
          case Tm.Local(y, _) => x == y
          case Tm.App(_, _) =>
            val (f, args) = body.flattenApps
            f match
              case Tm.Local(y, _) if x == y && args.size == ps.size =>
                ps.zip(args).forall {
                  case ((x, _), Tm.Local(y, _)) => x == y
                  case _                        => false
                }
              case _ => false
          case _ => false
      case _ => false

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
