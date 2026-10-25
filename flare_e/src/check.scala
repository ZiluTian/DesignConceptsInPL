package DSL.flare_e

import DSL.fl._
import DSL.flare.{FlarePrim, FlarePgm, FlareKernelProgram, FlareSugarProgram}
import DSL.flex.{FlexResult, FlexOk, FlexErr}

// Algorithm Z (Figures 16.4, 16.6, 16.8, 16.9): reconstructs the type, effect,
// type-constraint set, and effect-constraint set of a FLARE/E expression. The
// signature is
//
//   Z : Exp -> TypeEnvironment
//           -> (Type x TypeConstraintSet x Effect x EffectConstraintSet)
//
// expressed as recon(e, te) = Right((T, TCS, F, FCS)).
//
// The expressions of FLARE/E are exactly those of FLARE, so the AST, parser,
// desugaring, and syntactic-purity test are all reused from DSL.flare. Only the
// type domain (types now carry latent effects and cell regions) and the
// reconstruction algorithm (which also collects and solves effect constraints)
// are new.

object FlareERecon {

    type ReconResult = (T, List[(T, T)], Eff, List[EffCon])

    def recon(e: Exp, te: Map[String, TS]): Either[String, ReconResult] = e match {

        // ----------------------------------------------------------------
        // Literals, errors, and variable references (Figure 16.6)
        // ----------------------------------------------------------------

        case _: UnitLit   => Right((T.unit, Nil, EPure(), Nil))
        case _: IntLit    => Right((T.int, Nil, EPure(), Nil))
        case _: BoolLit   => Right((T.bool, Nil, EPure(), Nil))
        case _: Sym       => Right((T.symb, Nil, EPure(), Nil))
        // [errorZ]: a fresh type identifier
        case _: ErrorExpr => Right((TVar(FreshE.next()), Nil, EPure(), Nil))

        case Var(name) => te.get(name) match {
            case None => Left(s"unbound identifier: $name")
            // [varZ]: a closed schema is used as-is
            case Some(TSClosed(t)) => Right((t, Nil, EPure(), Nil))
            // [genvarZ]: instantiate a generic schema with fresh description
            // identifiers (and carry its instantiated effect constraints)
            case Some(TSGeneric(bound, body, fcs)) =>
                val sigma = bound.map(b => b -> FreshE.next()).toMap
                val tInst = Rename.t(sigma, body)
                val fcsInst = fcs.map { case EffCon(d, f) =>
                    EffCon(sigma.getOrElse(d, d), Rename.e(sigma, f)) }
                Right((tInst, Nil, EPure(), fcsInst))
        }

        // ----------------------------------------------------------------
        // Compound expressions (Figure 16.6)
        // ----------------------------------------------------------------

        // [ifZ]
        case If(test, th, el) =>
            recon(test, te).flatMap { rt =>
                recon(th, te).flatMap { rh =>
                    recon(el, te).map { re =>
                        val (t1, c1, f1, fc1) = rt
                        val (t2, c2, f2, fc2) = rh
                        val (t3, c3, f3, fc3) = re
                        (t2, c1 ++ c2 ++ c3 ++ List(t1 -> T.bool, t2 -> t3),
                         Eff.maxeff(List(f1, f2, f3)), fc1 ++ fc2 ++ fc3)
                    }
                }
            }

        // [->-introZ]: a fresh type identifier per formal, a fresh latent
        // effect identifier, and the constraint (>= δlat Fbody).
        case Abs(formals, body) =>
            val formalVars = formals.map(_ => TVar(FreshE.next()))
            val teBody = te ++
                formals.zip(formalVars).map { case (n, t) => n -> TSClosed(t) }.toMap
            recon(body, teBody).map { case (tBody, cBody, fBody, fcBody) =>
                val dLat = FreshE.next()
                (TArrow(formalVars, EVar(dLat), tBody), cBody, EPure(),
                 EffCon(dLat, fBody) :: fcBody)
            }

        // [->-elimZ]: a fresh result type and a fresh latent effect, with the
        // constraint T0 = (-> (T1..Tn) δlat δres).
        case MultiApp(rator, rands) =>
            reconAll(rator :: rands, te).map { case (ts, cs, fs, fcs) =>
                val t0 = ts.head
                val tArgs = ts.tail
                val dLat = FreshE.next()
                val dRes = FreshE.next()
                val arrow = TArrow(tArgs, EVar(dLat), TVar(dRes))
                (TVar(dRes), cs ++ List(t0 -> arrow),
                 Eff.maxeff(fs :+ EVar(dLat)), fcs)
            }

        // [primZ]: freshen the operator's schema, then the same constraint
        // pattern as [->-elimZ].
        case FlarePrim(op, args) =>
            TEPrimE.schemas.get(op) match {
                case None => Left(s"unknown primop: $op")
                case Some(schema) =>
                    val (top, fcsTop) = freshenSchema(schema)
                    reconAll(args, te).map { case (ts, cs, fs, fcs) =>
                        val dLat = FreshE.next()
                        val dRes = FreshE.next()
                        val arrow = TArrow(ts, EVar(dLat), TVar(dRes))
                        (TVar(dRes), cs ++ List(top -> arrow),
                         Eff.maxeff(fs :+ EVar(dLat)), fcs ++ fcsTop)
                    }
            }

        // ----------------------------------------------------------------
        // Let polymorphism (Figure 16.8)
        // ----------------------------------------------------------------

        // [letSPZ]: each definition is reconstructed in the OUTER environment
        // (parallel let); zgenPureSP generalizes over the free description
        // identifiers of each definition's type and constraints.
        case Let(binds, body) =>
            reconBinds(binds, te).flatMap { defnResults =>
                val schemas = defnResults.map {
                    case (name, tDef, cDef, _, fcDef, defn) =>
                        name -> zgenPureSP(tDef, te, cDef, fcDef, defn)
                }.toMap
                recon(body, te ++ schemas).map { case (tBody, cBody, fBody, fcBody) =>
                    val cDefns = defnResults.flatMap(_._3)
                    val fDefns = defnResults.map(_._4)
                    val fcDefns = defnResults.flatMap(_._5)
                    (tBody, cBody ++ cDefns,
                     Eff.maxeff(fBody :: fDefns), fcBody ++ fcDefns)
                }
            }

        // [letrecSPZ]: each definition is reconstructed in an environment that
        // also binds every *other* definition to a fresh description variable;
        // the equations δi = Ti tie those variables to the definitions'
        // reconstructed types.
        case LetRec(binds, body) =>
            val deltas = binds.map { case (n, _) => n -> TVar(FreshE.next()) }.toMap
            val teExtended = te ++
                deltas.map { case (n, t) => n -> TSClosed(t) }.toMap
            reconBinds(binds, teExtended).flatMap { defnResults =>
                val cUnion = defnResults.flatMap(_._3)
                val cEqs = defnResults.map { case (name, tDef, _, _, _, _) =>
                    (deltas(name), tDef) }
                val cDefns = cUnion ++ cEqs
                val fcDefns = defnResults.flatMap(_._5)
                val schemas = defnResults.map {
                    case (name, tDef, _, _, fcDef, defn) =>
                        name -> zgenPureSP(tDef, te, cDefns, fcDefns, defn)
                }.toMap
                recon(body, te ++ schemas).map { case (tBody, cBody, fBody, fcBody) =>
                    val fDefns = defnResults.map(_._4)
                    (tBody, cBody ++ cDefns,
                     Eff.maxeff(fBody :: fDefns), fcBody ++ fcDefns)
                }
            }

        case _ =>
            Left("internal error: unexpected expression node in reconstruction")
    }

    // Reconstruct a list of definitions in a common environment.
    private def reconBinds(binds: List[(String, Exp)], te: Map[String, TS]):
        Either[String, List[(String, T, List[(T, T)], Eff, List[EffCon], Exp)]] =
        binds.foldLeft[Either[String,
            List[(String, T, List[(T, T)], Eff, List[EffCon], Exp)]]](Right(Nil)) {
            case (acc, (name, defn)) => acc match {
                case Left(m) => Left(m)
                case Right(accList) =>
                    recon(defn, te).map { case (t, c, f, fc) =>
                        accList :+ (name, t, c, f, fc, defn)
                    }
            }
        }

    // Reconstruct a list of expressions in a common environment.
    private def reconAll(es: List[Exp], te: Map[String, TS]):
        Either[String, (List[T], List[(T, T)], List[Eff], List[EffCon])] =
        es.foldLeft[Either[String,
            (List[T], List[(T, T)], List[Eff], List[EffCon])]](Right((Nil, Nil, Nil, Nil))) {
            case (acc, e) => acc match {
                case Left(m) => Left(m)
                case Right((ts, cs, fs, fcs)) =>
                    recon(e, te).map { case (t, c, f, fc) =>
                        (ts :+ t, cs ++ c, fs :+ f, fcs ++ fc)
                    }
            }
        }

    // Instantiate a primitive's schema with fresh description identifiers.
    private def freshenSchema(ts: TS): (T, List[EffCon]) = ts match {
        case TSClosed(t) => (t, Nil)
        case TSGeneric(bound, body, fcs) =>
            val sigma = bound.map(b => b -> FreshE.next()).toMap
            val tInst = Rename.t(sigma, body)
            val fcsInst = fcs.map { case EffCon(d, f) =>
                EffCon(sigma.getOrElse(d, d), Rename.e(sigma, f)) }
            (tInst, fcsInst)
    }

    // ------------------------------------------------------------------
    // zgen / zgenPureSP (Figure 16.8)
    // ------------------------------------------------------------------

    // zgenPureSP: generalize a definition's algebraic type schema, but only if
    // the definition expression is syntactically pure (Figure 13.25);
    // otherwise keep it monomorphic (closed).
    def zgenPureSP(tDef: T, te: Map[String, TS], tcs: List[(T, T)],
                   fcs: List[EffCon], e: Exp): TS =
        if (DSL.flare.Purity.pure(e)) zgen(tDef, te, tcs, fcs)
        else TSClosed(tDef)

    // zgen: solve the type constraints, apply the substitution to the type and
    // to the effect constraints, and generalize over the description
    // identifiers that are free in the (substituted) type and constraints but
    // not in the (substituted) environment.
    def zgen(t: T, te: Map[String, TS], tcs: List[(T, T)],
             fcs: List[EffCon]): TS =
        UnifyE.solveTCS(tcs) match {
            case UnifyE.Solved(sigma) =>
                val t2 = UnifyE.substT(sigma, t)
                val fcs2 = substitutedFCS(sigma, fcs)
                val freeT = T.freeDescIds(t2)
                val freeF = fcs2.flatMap { case EffCon(d, f) =>
                    Set(d) ++ Eff.freeDescIds(f) }.toSet
                val freeEnv = freeDescIdsTE(sigma, te)
                val gen = (freeT ++ freeF) -- freeEnv
                if (gen.isEmpty) TSClosed(t2)
                else TSGeneric(gen.toList.sortBy(FreshE.order), t2, fcs2)
            case UnifyE.Unsolvable(_) =>
                // The local constraints do not unify; the top-level solve will
                // report the failure. Fall back to a closed type.
                TSClosed(t)
        }

    // Apply σ to an effect-constraint set, keeping only the constraints whose
    // left-hand side is still an effect identifier (ground constraints — whose
    // left-hand side resolved to a base effect — are dropped, as they do not
    // constrain any generalizable identifier).
    private def substitutedFCS(sigma: Map[String, Desc],
                               fcs: List[EffCon]): List[EffCon] =
        fcs.flatMap { case EffCon(d, f) =>
            UnifyE.substEff(sigma, EVar(d)) match {
                case EVar(dv) => Some(EffCon(dv, UnifyE.substEff(sigma, f)))
                case _ => None
            }
        }

    // FrDescIds_tyenv (σ TE): the free description identifiers of the
    // (substituted) type environment.
    private def freeDescIdsTE(sigma: Map[String, Desc],
                              te: Map[String, TS]): Set[String] =
        te.values.flatMap {
            case TSClosed(t) =>
                T.freeDescIds(UnifyE.substT(sigma, t))
            case TSGeneric(bound, body, fcs) =>
                val t2 = UnifyE.substT(sigma, body)
                val fcs2 = substitutedFCS(sigma, fcs)
                (T.freeDescIds(t2) ++
                    fcs2.flatMap { case EffCon(d, f) =>
                        Set(d) ++ Eff.freeDescIds(f) }.toSet) -- bound.toSet
        }.toSet

    // ------------------------------------------------------------------
    // Program reconstruction (Figure 16.9) and display
    // ------------------------------------------------------------------

    // Reconstruct the type and effect of a whole program.
    def reconProgram(p: FlarePgm): FlexResult = {
        FreshE.reset()
        val (formals, bodyExpr) = p match {
            case FlareKernelProgram(formals, body) =>
                (formals, DSL.flare.Desugar(body))
            case FlareSugarProgram(formals, body, defs) =>
                (formals, DSL.flare.Desugar.program(body, defs))
        }
        // A fresh type identifier per formal, bound in the initial environment.
        val tauFormals = formals.map(_ => TVar(FreshE.next()))
        val te0 = formals.zip(tauFormals)
            .map { case (n, t) => n -> TSClosed(t) }.toMap
        recon(bodyExpr, te0) match {
            case Left(m) => FlexErr(m)
            case Right((tBody, tcs, fBody, fcs)) =>
                UnifyE.solveTCS(tcs) match {
                    case UnifyE.Solved(sigmaTCS) =>
                        val sigmaFCS = SolveFCS.solve(fcs, sigmaTCS)
                        // Apply σTCS first, then σFCS (which resolves the
                        // remaining effect identifiers, including in the latent
                        // effects of any procedure types).
                        val f2 = tauFormals.map(t =>
                            UnifyE.substT(sigmaFCS, UnifyE.substT(sigmaTCS, t)))
                        val b2 = UnifyE.substT(sigmaFCS, UnifyE.substT(sigmaTCS, tBody))
                        val fb2 = UnifyE.substEff(sigmaFCS, UnifyE.substEff(sigmaTCS, fBody))
                        FlexOk(showProgramType(f2, fb2, b2))
                    case UnifyE.Unsolvable(failed) =>
                        FlexErr(UnifyE.failureMessage(failed))
                }
        }
    }

    // Display the program type as (=> (Targ*) Fbody Tbody), canonicalizing any
    // remaining free type identifiers to T1, T2, ... and free region
    // identifiers to R1, R2, ... in order of first appearance. (Effect
    // identifiers are all resolved by σFCS, so none remain.) A program with no
    // formals is displayed as (=> () Fbody Tbody).
    private def showProgramType(formals: List[T], bodyEff: Eff, bodyType: T): String = {
        val prog = TArrow(formals, bodyEff, bodyType)
        val (tOrder, rOrder) = collectFreeVars(prog)
        val tMap = tOrder.zipWithIndex.map { case (v, i) => v -> s"T${i + 1}" }.toMap
        val rMap = rOrder.zipWithIndex.map { case (v, i) => v -> s"R${i + 1}" }.toMap
        val psStr = formals.map(t => showT(t, tMap, rMap)).mkString(" ")
        val latStr = showEff(bodyEff, rMap)
        val rStr = showT(bodyType, tMap, rMap)
        s"(=> ($psStr) $latStr $rStr)"
    }

    // Collect the free type identifiers and free region identifiers of a type,
    // each in order of first appearance (a left-to-right depth-first walk).
    private def collectFreeVars(t: T): (List[String], List[String]) = {
        val tOrder = scala.collection.mutable.LinkedHashSet[String]()
        val rOrder = scala.collection.mutable.LinkedHashSet[String]()
        def walkT(t: T): Unit = t match {
            case TVar(v) => tOrder += v
            case TArrow(ps, lat, r) => ps.foreach(walkT); walkEff(lat); walkT(r)
            case TPair(a, b) => walkT(a); walkT(b)
            case TList(e) => walkT(e)
            case TCell(e, reg) => walkT(e); rOrder += reg
            case _ => ()
        }
        def walkEff(e: Eff): Unit = e match {
            case EBase(_, reg) => rOrder += reg
            case EMax(es) => es.foreach(walkEff)
            case _ => ()
        }
        walkT(t)
        (tOrder.toList, rOrder.toList)
    }

    // Display a type, applying the type- and region-identifier maps.
    private def showT(t: T, tMap: Map[String, String],
                      rMap: Map[String, String]): String = t match {
        case TBase(n) => n
        case TVar(v) => tMap.getOrElse(v, v)
        case TArrow(ps, lat, r) =>
            "(-> (" + ps.map(showT(_, tMap, rMap)).mkString(" ") + ") " +
            showEff(lat, rMap) + " " + showT(r, tMap, rMap) + ")"
        case TPair(a, b) =>
            "(pairof " + showT(a, tMap, rMap) + " " + showT(b, tMap, rMap) + ")"
        case TList(e) => "(listof " + showT(e, tMap, rMap) + ")"
        case TCell(e, reg) =>
            "(cellof " + showT(e, tMap, rMap) + " " + rMap.getOrElse(reg, reg) + ")"
    }

    // Display an effect in canonical form: the set of base effects it denotes,
    // sorted by (region, constructor). A single base effect is shown bare;
    // several are wrapped in maxeff; the empty set is shown as pure.
    private def showEff(e: Eff, rMap: Map[String, String]): String = {
        val leaves = baseLeaves(e).distinct
        if (leaves.isEmpty) "pure"
        else {
            val sorted = leaves.sortBy { case (c, reg) => (regionRank(reg, rMap), c) }
            if (sorted.sizeIs == 1) {
                val (c, reg) = sorted.head
                s"($c ${rMap.getOrElse(reg, reg)})"
            } else {
                "(maxeff " +
                    sorted.map { case (c, reg) =>
                        s"($c ${rMap.getOrElse(reg, reg)})" }.mkString(" ") + ")"
            }
        }
    }

    private def baseLeaves(e: Eff): List[(String, String)] = e match {
        case EPure() => Nil
        case EBase(c, reg) => List((c, reg))
        case EVar(_) => Nil
        case EMax(es) => es.flatMap(baseLeaves)
    }

    private def regionRank(reg: String, rMap: Map[String, String]): Int =
        rMap.get(reg).map(_.stripPrefix("R").toInt).getOrElse(0)
}

// Parse and reconstruct the type and effect of a full-FLARE/E program.
def flareReconE(input: String): FlexResult =
    DSL.flare.FlareProgram(input) match {
        case Some(p) => FlareERecon.reconProgram(p)
        case None => FlexErr("parse error")
    }

// Test helpers:  "(flare ...)" shouldFlareEReconTo (FlexOk("(=> () (init R1) (cellof int R1))"))
extension (input: String)
    def shouldFlareEReconTo(expected: FlexResult): Unit = {
        val got = flareReconE(input)
        assert(got == expected, s"expected $expected but got $got for: $input")
    }

// "(flare ...)" shouldFlareEReconFail("unbound")
extension (input: String)
    def shouldFlareEReconFail(prefix: String): Unit = {
        val got = flareReconE(input)
        got match {
            case FlexErr(m) =>
                assert(m.startsWith(prefix),
                    s"expected an error starting with '$prefix' but got '$m' for: $input")
            case FlexOk(t) =>
                throw new AssertionError(s"expected a type error but got FlexOk($t) for: $input")
        }
    }
