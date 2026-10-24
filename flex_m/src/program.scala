package DSL.flex_m

import DSL.fl._
import DSL.flex._
import scala.util.parsing.combinator._

// Parses FLEX/M concrete syntax (s-expressions) into the FLEX/M AST.
//
// FLEX/M (Chapter 15.2 of the book) is FLEX/SP with first-class modules and
// static dependent types. The concrete syntax (Figure 15.1) is the FLEX/SP
// s-expression kernel extended with
//
//   (module DD* VD*)       a module expression
//   (open Emod Ebody)      a module open
//   (load Y T)             loading a compiled module
//   (match Edisc (PT E)*)  pattern matching (Section 15.4.6)
//
// plus the sugar (Figure 15.2)
//
//   (letrec ((I T E)*) Ebody)   a typed recursive binding (desugars to
//                               (open (module (def I T E)*) Ebody))
//   (mselect I Emod)            module selection (desugars to (open Emod I))
//   (let-type ...), (let-type* ...)
//
// and the program forms
//
//   (flex/Mk ((I T)*) Ebody)
//   (flex/M  ((I T)*) Ebody (def-type τ T)* DD* VD*)
//
// In FLEX/M the pair / list kernel forms (pair, fst, snd, cons, car, cdr,
// null, null?) are NOT keywords: they are ordinary value names (procedures a
// client obtains from a module such as ElistModule). So `null`, `cons`, ...
// parse as variable references in value position, and as constructor /
// literal patterns where the grammar allows.
//
// Type positions are parsed by DSL.flex_m.MT.parse.

object FlexMProgram extends FlLexer {

    // FLEX/M keywords (Figures 15.1 and 15.2) — see Idents.keywords.
    private val keywords = Idents.keywords

    def apply(input: String): Option[FlexMPgm] = {
        parse(sExp, input) match {
            case Success(raw, _) => interpretProgram(raw)
            case _ => None
        }
    }

    def interpretProgram(raw: Raw): Option[FlexMPgm] = raw match {
        case RawList(List(RawAtom("flex/Mk"), formalsRaw, bodyRaw)) =>
            for {
                fs <- typedFormals(formalsRaw)
                body <- interpretExp(bodyRaw)
            } yield FlexMKernelProgram(fs, body)
        case RawList(List(RawAtom("flex/M"), formalsRaw, bodyRaw, items @ _*)) =>
            for {
                fs <- typedFormals(formalsRaw)
                (typeDefs, dts, vds) <- interpretMItems(items.toList)
                body <- interpretExp(bodyRaw)
            } yield FlexMSugarProgram(fs, body, typeDefs, dts, vds)
        case _ => None
    }

    // ------------------------------------------------------------------
    // Expressions
    // ------------------------------------------------------------------

    // The expression-interpretation entry point. It is public because
    // MT.parse (in Type.scala) interprets the module expression of a
    // dependent type constructor (dselect θ Emod) through it.
    def interpretExp(raw: Raw): Option[Exp] = raw match {
        case RawAtom(a) => interpretAtom(a)
        case RawList(items) => interpretList(items)
    }

    // A value position: a literal, or a value identifier (which may not be a
    // keyword). Note that null / cons / car / cdr / ... are value
    // identifiers in FLEX/M (they are not in `keywords`).
    def interpretAtom(a: String): Option[Exp] = {
        if (keywords.contains(a)) None
        else Some(a match {
            case "#u" => UnitLit()
            case "#t" => BoolLit(true)
            case "#f" => BoolLit(false)
            case n if isInt(n) => IntLit(n.toInt)
            case other => Var(other)
        })
    }

    private def isInt(s: String): Boolean = {
        val digits = if (s.nonEmpty && s.head == '-') s.tail else s
        digits.nonEmpty && digits.forall(_.isDigit)
    }

    def interpretList(items: List[Raw]): Option[Exp] = items match {
        case Nil => None
        case RawAtom(k) :: rest if keywords.contains(k) => interpretKeyword(k, rest)
        case RawAtom(a) :: rest if a.startsWith("@") =>
            allOf(rest.map(interpretExp)) map (args => SugaredPrimOp(a.drop(1), args))
        case first :: rest =>
            for {
                rator <- interpretExp(first)
                args <- allOf(rest.map(interpretExp))
            } yield MApp(rator, args)
    }

    def interpretKeyword(k: String, rest: List[Raw]): Option[Exp] = k match {
        // Kernel forms (Figure 15.1).
        case "error" => rest match {
            case List(RawAtom(msg), tRaw) => MT.parse(tRaw) map (MError(msg, _))
            case _ => None
        }
        case "if" => rest match {
            case List(t, th, el) => lift3(interpretExp(t), interpretExp(th), interpretExp(el)) (If(_, _, _))
            case _ => None
        }
        case "prim" => rest match {
            case List(RawAtom(opName), args @ _*) =>
                for {
                    tag <- PrimOpTag.fromName(opName)
                    a <- allOf(args.toList.map(interpretExp))
                } yield PrimOp(tag, a)
            case _ => None
        }
        case "abs" => rest match {
            case List(formalsRaw, body) =>
                for {
                    fs <- typedFormals(formalsRaw)
                    b <- interpretExp(body)
                } yield MAbs(fs, b)
            case _ => None
        }
        // let is a kernel form (the FLEX kernel let, book p.632): bindings are
        // untyped.
        case "let" => rest match {
            case List(bindsRaw, body) =>
                for {
                    bs <- untypedBindings(bindsRaw)
                    b <- interpretExp(body)
                } yield Let(bs, b)
            case _ => None
        }
        case "the" => rest match {
            case List(tRaw, e) =>
                for {
                    t <- MT.parse(tRaw)
                    ex <- interpretExp(e)
                } yield MThe(t, ex)
            case _ => None
        }
        case "sym" => rest match {
            case List(RawAtom(s)) => Some(Sym(s))
            case _ => None
        }
        case "prod" => allOf(rest.map(interpretExp)) map (cs => ProdExp(cs))
        case "get" => rest match {
            // The index must be an integer literal.
            case List(RawAtom(n), e) if isInt(n) =>
                interpretExp(e) map (GetExp(n.toInt, _))
            case _ => None
        }
        case "seq" => allOf(rest.map(interpretExp)) map (cs => SeqExp(cs))
        case "seq-get" => rest match {
            case List(i, s) => lift2(interpretExp(i), interpretExp(s)) (SeqGetExp(_, _))
            case _ => None
        }
        case "seq-size" => unary(rest) (SeqSizeExp(_))
        case "record" => recordFields(rest) map (fs => RecordExp(fs))
        case "select" => rest match {
            case List(nameRaw, e) =>
                for {
                    n <- selectName(nameRaw)
                    ex <- interpretExp(e)
                } yield SelectExp(n, ex)
            case _ => None
        }
        case "with" => rest match {
            case List(rcd, body) => lift2(interpretExp(rcd), interpretExp(body)) (WithExp(_, _))
            case _ => None
        }
        case "one" => rest match {
            case List(tRaw, tagRaw, payload) =>
                for {
                    t <- MT.parse(tRaw)
                    tag <- selectName(tagRaw)
                    p <- interpretExp(payload)
                } yield MOne(t, tag, p)
            case _ => None
        }
        case "tagcase" => rest match {
            case List(discRaw, payloadRaw, clauses @ _*) =>
                // A trailing (else E) clause is optional.
                val (clausesRaw, elseRaw) = clauses.toList match {
                    case Nil => (Nil, None)
                    case init2 :+ last if isElse(last) => (init2, Some(last))
                    case cs => (cs, None)
                }
                val parsedElse: Option[Option[Exp]] = elseRaw match {
                    case Some(raw) => elseBody(raw) map (Some(_))
                    case None => Some(None)
                }
                for {
                    d <- interpretExp(discRaw)
                    pn <- selectName(payloadRaw)
                    cs <- allOf(clausesRaw.map(tagClause))
                    el <- parsedElse
                } yield TagCaseExp(d, pn, cs, el)
            case _ => None
        }
        case "set!" => rest match {
            case List(nameRaw, e) =>
                for {
                    n <- selectName(nameRaw)
                    ex <- interpretExp(e)
                } yield SetExp(n, ex)
            case _ => None
        }
        case "cell" => unary(rest) (CellExp(_))
        case "^" => unary(rest) (DerefExp(_))
        case ":=" => rest match {
            case List(c, e) => lift2(interpretExp(c), interpretExp(e)) (CellSetExp(_, _))
            case _ => None
        }
        case "cell=?" => rest match {
            case List(e1, e2) => lift2(interpretExp(e1), interpretExp(e2)) (CellEqExp(_, _))
            case _ => None
        }

        // Polymorphism (inherited from FLEX/SP, Figure 12.9).
        case "pabs" => rest match {
            case List(varsRaw, body) =>
                typeVars(varsRaw) flatMap { vs =>
                    interpretExp(body) map (MPabs(vs, _))
                }
            case _ => None
        }
        case "pcall" => rest match {
            case List(eRaw, ts @ _*) =>
                for {
                    e <- interpretExp(eRaw)
                    ts2 <- allOf(ts.toList.map(MT.parse))
                } yield MPcall(e, ts2)
            case _ => None
        }

        // FLEX/M module forms (Figure 15.1).
        case "module" => interpretModuleItems(rest.toList) map { case (dts, vds) => MModule(dts, vds) }
        case "open" => rest match {
            case List(emod, body) => lift2(interpretExp(emod), interpretExp(body)) (MOpen(_, _))
            case _ => None
        }
        case "load" => rest match {
            case List(RawAtom(file), tRaw) =>
                MT.parse(tRaw) map (MLoad(file, _))
            case _ => None
        }
        case "match" => rest match {
            case List(disc, clauses @ _*) =>
                for {
                    d <- interpretExp(disc)
                    cs <- allOf(clauses.toList.map(matchClause))
                } yield MMatch(d, cs)
            case _ => None
        }

        // Sugar forms (Figures 15.2 and 6.3 / 11.21).
        case "cond" => interpretCond(rest)
        case "scand" => allOf(rest.map(interpretExp)) map (es => Scand(es))
        case "scor" => allOf(rest.map(interpretExp)) map (es => Scor(es))
        case "begin" => rest match {
            case List(e1, e2) => lift2(interpretExp(e1), interpretExp(e2)) (BeginExp(_, _))
            case _ => None
        }
        case "letrec" => rest match {
            case List(bindsRaw, body) =>
                for {
                    bs <- typedBindings(bindsRaw)
                    b <- interpretExp(body)
                } yield MLetRec(bs, b)
            case _ => None
        }
        case "mselect" => rest match {
            case List(RawAtom(name), emod) if Idents.validValueIdent(name) =>
                interpretExp(emod) map (MMselect(name, _))
            case _ => None
        }
        case "let-type" => rest match {
            case List(bindsRaw, body) =>
                for {
                    bs <- typeBindings(bindsRaw)
                    b <- interpretExp(body)
                } yield MLetType(bs, b)
            case _ => None
        }
        case "let-type*" => rest match {
            case List(bindsRaw, body) =>
                for {
                    bs <- typeBindings(bindsRaw)
                    b <- interpretExp(body)
                } yield MLetTypeStar(bs, b)
            case _ => None
        }
        case _ => None
    }

    private def isElse(raw: Raw): Boolean = raw match {
        case RawList(List(RawAtom("else"), _)) => true
        case _ => false
    }

    private def elseBody(raw: Raw): Option[Exp] = raw match {
        case RawList(List(RawAtom("else"), e)) => interpretExp(e)
        case _ => None
    }

    private def tagClause(raw: Raw): Option[(String, Exp)] = raw match {
        case RawList(List(tagRaw, body)) =>
            for {
                tag <- selectName(tagRaw)
                b <- interpretExp(body)
            } yield (tag, b)
        case _ => None
    }

    def interpretCond(items: List[Raw]): Option[Exp] = {
        val branches = List.newBuilder[(Exp, Exp)]
        var default: Option[Exp] = None
        var err: Option[String] = None
        items.foreach {
            case RawList(List(RawAtom("else"), d)) if default.isEmpty =>
                interpretExp(d) match {
                    case Some(e) => default = Some(e)
                    case None => err = Some("cond: malformed else clause")
                }
            case RawList(List(t, th)) =>
                (interpretExp(t), interpretExp(th)) match {
                    case (Some(te), Some(ee)) => branches += ((te, ee))
                    case _ => err = Some("cond: malformed branch")
                }
            case _ => err = Some("cond: malformed clause")
        }
        err match {
            case Some(_) => None
            case None => Some(Cond(branches.result(), default))
        }
    }

    // ------------------------------------------------------------------
    // Patterns (Section 15.4.6): PT ::= _ | I | L | (I PT*)
    // ------------------------------------------------------------------

    def interpretPattern(raw: Raw): Option[Mpat] = raw match {
        case RawAtom("_") => Some(MpatWild())
        // Literals first (a #u/#t/#f atom or an integer is a literal, and
        // (sym s) is a symbolic literal — `sym` is a keyword, so it is not a
        // constructor pattern head).
        case RawAtom("#u") => Some(MpatLit(UnitLit()))
        case RawAtom("#t") => Some(MpatLit(BoolLit(true)))
        case RawAtom("#f") => Some(MpatLit(BoolLit(false)))
        case RawAtom(n) if isInt(n) => Some(MpatLit(IntLit(n.toInt)))
        case RawList(List(RawAtom("sym"), RawAtom(s))) => Some(MpatLit(Sym(s)))
        // A variable pattern: a value identifier (not a keyword, not a
        // #literal, not a type-constructor name).
        case RawAtom(a) if Idents.validValueIdent(a) && !a.startsWith("#") => Some(MpatVar(a))
        // A constructor pattern (I PT*): I is a value identifier naming a
        // constructor (e.g. `null`, `cons` from an opened list module).
        case RawList(RawAtom(head) :: subs) if Idents.validValueIdent(head) =>
            allOf(subs.toList.map(interpretPattern)) map (ps => MpatCons(head, ps))
        case _ => None
    }

    private def matchClause(raw: Raw): Option[(Mpat, Exp)] = raw match {
        case RawList(List(patRaw, body)) =>
            for {
                p <- interpretPattern(patRaw)
                b <- interpretExp(body)
            } yield (p, b)
        case _ => None
    }

    // ------------------------------------------------------------------
    // Binding lists and formals
    // ------------------------------------------------------------------

    // ((I T)*) — typed formals (program parameters, abs parameters).
    def typedFormals(raw: Raw): Option[List[(String, MT)]] = raw match {
        case RawList(items) =>
            allOf(items.map {
                case RawList(List(RawAtom(name), tRaw)) if Idents.validValueIdent(name) =>
                    MT.parse(tRaw) map (t => name -> t)
                case _ => None
            })
        case _ => None
    }

    // ((I E)*) — untyped let bindings (the FLEX kernel let, book p.632).
    def untypedBindings(raw: Raw): Option[List[(String, Exp)]] = raw match {
        case RawList(items) =>
            allOf(items.map {
                case RawList(List(RawAtom(name), e)) if Idents.validValueIdent(name) =>
                    interpretExp(e) map (ex => name -> ex)
                case _ => None
            })
        case _ => None
    }

    // ((I T E)*) — typed letrec bindings (the FLEX/M letrec sugar).
    def typedBindings(raw: Raw): Option[List[(String, MT, Exp)]] = raw match {
        case RawList(items) =>
            allOf(items.map {
                case RawList(List(RawAtom(name), tRaw, e)) if Idents.validValueIdent(name) =>
                    (MT.parse(tRaw), interpretExp(e)) match {
                        case (Some(t), Some(ex)) => Some((name, t, ex))
                        case _ => None
                    }
                case _ => None
            })
        case _ => None
    }

    // ((τ T)*) — type bindings for let-type / let-type*.
    def typeBindings(raw: Raw): Option[List[(String, MT)]] = raw match {
        case RawList(items) =>
            allOf(items.map {
                case RawList(List(RawAtom(name), tRaw)) if MT.isTypeIdent(name) =>
                    MT.parse(tRaw) map (t => name -> t)
                case _ => None
            })
        case _ => None
    }

    // (I*) — the binder list of a (pabs (τ*) E): a nonempty, duplicate-free
    // list of type identifiers.
    private def typeVars(raw: Raw): Option[List[String]] = raw match {
        case RawList(items) if items.nonEmpty =>
            val vs: List[Option[String]] = items.map {
                case RawAtom(n) if MT.isTypeIdent(n) => Some(n)
                case _ => None
            }
            if (vs.exists(_.isEmpty) || vs.map(_.get).toSet.size != vs.size) None
            else Some(vs.map(_.get))
        case _ => None
    }

    private def recordFields(raws: List[Raw]): Option[List[(String, Exp)]] =
        allOf(raws.map {
            case RawList(List(RawAtom(name), e)) if Idents.validValueIdent(name) =>
                interpretExp(e) map (ex => name -> ex)
            case _ => None
        })

    // A value-identifier position: a name that is not a keyword.
    private def selectName(raw: Raw): Option[String] = raw match {
        case RawAtom(n) if Idents.validValueIdent(n) => Some(n)
        case _ => None
    }

    // ------------------------------------------------------------------
    // Module items (def-datatype / def) and program items
    // ------------------------------------------------------------------

    // A data-type declaration (def-datatype (θ τ*) (Itag Tcomp*)*). The θ is
    // the abstract type-constructor name, τ* are dummy parameter names (their
    // count is the arity; they have no binding power), and each clause is a
    // constructor name with a list of component types.
    def interpretDtItem(raw: Raw): Option[MDtDef] = raw match {
        case RawList(List(RawAtom("def-datatype"), specRaw, clauses @ _*)) =>
            (interpretDtSpec(specRaw), allOf(clauses.toList.map(dtClause))) match {
                case (Some((name, params)), Some(ctors)) =>
                    if (ctors.map(_._1).toSet.size == ctors.size) Some(MDtDef(name, params, ctors))
                    else None
                case _ => None
            }
        case _ => None
    }

    private def interpretDtSpec(raw: Raw): Option[(String, List[String])] = raw match {
        case RawList(RawAtom(name) :: dummies) if MT.isTyConName(name) =>
            val ds: List[Option[String]] = dummies.map {
                case RawAtom(d) if MT.isTypeIdent(d) => Some(d)
                case _ => None
            }
            if (ds.exists(_.isEmpty) || ds.map(_.get).toSet.size != ds.size) None
            else Some(name -> ds.map(_.get))
        case _ => None
    }

    private def dtClause(raw: Raw): Option[(String, List[MT])] = raw match {
        case RawList(RawAtom(tag) :: tsRaw) if Idents.validValueIdent(tag) =>
            allOf(tsRaw.map(MT.parse)) map (ts => tag -> ts)
        case _ => None
    }

    // A value definition (def I T E) inside a module or program.
    def interpretVdItem(raw: Raw): Option[MValDef] = raw match {
        case RawList(List(RawAtom("def"), RawAtom(name), tRaw, e)) if Idents.validValueIdent(name) =>
            for {
                t <- MT.parse(tRaw)
                ex <- interpretExp(e)
            } yield MValDef(name, t, ex)
        case _ => None
    }

    // The value names introduced by a set of module items (the def names, the
    // constructor names, and the implicit deconstructor names ctor~) must all
    // be distinct (book p.896).
    private def distinctValueNames(dts: List[MDtDef], vds: List[MValDef]): Boolean = {
        val all = dts.flatMap(_.ctors.map(_._1)) ++
            dts.flatMap(_.ctors.map(_._1 + "~")) ++
            vds.map(_.name)
        all.toSet.size == all.size
    }

    // (def-datatype ...)* (def I T E)* — the items of a (module ...)
    // expression, in any order.
    def interpretModuleItems(items: List[Raw]): Option[(List[MDtDef], List[MValDef])] = {
        val dts = List.newBuilder[MDtDef]
        val vds = List.newBuilder[MValDef]
        var err: Option[String] = None
        items.foreach { raw =>
            raw match {
                case RawList(RawAtom("def-datatype") :: _) if err.isEmpty =>
                    interpretDtItem(raw) match {
                        case Some(dt) => dts += dt
                        case None => err = Some("malformed def-datatype")
                    }
                case RawList(RawAtom("def") :: _) if err.isEmpty =>
                    interpretVdItem(raw) match {
                        case Some(vd) => vds += vd
                        case None => err = Some("malformed def")
                    }
                case _ if err.isEmpty => err = Some("malformed module item")
                case _ => ()
            }
        }
        err match {
            case Some(_) => None
            case None =>
                val d = dts.result(); val v = vds.result()
                if (distinctValueNames(d, v)) Some((d, v)) else None
        }
    }

    // The program items of a flex/M program (Figure 15.2): def-type /
    // def-datatype / def in any order, normalized to (all def-types first,
    // then all def-datatypes, then all defs), preserving relative order.
    def interpretMItems(items: List[Raw]): Option[(List[(String, MT)], List[MDtDef], List[MValDef])] = {
        val typeDefs = List.newBuilder[(String, MT)]
        val dts = List.newBuilder[MDtDef]
        val vds = List.newBuilder[MValDef]
        var err: Option[String] = None
        items.foreach { raw =>
            raw match {
                case RawList(List(RawAtom("def-type"), RawAtom(name), tRaw)) if err.isEmpty =>
                    if (!MT.isTypeIdent(name)) err = Some(s"illegal type identifier in def-type: $name")
                    else MT.parse(tRaw) match {
                        case Some(t) => typeDefs += (name -> t)
                        case None => err = Some(s"malformed type in def-type: $name")
                    }
                case RawList(RawAtom("def-datatype") :: _) if err.isEmpty =>
                    interpretDtItem(raw) match {
                        case Some(dt) => dts += dt
                        case None => err = Some("malformed def-datatype")
                    }
                case RawList(RawAtom("def") :: _) if err.isEmpty =>
                    interpretVdItem(raw) match {
                        case Some(vd) => vds += vd
                        case None => err = Some("malformed def")
                    }
                case _ if err.isEmpty => err = Some("malformed program item")
                case _ => ()
            }
        }
        err match {
            case Some(_) => None
            case None =>
                val d = dts.result(); val v = vds.result()
                if (distinctValueNames(d, v)) Some((typeDefs.result(), d, v)) else None
        }
    }

    // ------------------------------------------------------------------
    // Option combinators
    // ------------------------------------------------------------------

    private def allOf[A](oas: List[Option[A]]): Option[List[A]] =
        oas.foldRight[Option[List[A]]](Some(Nil)) { (oa, acc) =>
            acc flatMap { as => oa map (_ +: as) }
        }

    private def lift2[A, B, C](oa: Option[A], ob: Option[B])(f: (A, B) => C): Option[C] =
        for {
            a <- oa
            b <- ob
        } yield f(a, b)

    private def lift3[A, B, C, D](oa: Option[A], ob: Option[B], oc: Option[C])(f: (A, B, C) => D): Option[D] =
        for {
            a <- oa
            b <- ob
            c <- oc
        } yield f(a, b, c)

    private def unary(rest: List[Raw])(f: Exp => Exp): Option[Exp] = rest match {
        case List(e) => interpretExp(e) map f
        case _ => None
    }
}
