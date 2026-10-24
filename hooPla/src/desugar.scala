package DSL.hooPla

import DSL.fl._

// The desugaring function for HOOPLA (Figure 7.23 of the book). It maps
// HOOPLA expressions (HOOK kernel + HOOPLA sugar) to HOOK kernel
// expressions:
//
//   (object)                        -> (null-object)
//   (object E1 Erest*)              -> (compose E1 (object Erest*))
//   (class (Iinit*) Eobject*)       -> (method new (_ Iinit*) (object Eobject*))   { _ fresh }
//   (abs (Iformal*) Ebody)          -> (method call (_ Iformal*) Ebody)            { _ fresh }
//   (E Erand*)                      -> (send call E Erand*)
//   (let ((I E)*) Ebody)            -> ((abs (I*) Ebody) E*)
//   (if Etest Ethen Eelse)          -> (send if-true Etest (abs () Ethen) (abs () Eelse))
//
// The HOOK kernel forms (method, compose, null-object, send) and the
// literals / variable references pass through unchanged (recursing into
// subexpressions).
object Desugar {

    private var counter = 0
    private def fresh(): String = { counter += 1; s"@@hoo_fresh_$counter" }

    def apply(e: Exp): Exp = e match {
        // Literals and variable references: unchanged.
        case e: BoolLit    => e
        case e: IntLit     => e
        case e: Sym        => e
        case e: Var        => e

        // HOOK kernel forms: recurse into subexpressions.
        case MethodExp(m, r, fs, b) => MethodExp(m, r, fs, apply(b))
        case ComposeExp(a, b)       => ComposeExp(apply(a), apply(b))
        case NullObjectExp()        => NullObjectExp()
        case SendExp(m, r, as)      => SendExp(m, apply(r), as.map(apply))

        // HOOPLA sugar forms (Figure 7.23).
        case ObjectExp(Nil)     => NullObjectExp()
        case ObjectExp(e :: es) => ComposeExp(apply(e), apply(ObjectExp(es)))

        case ClassExp(inits, objs) =>
            MethodExp("new", fresh(), inits, apply(ObjectExp(objs)))

        case HooAbsExp(formals, body) =>
            MethodExp("call", fresh(), formals, apply(body))

        case TaglessAppExp(rator, rands) =>
            SendExp("call", apply(rator), rands.map(apply))

        case HooLetExp(binds, body) =>
            // ((abs (I*) Ebody) Edefn*)
            apply(TaglessAppExp(HooAbsExp(binds.map(_._1), body), binds.map(_._2)))

        case HooIfExp(t, th, el) =>
            // (send if-true Etest (abs () Ethen) (abs () Eelse))
            apply(SendExp("if-true", t, List(HooAbsExp(Nil, th), HooAbsExp(Nil, el))))

        // Anything else (should not occur): pass through.
        case e => e
    }
}
