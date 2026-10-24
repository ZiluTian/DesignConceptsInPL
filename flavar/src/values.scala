package DSL.flavar

import DSL.fl._

// FLAVAR's runtime representation of mutable variables (Section 8.4 of the
// book). The principal feature of FLAVARK is that variables, like mutable
// cells, are represented as locations in the store: an environment binding
// associates a name I with a *location* (a VarBox), and the location holds the
// current value. The indirection through the location allows the value
// associated with a name to be changed (set!).

// A mutable variable location: a one-slot container holding a time-dependent
// value. (Contrast with DSL.flic.CellValue, which is a first-class value that
// can be passed around; a VarBox is not a value — it is the thing a name is
// bound to in the environment.)
final class VarBox(var value: Value)

// A lexical environment for FLAVAR: names -> VarBox. Unlike DSL.fl.Env (which
// maps names -> Value directly), every binding here is a location, so a name
// can be reassigned in place by set!.
//
//   lookup     read the current value of a name (late: reads the box)
//   lookupBox  read the location itself (for set!)
//   bindBox    bind a name to a specific location (used when installing defs)
//   update     write a value into the location for a name (create if absent)
//   extended   a new environment with a *fresh* location for a formal
//              parameter, seeded with the argument value (CBV parameter
//              passing, Figure 8.26)
final class FlavarEnv {
    var bindings: Map[String, VarBox] = Map.empty

    def lookupBox(name: String): Option[VarBox] = bindings.get(name)
    def lookup(name: String): Option[Value]     = bindings.get(name).map(_.value)

    def bindBox(name: String, box: VarBox): Unit =
        bindings = bindings.updated(name, box)

    def update(name: String, v: Value): Unit = bindings.get(name) match {
        case Some(box) => box.value = v
        case None      => bindings = bindings.updated(name, new VarBox(v))
    }

    // A fresh location for a new binding (procedure application / shadowing).
    def extended(name: String, v: Value): FlavarEnv = {
        val e = new FlavarEnv(); e.bindings = bindings.updated(name, new VarBox(v)); e
    }
}

// Procedures in FLAVAR capture a FlavarEnv. A FlavarClosure is the value of a
// (lam I E); a FlavarRecClosure is the value of the kernel (rec I E) and
// supports self-reference for recursion.
case class FlavarClosure(formal: String, body: Exp, env: FlavarEnv) extends Proc
case class FlavarRecClosure(name: String, body: Exp, env: FlavarEnv) extends Proc
