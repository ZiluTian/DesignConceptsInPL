package DSL.fil

import DSL.fl._

// A mutable product (Figure 17.14 of the book): a store location with a
// fixed number of component slots. It is created by the mprod primop (a
// fresh location, one slot per argument), its slots are read by the indexed
// primop (mget J) and written by (mset! J) (which yields unit), and two
// products are equal (mprod=?) iff they are the same location in the store.
//
// FIL has no cells and no pairs: a cell is a one-slot mutable product and a
// pair is a two-slot one (footnote 4, page 1032). As with DSL.flic's
// CellValue, the location number is an allocation-order counter; tests must
// therefore assert on values fetched through (mget J), never on the location
// itself.
final class MProdValue(val loc: Int, var slots: Array[Value]) extends Value {
    override def toString: String =
        "mprod@" + loc + "(" + slots.map(FLValue.show).mkString(", ") + ")"
}

object MProdValue {
    private var counter: Int = 0
    /** Allocate a fresh mutable product with the given initial slots. */
    def fresh(initial: List[Value]): MProdValue = {
        counter += 1
        new MProdValue(counter, initial.toArray)
    }
}

// A FIL procedure value: an abstraction with a (possibly empty) list of
// formal parameters, capturing the environment in which it was created.
// (FL's Closure has exactly one formal; FIL's abs is multi-formal.) FIL has
// no (rec ...) or letrec form, so there is no recursive-closure value: the
// "knot-tying" of recursion is performed by writing closures into the slots
// of mutable products (the letrec translation in Translate.scala).
final case class FilClosure(formals: List[String], body: Exp, env: Env) extends Proc

object FilValue {
    // Render a runtime value in the book's outcome notation (an extension of
    // FL's: a mutable product displays its location and slots).
    def show(v: Value): String = v match {
        case mp: MProdValue => mp.toString
        case other          => FLValue.show(other)
    }
}
