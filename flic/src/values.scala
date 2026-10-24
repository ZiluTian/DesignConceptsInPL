package DSL.flic

import DSL.fl._

// A mutable cell (Figure 8.8 of the book): a one-slot container holding a
// time-dependent content. The book writes a cell as loc$val, where loc is a
// natural-number location that uniquely identifies the cell. Cell identity
// (for cell=?) is the location number.
final class CellValue(val loc: Int, var content: Value) extends Value {
    override def toString: String = loc + "$" + FLValue.show(content)
}

object CellValue {
    private var counter: Int = 0
    /** Allocate a fresh cell with the given initial content. */
    def fresh(initial: Value): CellValue = {
        counter += 1
        new CellValue(counter, initial)
    }
}
