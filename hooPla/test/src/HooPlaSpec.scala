package DSL.hooPla

import org.scalatest.flatspec.AnyFlatSpecLike

class HooPlaSpec extends AnyFlatSpecLike {

    // ------------------------------------------------------------------
    // Parsing
    // ------------------------------------------------------------------

    "A valid HOOK/HOOPLA program" should "parse" in {
        assert(HooPlaProgram("(hoopla () 3)").isDefined)
        assert(HooPlaProgram("(hook () (send + 1 2))").isDefined)
        assert(HooPlaProgram("(hoopla (n) (send + n 40))").isDefined)
        assert(HooPlaProgram("(hoopla () (send call three) (def three (method call () 3)))").isDefined)
        assert(HooPlaProgram("(foo () 3)").isEmpty) // unknown program tag
        assert(HooPlaProgram("(hoopla ()").isEmpty) // malformed s-expression
    }

    // ------------------------------------------------------------------
    // HOOK kernel: method / send / compose (book p.363-366)
    // ------------------------------------------------------------------

    "A method object" should "respond to the message it was created for" in {
        "(hook () (send call (method call () 3)))" shouldHooPlaEvalTo (Nil, HVal(IntObj(3)))
    }

    "FL procedure encodings (p.364)" should "work via defs" in {
        // A procedure's receiver parameter is ignored by convention (_);
        // the send's arguments bind the method's formal parameters.
        "(hook () (send call id #t) (def id (method call (_ x) x)))" shouldHooPlaEvalTo (Nil, HVal(BoolObj(true)))
        "(hook () (send call first 17 #f) (def first (method call (_ y z) y)))" shouldHooPlaEvalTo (Nil, HVal(IntObj(17)))
        "(hook () (send call second 17 #f) (def second (method call (_ y z) z)))" shouldHooPlaEvalTo (Nil, HVal(BoolObj(false)))
    }

    "Integer objects (p.364-365)" should "respond to the numeric messages" in {
        "(hoopla () (send + 2 3))" shouldHooPlaEvalTo (Nil, HVal(IntObj(5)))
        "(hoopla () (send - 2 3))" shouldHooPlaEvalTo (Nil, HVal(IntObj(-1)))
        "(hoopla () (send * 2 3))" shouldHooPlaEvalTo (Nil, HVal(IntObj(6)))
        "(hoopla () (send / 7 2))" shouldHooPlaEvalTo (Nil, HVal(IntObj(3)))
        "(hoopla () (send % 7 3))" shouldHooPlaEvalTo (Nil, HVal(IntObj(1)))
        "(hoopla () (send < 2 3))" shouldHooPlaEvalTo (Nil, HVal(BoolObj(true)))
        "(hoopla () (send = 2 3))" shouldHooPlaEvalTo (Nil, HVal(BoolObj(false)))
        "(hoopla () (send = 2 (send + 1 1)))" shouldHooPlaEvalTo (Nil, HVal(BoolObj(true)))
        // cross-kind comparison returns false (p.373: = uses scand and int?)
        "(hoopla () (send = 2 #t))" shouldHooPlaEvalTo (Nil, HVal(BoolObj(false)))
    }

    "A send to a message the receiver does not handle (p.364)" should "error" in {
        "(hook () (send foo id 17) (def id (method call (x) x)))" shouldHooPlaEvalTo (Nil, HErr("error:no-such-method: foo"))
    }

    "Object composition (p.365)" should "combine method tables, first object wins" in {
        // the book's square5 example
        val prog = """(hook () (send + (send side s5) (send area s5))
                      (def s5 (compose (method side (_) 5)
                                       (method area (_) 25))))"""
        prog shouldHooPlaEvalTo (Nil, HVal(IntObj(30)))
        // same-named messages: the first object's method takes precedence
        "(hook () (send side (compose (method side (_) 1) (method side (_) 2))))" shouldHooPlaEvalTo (Nil, HVal(IntObj(1)))
    }

    "The null object" should "be the identity for compose" in {
        "(hook () (send side (compose (null-object) (method side (_) 9))))" shouldHooPlaEvalTo (Nil, HVal(IntObj(9)))
        "(hook () (send side (compose (method side (_) 9) (null-object))))" shouldHooPlaEvalTo (Nil, HVal(IntObj(9)))
        "(hook () (send foo (null-object)))" shouldHooPlaEvalTo (Nil, HErr("error:no-such-method: foo"))
    }

    // ------------------------------------------------------------------
    // HOOPLA: classes, mixins (book p.366-369)
    // ------------------------------------------------------------------

    "A class (p.369)" should "create instances that respond to its methods" in {
        val prog = """(hoopla () (send area (send new square 9))
                      (def square (class (s)
                                    (method side (self) s)
                                    (method area (self)
                                      (send * (send side self) (send side self))))))"""
        prog shouldHooPlaEvalTo (Nil, HVal(IntObj(81)))
    }

    "Scalable squares: the whole-receiver semantics (p.367)" should "compute area via the composed receiver" in {
        // ss2 = (send scale ss1 2); area is inherited from the square
        // component, and its `self` is the *whole* scaled object, so
        // (send side self) yields 14, not 7.
        val side = """(hoopla () (send side ss2)
                      (def square (class (s)
                                    (method side (self) s)
                                    (method area (self)
                                      (send * (send side self) (send side self)))))
                      (def scalable-square (class (s)
                                    (send new square s)
                                    (method scale (unscaled-self factor)
                                      (object (method side (scaled-self)
                                                    (send * (send side unscaled-self) factor))
                                              unscaled-self))))
                      (def ss2 (send scale (send new scalable-square 7) 2)))"""
        side shouldHooPlaEvalTo (Nil, HVal(IntObj(14)))
        val area = side.replace("(send side ss2)", "(send area ss2)")
        area shouldHooPlaEvalTo (Nil, HVal(IntObj(196)))
    }

    "The color mixin (p.368-369)" should "mix into, and be preserved by, other objects" in {
        val prog = """(hoopla () (send color ss6)
                      (def square (class (s)
                                    (method side (self) s)))
                      (def scalable-square (class (s)
                                    (send new square s)
                                    (method scale (unscaled-self factor)
                                      (object (method side (scaled-self)
                                                    (send * (send side unscaled-self) factor))
                                              unscaled-self))))
                      (def color (class (col)
                                    (method color (self) col)
                                    (method new-color (self new-col)
                                      (object (send new color new-col) self))))
                      (def ss1 (send new scalable-square 7))
                      (def red (send new color (sym red)))
                      (def ss4 (compose red ss1))
                      (def ss5 (send scale ss4 2))
                      (def ss6 (send new-color ss5 (sym blue))))"""
        prog shouldHooPlaEvalTo (Nil, HVal(SymObj("blue")))
        // new-color preserves the side length (p.369)
        val side = prog.replace("(send color ss6)", "(send side ss6)")
        side shouldHooPlaEvalTo (Nil, HVal(IntObj(14)))
        // and scale preserves the color
        val col5 = prog.replace("(send color ss6)", "(send color ss5)")
        col5 shouldHooPlaEvalTo (Nil, HVal(SymObj("red")))
    }

    // ------------------------------------------------------------------
    // The Figure 7.24 sample classes (colored turtles, p.370)
    // ------------------------------------------------------------------

    private val turtleDefs: String =
        """(def point
           (class (init-x init-y)
             (method x (self) init-x)
             (method y (self) init-y)
             (method move (self dx dy)
               (object (send new point
                             (send + (send x self) dx)
                             (send + (send y self) dy))
                       self))))
          (def direction
           (class (init-angle)
             (method angle (self) init-angle)
             (method turn (self delta)
               (object (send new direction
                             (send + (send angle self) delta))
                       self))))
          (def turtle
           (class (x y angle)
             (method home (self)
               (object (send new turtle x y angle)
                       self))
             (send new point x y)
             (send new direction angle)))
          (def color
           (class (col)
             (method color (self) col)
             (method new-color (self new-col)
               (object (send new color new-col) self))))
          (def colored-turtle
           (class (x y angle col)
             (send new turtle x y angle)
             (send new color col)))"""

    private def turtleBody(body: String, extraDefs: String = ""): String =
        s"(hoopla () $body $turtleDefs $extraDefs)"

    "A newly-created turtle (p.370)" should "report its position, angle, and color" in {
        turtleBody("(send x t1)", "(def t1 (send new colored-turtle 0 0 0 (sym green)))") shouldHooPlaEvalTo (Nil, HVal(IntObj(0)))
        turtleBody("(send y t1)", "(def t1 (send new colored-turtle 0 0 0 (sym green)))") shouldHooPlaEvalTo (Nil, HVal(IntObj(0)))
        turtleBody("(send angle t1)", "(def t1 (send new colored-turtle 0 0 0 (sym green)))") shouldHooPlaEvalTo (Nil, HVal(IntObj(0)))
        turtleBody("(send color t1)", "(def t1 (send new colored-turtle 0 0 0 (sym green)))") shouldHooPlaEvalTo (Nil, HVal(SymObj("green")))
    }

    "A rotated and translated turtle (p.370)" should "combine turn and move" in {
        val defs = "(def t1 (send new colored-turtle 0 0 0 (sym green))) (def t2 (send move (send turn t1 45) 17 23))"
        turtleBody("(send x t2)", defs) shouldHooPlaEvalTo (Nil, HVal(IntObj(17)))
        turtleBody("(send y t2)", defs) shouldHooPlaEvalTo (Nil, HVal(IntObj(23)))
        turtleBody("(send angle t2)", defs) shouldHooPlaEvalTo (Nil, HVal(IntObj(45)))
        turtleBody("(send color t2)", defs) shouldHooPlaEvalTo (Nil, HVal(SymObj("green")))
    }

    "A turtle sent home (p.370)" should "return to the origin but keep its color" in {
        val defs = "(def t1 (send new colored-turtle 0 0 0 (sym green))) (def t2 (send move (send turn t1 45) 17 23)) (def t3 (send home t2))"
        turtleBody("(send x t3)", defs) shouldHooPlaEvalTo (Nil, HVal(IntObj(0)))
        turtleBody("(send y t3)", defs) shouldHooPlaEvalTo (Nil, HVal(IntObj(0)))
        turtleBody("(send angle t3)", defs) shouldHooPlaEvalTo (Nil, HVal(IntObj(0)))
        turtleBody("(send color t3)", defs) shouldHooPlaEvalTo (Nil, HVal(SymObj("green")))
    }

    // ------------------------------------------------------------------
    // HOOPLA's FL-like sugar (p.370): abs, let, if, tagless application
    // ------------------------------------------------------------------

    "abs and tagless application" should "encode procedures as objects" in {
        "(hoopla () (let ((f (abs (x y) (send + x y)))) (f 3 4)))" shouldHooPlaEvalTo (Nil, HVal(IntObj(7)))
        "(hoopla () ((abs () 42)))" shouldHooPlaEvalTo (Nil, HVal(IntObj(42)))
    }

    "let over objects (Exercise 7.28 style)" should "bind and use local objects" in {
        val prog = """(hoopla () (let ((ob1 (object (method value (self) 1)))
                                       (ob2 (object (method value (self) 2)))
                                       (ob3 (object (method value (self) 3)
                                                   (method x (self) 4))))
                                  (send + (send value ob3) (send x ob3))))"""
        prog shouldHooPlaEvalTo (Nil, HVal(IntObj(7)))
    }

    "if" should "send if-true to the test and call the chosen thunk" in {
        "(hoopla () (if (send < 1 2) 10 20))" shouldHooPlaEvalTo (Nil, HVal(IntObj(10)))
        "(hoopla () (if (send < 2 1) 10 20))" shouldHooPlaEvalTo (Nil, HVal(IntObj(20)))
    }

    "Boolean objects" should "respond to not, and, and or" in {
        "(hoopla () (send not #t))" shouldHooPlaEvalTo (Nil, HVal(BoolObj(false)))
        "(hoopla () (send and #t (send not #f)))" shouldHooPlaEvalTo (Nil, HVal(BoolObj(true)))
        "(hoopla () (send or #f (send not #t)))" shouldHooPlaEvalTo (Nil, HVal(BoolObj(false)))
    }

    "Symbol objects" should "compare with = and !=" in {
        "(hoopla () (send = (sym a) (sym a)))" shouldHooPlaEvalTo (Nil, HVal(BoolObj(true)))
        "(hoopla () (send = (sym a) (sym b)))" shouldHooPlaEvalTo (Nil, HVal(BoolObj(false)))
        "(hoopla () (send = (sym a) 3))" shouldHooPlaEvalTo (Nil, HVal(BoolObj(false)))
    }

    // ------------------------------------------------------------------
    // Program arguments and errors
    // ------------------------------------------------------------------

    "Program arguments" should "be bound as integer objects" in {
        "(hook (n) (send + n 40))" shouldHooPlaEvalTo (List(2), HVal(IntObj(42)))
    }

    "Arity mismatches" should "return HErr" in {
        // a message to a built-in with the wrong number of arguments
        "(hoopla () (send + 2))" shouldHooPlaEvalTo (Nil, HErr("arity mismatch: '+' expects 1 argument(s), got 0"))
        // a message to a user method with the wrong number of arguments
        "(hoopla () (send call (method call (_ x) x)))" shouldHooPlaEvalTo (Nil, HErr("arity mismatch: method for 'call' expects 1 argument(s), got 0"))
    }

    "An unbound variable" should "return HErr" in {
        "(hoopla () xyz)" shouldHooPlaEvalTo (Nil, HErr("unbound variable: xyz"))
    }

    "A wrong program arity" should "return HErr" in {
        "(hoopla (x y) x)" shouldHooPlaEvalTo (List(1), HErr("expected 2 argument(s), got 1"))
    }
}
