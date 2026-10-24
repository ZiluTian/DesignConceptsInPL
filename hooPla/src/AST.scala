package DSL.hooPla

import DSL.fl._
import DSL.sexp._

// AST of HOOK (Humble Object-Oriented Kernel) and HOOPLA (HOOK + syntactic
// sugar), Section 7.3 of the book.
//
// HOOK kernel (Figure 7.22):
//   P ∈ Prog  ::= (hook (Iformal*) Ebody Ddefn*)         [Program]
//   D ∈ Def   ::= (def Iname Edefn)                       [Definition]
//   E ∈ Exp   ::= L                                       [Literal]
//                | I                                       [VariableReference]
//                | (method M (Ireceiver Iformal*) Ebody)   [SimpleObject]
//                | (compose Eobj1 Eobj2)                   [ObjectComposition]
//                | (null-object)                           [NullObject]
//                | (send M Ereceiver Earg*)                 [MessageSend]
//   L ∈ Lit   ::= B | N | (sym Y)
//
// HOOPLA sugar (Figure 7.23):
//   (hoopla (I*) Ebody D*)    program tag (HOOK's is `hook`)
//   (object E*)               object composition of any number of objects
//   (class (Iinit*) Eobject*) an instance-creating object (responds to `new`)
//   (abs (Iformal*) Ebody)    a procedure object (responds to `call`)
//   (E Erand*)                tagless application  -> (send call E Erand*)
//   (let ((I E)*) Ebody)      local binding
//   (if Etest Ethen Eelse)    conditional
//
// Literals (BoolLit / IntLit / Sym), variable references (Var), the program
// nodes (UnsugaredProgram / SugaredProgram), and ValueDef are reused from
// DSL.fl. The desugaring function (Desugar, Figure 7.23) removes the HOOPLA
// sugar; the reference evaluator (Evaluator) interprets the HOOK kernel
// directly. The book instead defines the semantics by a translation into FL
// (Figure 7.25); see the README for the correspondence.

// ---------------------------------------------------------------------------
// HOOK kernel expressions (Figure 7.22)
// ---------------------------------------------------------------------------

// (method M (Ireceiver Iformal*) Ebody) — a simple object: an object that
// responds to the single message M by invoking the method. The receiver
// parameter generalizes Smalltalk's self / Java's this.
case class MethodExp(message: String, receiver: String, formals: List[String], body: Exp) extends INode with Exp {
    label = "Method"
    children = List(SymbolicToken(message)) ++ (receiver +: formals).map(s => SymbolicToken(s)) :+ body
}

// (compose Eobj1 Eobj2) — object composition: the methods of Eobj1 take
// precedence over the (same-named) methods of Eobj2.
case class ComposeExp(obj1: Exp, obj2: Exp) extends INode with Exp {
    label = "Compose"; children = List(obj1, obj2)
}

// (null-object) — the object with no methods; the identity for compose.
case class NullObjectExp() extends SymbolicToken with Exp {
    label = "NullObject"; value = "null-object"
}

// (send M Ereceiver Earg*) — a message send: evaluate the receiver and the
// arguments, look up the method for M in the receiver, and invoke it with
// the receiver and the arguments.
case class SendExp(message: String, receiver: Exp, args: List[Exp]) extends INode with Exp {
    label = "Send"
    children = List(SymbolicToken(message)) :+ receiver :++ args
}

// ---------------------------------------------------------------------------
// HOOPLA sugar expressions (Figure 7.23)
// ---------------------------------------------------------------------------

// (object E*) — compose an arbitrary number of objects (left to right; the
// leftmost object's methods take precedence).
case class ObjectExp(objs: List[Exp]) extends INode with Exp {
    label = "Object"; children = objs
}

// (class (Iinit*) Eobject*) — a class: an object that responds to the single
// message `new` with the arguments Iinit*, creating (object Eobject*).
case class ClassExp(inits: List[String], objs: List[Exp]) extends INode with Exp {
    label = "Class"
    children = INode(inits.map(s => SymbolicToken(s))) :: objs
}

// (abs (Iformal*) Ebody) — a procedure object: an object that responds to
// the message `call` (ignoring its receiver).
case class HooAbsExp(formals: List[String], body: Exp) extends INode with Exp {
    label = "HooAbs"
    children = formals.map(s => SymbolicToken(s)) :+ body
}

// (E Erand*) — a tagless multi-application (the rator is the first element).
case class TaglessAppExp(rator: Exp, rands: List[Exp]) extends INode with Exp {
    label = "TaglessApp"; children = rator :: rands
}

// (let ((I E)*) Ebody) — local (non-recursive) binding.
case class HooLetExp(binds: List[(String, Exp)], body: Exp) extends INode with Exp {
    label = "HooLet"
    children = binds.map { case (n, e) => INode(List(SymbolicToken(n), e)) } :+ body
}

// (if Etest Ethen Eelse) — a conditional (exactly three arguments in HOOPLA).
case class HooIfExp(test: Exp, thenExp: Exp, elseExp: Exp) extends INode with Exp {
    label = "HooIf"; children = List(test, thenExp, elseExp)
}

extension (c: FL)
    def show(): Unit = {
        val printTree = new PrintHooPla()
        c.accept(printTree)
    }
