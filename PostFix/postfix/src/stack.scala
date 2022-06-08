package postfix

import scala.collection.mutable.ListBuffer

class Stack[T]() {
    val stack: ListBuffer[T] = new ListBuffer()

    def push(x: T): Unit = {
        stack.prepend(x)
    }

    def pop(): Option[T] = {
        stack.headOption match {
            case Some(x) => 
                Some(stack.remove(0))
            case _ => None
        }
    }

    override def toString(): String = {
        stack.map(i => i.toString).mkString(", ")
    }
}

class CommandTokenStack extends Stack[CommandToken] {
    def popInt(): Option[Int] = {
        val pop_res: Option[CommandToken] = pop()
        pop_res match {
            case Some(INTEGER(n)) => Some(n)
            case _ => None
        }
    }

    def pushInt(v: Int): Unit = {
        stack.prepend(INTEGER(v))
    }

    def binOp(customBinOp: (Int, Int) => Option[Int]): Option[Unit] = {
        val v1 = popInt()
        val v2 = popInt()
        (v1, v2) match {
            case (Some(x1), Some(x2)) =>
                val ans = customBinOp(x1, x2)
                if (ans.isDefined){
                    Some(pushInt(ans.get))
                } else {
                    None
                }
            case _ => None
        }
    }
}

