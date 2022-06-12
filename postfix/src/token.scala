package DSL.postfix

sealed trait CommandToken {
    def run(stack: CommandTokenStack): Option[Unit] = {
        Some(stack.push(this))
    }

    def runTimeInstructions(): List[CommandToken] = List()

    def discard(): Unit = {}
}

case class INTEGER(n: Int) extends CommandToken
case object ADD extends CommandToken {
    override def run(stack: CommandTokenStack): Option[Unit] = {
        stack.binOp((x, y) => Some(y + x))
    }
}

case object SUB extends CommandToken {
    override def run(stack: CommandTokenStack): Option[Unit] = {
        stack.binOp((x, y) => Some(y - x))
    }
}

case object MUL extends CommandToken {
    override def run(stack: CommandTokenStack): Option[Unit] = {
        stack.binOp((x, y) => Some(y * x))
    }
}

case object DIV extends CommandToken {
    override def run(stack: CommandTokenStack): Option[Unit] = {
        stack.binOp((x, y) => if (x==0) None else Some(y / x))
    }
}

case object REM extends CommandToken {
    override def run(stack: CommandTokenStack): Option[Unit] = {
        stack.binOp((x, y) => if (x==0) None else Some(y % x))
    }
}

case object EQ extends CommandToken {
    override def run(stack: CommandTokenStack): Option[Unit] = {
        stack.binOp((x, y) => if (y == x) Some(1) else Some(0))
    }
}

case object GT extends CommandToken {
    override def run(stack: CommandTokenStack): Option[Unit] = {
        stack.binOp((x, y) => if (y > x) Some(1) else Some(0))
    }
}

case object LT extends CommandToken {
    override def run(stack: CommandTokenStack): Option[Unit] = {
        stack.binOp((x, y) => if (y < x) Some(1) else Some(0))
    }
}

case object POP extends CommandToken {
    override def run(stack: CommandTokenStack): Option[Unit] = {
        stack.pop() match {
            case Some(x) => Some(x.discard())
            case _ => None
        }
    }
}

case object SWAP extends CommandToken {
    override def run(stack: CommandTokenStack): Option[Unit] = {
        val v1 = stack.pop()
        val v2 = stack.pop()
        (v1, v2) match {
            case (Some(a), Some(b)) =>
                stack.push(a)
                Some(stack.push(b))
            case _ => None
        }
    }
}

case object SEL extends CommandToken {
    override def run(stack: CommandTokenStack): Option[Unit] = {
        val v1 = stack.pop()
        val v2 = stack.pop()
        val v3 = stack.pop()
        (v1, v2, v3) match {
            case (Some(a), Some(b), Some(INTEGER(c))) =>
                Some(if (c==0) stack.push(a) else stack.push(b))
            case _ => None
        }
    }
}

// 1-indexed
case object NGET extends CommandToken {
    override def run(stack: CommandTokenStack): Option[Unit] = {
        val v_index = stack.popInt()
        if (v_index.isDefined){
            val v_index_int = v_index.get - 1 // 1-indexed
            if (stack.stack.isDefinedAt(v_index_int)){
                val v_i = stack.stack(v_index_int)
                v_i match {
                    case INTEGER(k) => Some(stack.push(v_i))
                    case _ => None
                }
            } else {
                None
            }
        } else {
            None
        }
    }
}

case object EXEC extends CommandToken {
    var prependInstructions: List[CommandToken] = List()
    override def run(stack: CommandTokenStack): Option[Unit] = {
        val v1 = stack.pop()
        v1 match {
            case Some(EXECUTABLE(x)) =>
                prependInstructions = x
                Some(v1.get.discard())
            case _ => None
        }
    }

    override def runTimeInstructions(): List[CommandToken] = prependInstructions
}

case class EXECUTABLE(seq: List[CommandToken]) extends CommandToken

