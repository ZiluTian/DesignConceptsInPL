import mill._, scalalib._

trait DSL extends ScalaModule{
  def scalaVersion = "3.1.2"

  def ivyDeps = Agg(
      ivy"org.scala-lang.modules::scala-parser-combinators:2.1.1",
  )

  object test extends Tests with TestModule.ScalaTest {
    def ivyDeps = Agg(ivy"org.scalatest::scalatest:3.2.12")
  }
}

object postfix extends DSL
object sexp extends DSL
object el extends DSL {
  def moduleDeps = Seq(sexp)
}

