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
object elmm extends DSL {
  def moduleDeps = Seq(sexp)
}
object elm extends DSL {
  def moduleDeps = Seq(sexp)
}
object fl extends DSL {
  def moduleDeps = Seq(sexp)
}
object flic extends DSL {
  def moduleDeps = Seq(sexp, fl)
}
object flavar extends DSL {
  def moduleDeps = Seq(sexp, fl, flic)
}
object hooPla extends DSL {
  def moduleDeps = Seq(sexp, fl)
}
object flex extends DSL {
  def moduleDeps = Seq(sexp, fl)
}
object flex_s extends DSL {
  def moduleDeps = Seq(sexp, fl, flex)
}
object flex_sp extends DSL {
  def moduleDeps = Seq(sexp, fl, flex)
}
object flex_p extends DSL {
  def moduleDeps = Seq(sexp, fl, flex, flex_sp)
}
object flex_spd extends DSL {
  def moduleDeps = Seq(sexp, fl, flex, flex_sp)
}
object flex_spdk extends DSL {
  def moduleDeps = Seq(sexp, fl, flex, flex_sp, flex_spd)
}
object flex_m extends DSL {
  def moduleDeps = Seq(sexp, fl, flex, flex_sp)
}
object flare extends DSL {
  def moduleDeps = Seq(sexp, fl, flex)
}
object flare_e extends DSL {
  def moduleDeps = Seq(sexp, fl, flex, flare)
}
object flare_v extends DSL {
  def moduleDeps = Seq(sexp, fl, flex, flare)
}
object fil extends DSL {
  def moduleDeps = Seq(sexp, fl, flare)
}

