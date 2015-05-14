package sav

import org.scalatest._

import scala.reflect.ClassTag

/**
 * Created by gs on 14.05.15.
 */
class AdtSolverSpec extends FlatSpec with BeforeAndAfter {

  private var _currentTestName: String = "<Unset>"
  def currentTestName = _currentTestName
  override protected def runTest(testName: String, reporter: Reporter,
                                  stopper: Stopper, configMap: Map[String, Any],
                                  tracker: Tracker): Unit = {
    _currentTestName = testName
    super.runTest(testName, reporter, stopper, configMap, tracker)
  }

  import types._

  trait FreshSolver {
    val solver = new AdtSolver
    val sig: Signature
    val declaredTypes: Typing = Map()
    val eqs: Seq[(Term, Term)] = Seq()
    val ineqs: Seq[(Term, Term)] = Seq()

    def solve =
      solver.solve(Instance(sig, declaredTypes, eqs, ineqs, Seq(), Seq()))
    def assertSat() =
      solve match {
        case Unsat(reason) =>
          fail(s"Unexpectedly unsat: $reason\n" + solver.dumpTerms())
        case _ => // Ok
      }
    def assertUnsat() =
      solve match {
        case Sat() => fail(s"Unexpectedly sat")
        case _ => // Ok
      }
    def assertUnsatDueTo[T <: UnsatReason]()(implicit ev: ClassTag[T]) =
      solve match {
        case Sat() => fail(s"Unexpectedly sat")
        case Unsat(_: T) => // Ok
        case Unsat(reason) => fail(s"Expected unsat due to $ev, instead got $reason")
      }
  }
  trait SimpleFiniteSig extends FreshSolver {
    val sigFin = Seq(Seq(), Seq()) // Cona, Conb
    val sig = Signature(Seq(sigFin))

    val Fina = Constructor(0,0,List())
    val Finb = Constructor(0,1,List())
  }
  trait FiniteAndListSig extends SimpleFiniteSig {
    val sigList = Seq(Seq(0,1), Seq()) // Cons(Fin, List), Nil
    override val sig = Signature(Seq(sigFin, sigList))

    def Cons(h: Term, t:Term) = Constructor(1,0,List(h,t))
    val Nil = Constructor(1,1,List())
    def Head(cons: Term) = Selector(1,0,0,cons)
    def Tail(cons: Term) = Selector(1,0,1,cons)
  }

  before {
    println(s"== $currentTestName ==")
  }
  after {
    println("")
  }


  "Solver" should "return sat on empty constraints" in new SimpleFiniteSig {
    assertSat()
  }

  it should "return sat on trivial constraints" in new SimpleFiniteSig {
    override val eqs = Seq((Variable(1), Variable(1)))
    assertSat()
  }

  it should "return unsat on trivial inequality" in new SimpleFiniteSig {
    override val ineqs = Seq((Variable(1), Variable(1)))
    assertUnsatDueTo[InvalidEquality]()
  }

  it should "return sat on trivial unification" in new SimpleFiniteSig {
    override val eqs = Seq((Variable(1), Fina) )
    assertSat()
  }

  it should "return unsat on trivially distinct constructors" in new SimpleFiniteSig {
    override val eqs = Seq((Fina, Finb) )
    assertUnsatDueTo[EmptyLabelling]()
  }

  it should "return unsat on simply distinct constructors 1" in new SimpleFiniteSig {
    override val eqs = Seq((Variable(1), Fina), (Variable(1), Finb) )
    assertUnsatDueTo[EmptyLabelling]()
  }
  it should "return unsat on simply distinct constructors 2" in new SimpleFiniteSig {
    override val eqs = Seq((Variable(1), Fina), (Finb, Variable(1)) )
    assertUnsatDueTo[EmptyLabelling]()
  }
  it should "return unsat on simple inequality" in new SimpleFiniteSig {
    override val eqs = Seq((Variable(1), Fina), (Variable(2), Fina) )
    override val ineqs = Seq((Variable(1), Variable(2)))
    assertUnsatDueTo[InvalidEquality]()
  }

  it should "return sat on simple equality" in new SimpleFiniteSig {
    override val eqs = Seq((Variable(1), Fina), (Variable(1), Fina) )
    assertSat()
  }
  it should "return sat on simple equality 2" in new SimpleFiniteSig {
    override val eqs = Seq((Variable(1), Fina),
      (Variable(2), Fina),
      (Variable(1), Variable(2)) )
    assertSat()
  }

  it should "return sat on list equality" in new FiniteAndListSig {
    val x = Variable(1)
    val y = Variable(2)
    override val eqs = Seq( (Cons(x,Nil), Cons(y,Nil)) )
    assertSat()
  }

  it should "return unsat on list inequality" in new FiniteAndListSig {
    val x = Variable(1)
    val y = Variable(2)
    override val eqs = Seq( (Cons(x,Nil), Cons(y,Nil)) )
    override val ineqs = Seq( (x,y) )
    assertUnsatDueTo[InvalidEquality]()
  }

  it should "return unsat on list cycle" in new FiniteAndListSig {
    val x = Variable(1)
    override val eqs = Seq( (Cons(x,Nil), x) )
    assertUnsatDueTo[Cyclic]()
  }

  it should "return sat on list len [_] <= len [_,_]" in new FiniteAndListSig {
    val x = Variable(1)
    override val eqs = Seq( (Cons(Fina,x), Cons(Fina,Cons(Fina,Nil))) )
    assertSat()
  }
  it should "return unsat on list len [_,_] <= len [_]" in new FiniteAndListSig {
    val x = Variable(1)
    override val eqs = Seq( (Cons(Fina,Nil), Cons(Fina,Cons(Fina,x))) )
    assertUnsatDueTo[EmptyLabelling]()
  }

  it should "return unsat on list equality with selectors" in new FiniteAndListSig {
    val x = Variable(1)
    val y = Variable(2)
    override val eqs = Seq( (y, Cons(x,Nil)), (Head(x), y), (Tail(x), Nil) )
    assertSat()
  }
  it should "return unsat on list inequality with selectors" in new FiniteAndListSig {
    val x = Variable(1)
    val y = Variable(2)
    override val eqs = Seq( (Head(x), y), (Tail(x), Nil) )
    override val ineqs = Seq( (y, Cons(x,Nil)) )
    assertUnsatDueTo[InvalidEquality]()
  }

}
