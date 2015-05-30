//package sav
//
//import org.scalatest._
//
//import scala.reflect.ClassTag
//
///**
// * Created by gs on 14.05.15.
// */
//class AdtSolverDemo extends FlatSpec with BeforeAndAfter {
//
//  private var _currentTestName: String = "<Unset>"
//  def currentTestName = _currentTestName
//  override protected def runTest(testName: String, reporter: Reporter,
//                                  stopper: Stopper, configMap: Map[String, Any],
//                                  tracker: Tracker): Unit = {
//    _currentTestName = testName
//    super.runTest(testName, reporter, stopper, configMap, tracker)
//  }
//
//  before {
//    println(s"== $currentTestName ==")
//  }
//  after {
//    println("")
//  }
//
//  import sav.types._
//
//  trait FreshSolver {
//    val solver = new AdtSolver
//    val sig: Signature
//    val declaredTypes: Typing = Map()
//    val eqs: Seq[(Term, Term)] = Seq()
//    val ineqs: Seq[(Term, Term)] = Seq()
//    val tests: Seq[Tester] = Seq()
//    val negtests: Seq[Tester] = Seq()
//
//    def solve =
//      solver.solve(Instance(sig, declaredTypes, eqs, ineqs, tests, negtests))
//
//    def assertSat(dumpModel: Boolean = false) = {
//      solve match {
//        case Unsat(reason) =>
//          fail(s"Unexpectedly unsat: $reason\n" + solver.dumpTerms())
//        case Sat(model) => // Ok
//          if (dumpModel) {
//            println(s"'Model':")
//            for ((lblOption, terms) <- model; termsSorted = terms.sortBy(solver.termNiceness))
//              println(s"\t$lblOption | ${termsSorted.mkString(" = ")}")
//          }
//      }
//    }
//    def assertUnsat() = {
//      solve match {
//        case Sat(_) => fail(s"Unexpectedly sat")
//        case _ => // Ok
//      }
//    }
//    def assertUnsatDueTo[T <: UnsatReason]()(implicit ev: ClassTag[T]) = {
//      solve match {
//        case Sat(_) => fail(s"Unexpectedly sat")
//        case Unsat(_: T) => // Ok
//        case Unsat(reason) => fail(s"Expected unsat due to $ev, instead got $reason")
//      }
//    }
//  }
//
//
//  trait SimpleFiniteSig extends FreshSolver {
//    val Fina = Constructor(0,0,List())
//    val Finb = Constructor(0,1,List())
//
//    val sigFin = Seq(Seq(), Seq()) // Cona, Conb
//    val sigFinDts = Seq(Seq(), Seq())
//    val sig = Signature(Seq(sigFin), Seq(sigFinDts))
//  }
//
//  trait FiniteAndListSig extends SimpleFiniteSig {
//    def Cons(h: Term, t:Term) = Constructor(1,0,List(h,t))
//    val Nil = Constructor(1,1,List())
//    def Head(cons: Term) = Selector(1,0,0,cons)
//    def Tail(cons: Term) = Selector(1,0,1,cons)
//
//    val sigList = Seq(Seq(0,1), Seq()) // Cons(Fin, List), Nil
//    val sigListDts = Seq(Seq(Fina, Nil), Seq())
//    override val sig = Signature(Seq(sigFin, sigList), Seq(sigFinDts, sigListDts))
//  }
//
//  trait SIntAndIntListSig extends FreshSolver {
//    def Succ(pred: Term) = Constructor(0,0,List(pred))
//    val Zero = Constructor(0,1,List())
//    def Pred(succ: Term) = Selector(0,0,0,succ)
//
//    def Cons(h: Term, t:Term) = Constructor(1,0,List(h,t))
//    val Nil = Constructor(1,1,List())
//    def Head(cons: Term) = Selector(1,0,0,cons)
//    def Tail(cons: Term) = Selector(1,0,1,cons)
//
//    val sigSInt = Seq(Seq(0), Seq()) // Succ(SInt), Zero
//    val sigSIntDts = Seq(Seq(Zero), Seq())
//    val sigList = Seq(Seq(0,1), Seq()) // Cons(SInt, List), Nil
//    val sigListDts = Seq(Seq(Zero, Nil), Seq())
//    override val sig = Signature(Seq(sigSInt, sigList), Seq(sigSIntDts, sigListDts))
//  }
//
//
//  "Solver" should "return sat on list equality" in new FiniteAndListSig {
//    val x = Variable(1)
//    val y = Variable(2)
//    override val eqs = Seq( (Cons(x,Nil), Cons(y,Nil)) )
//    assertSat(true)
//  }
//
//  it should "return unsat on simple inequalityk" in new SimpleFiniteSig {
//    override val eqs = Seq( (Variable(1), Fina), (Variable(2), Fina) )
//    override val ineqs = Seq( (Variable(1), Variable(2)) )
//    assertUnsat()
//  }
////
//  it should "return sat on our example for branching" in new SIntAndIntListSig {
//    //    solver.debugOn
//    val x = Variable(1)
//    val y = Variable(2)
//    val z = Variable(3)
//    override val eqs = Seq( (x, Cons(y, z)) )
//    override val ineqs = Seq( (y, Zero), (Head(z), Zero) )
//    assertSat(true)
//  }
////
//  it should "return unsat on list cycle" in new FiniteAndListSig {
//    val x = Variable(1)
//    override val eqs = Seq( (Cons(x,Nil), x) )
//    assertUnsat()
//  }
////
//  it should "return unsat on longer list cycle" in new FiniteAndListSig {
//    //    solver.debugOn
//    def TailN: (Int, Term) => Term = (n, arg) => n match {
//      case 0 => arg
//      case 1 => Tail(arg)
//      case i => Tail(TailN(i-1, arg))
//    }
//
//    val x = Variable(1)
//    val z = Variable(3)
//    override val eqs = Seq( (TailN(2,z), x), (z, x) )
//    override val tests = Seq( Tester(1,0,z) )
//    assertUnsat()
//  }
//
//}
