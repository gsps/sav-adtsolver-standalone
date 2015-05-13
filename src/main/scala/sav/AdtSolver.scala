package sav

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

/**
 * Created by gs on 24.04.15.
 */
class AdtSolver() {
  type Index      = Int
  type CtorRef    = Int
  type SortRef    = Int
  type TermRef    = Int
  type CtorRefSet = mutable.BitSet
  type ConstId    = Int
  type Labels     = Option[(SortRef, CtorRefSet)]
  type Typing     = Map[Term, SortRef]

  // TODO: Consider special case of a single sort with a single constructor,
  //  that is, labels(t) == None -- which then is the implicit representation of
  //  labels(t) == {the single constructor} -- might allow rule Instantiate 2
  //  (and others?).

  case class Instance(sig: Signature,
                      declaredTypes: Typing, // FIXME: Redundant b/c of tests!
                      eqs: Seq[(Term, Term)], ineqs: Seq[(Term, Term)],
                      tests: Seq[Tester], negtests: Seq[Tester]) {
    def allTopLevelTerms =
      (eqs ++ ineqs).foldLeft(Seq[Term]()){
        case (seq, (s, t)) => s +: t +: seq
      } ++ (tests ++ negtests).foldLeft(Seq[Term]()){
        case (seq, Tester(_, _, t)) => t +: seq
      }
  }
  case class Signature(sorts: Seq[Seq[Seq[SortRef]]]) {
    require(sorts forall { ctors =>
      ctors forall { args =>
        args forall sortRefs.contains
      }
    })

    val sortRefs: Set[SortRef] = (0 until sorts.size).toSet
    def ctorRefs(sort: SortRef): CtorRefSet = {
      // sort \in sortRefs
      val ctors = (0 until sorts(sort).size).toSet
      newCtorRefSet(ctors)
    }
    def argIndices(sort: SortRef, ctor: CtorRef): Set[Index] = {
      // sort \in sortRefs, ctor in \in ctorRefs(sort)
      (0 until sorts(sort)(ctor).size).toSet
    }
    def argSort(sort: SortRef, ctor: CtorRef, index: Index): SortRef = {
      // sort \in sortRefs, ctor in \in ctorRefs(sort),
      //  index \in argIndices(sort, ctor)
      sorts(sort)(ctor)(index)
    }

    def isFiniteCtor(sort: SortRef, ctor: CtorRef): Boolean = ???

    def designatedTerm(sort: SortRef, ctor: CtorRef): TermRef = ???
  }

  sealed abstract class Term {
    def isAtomic = false
    def subTerms = Seq[Term]()
    // FIXME: Is forming the closure via termRefs a bad idea?
    def ref = termRefs.get(this).head
//    def rep = representative(ref)
  }
  case class Variable() extends Term { override def isAtomic = true }
  case class Constant(constId: ConstId) extends Term { override def isAtomic = true }
  case class Constructor(sort: SortRef, ctor: CtorRef,
                         args: List[Term]) extends Term {
    override def subTerms = args.toSeq
  }
  case class Selector(sort: SortRef, ctor: CtorRef,
                      index: Index, arg: Term) extends Term {
    override def subTerms = Seq(arg)
  }

  case class Tester(sort: SortRef, ctor: CtorRef, arg: Term)

//  sealed abstract class ITerm()
//  case class IVariable() extends ITerm
//  abstract class Term { def data: TermData }
  //  case class ETerm(data: TermData)
  //  case class ITerm(id: TermRef, data: TermData) extends Term
  //  sealed abstract class TermData
  //  case class Variable() extends TermData
  //  case class Constant() extends TermData
  //  case class Selector(sort: SortRef, index: Int, arg: Term) extends TermData
  //  case class Constructor(sort: SortRef, args: List[Term]) extends TermData
//  protected case class ITerm(id: TermRef, data: Term)

  // Invariant: size of {terms, eqClass[Siz]es, labels} == nextTermId
  protected var nextTermId: TermRef

  protected var sig: Signature
  protected var declaredTypes: Typing

  protected val terms         = new ArrayBuffer[Term]
  protected val termRefs      = new mutable.HashMap[Term, TermRef]

  protected val eqClasses     = new ArrayBuffer[TermRef]
  protected val eqClassSizes  = new ArrayBuffer[Int]
  protected val eqClassConsts = new ArrayBuffer[Option[ConstId]]
  protected val labels        = new ArrayBuffer[Labels]

  // NOTE: On the right data structure for edge lists:
  //  We operate on these edge lists in two ways,
  //    a) we iterate over them (in no particular order), and
  //    b) we merge them (when merging equivalence classes and thus the
  //        representatives' data structures, incl. edge lists).
  //  TODO: Thus, use linked lists (which can be merged in O(n)).
  // ^^ Disregard this.
  protected val outEdges      = new ArrayBuffer[ArrayBuffer[TermRef]]
  protected val inEdges       = new ArrayBuffer[mutable.HashSet[TermRef]]
  protected val sources       = new mutable.HashSet[TermRef]
  protected val sinks         = new mutable.HashSet[TermRef]
  protected val sharedSets    = new ArrayBuffer[mutable.HashSet[Index]]

  protected val selectorsOf = new mutable.HashMap[TermRef, mutable.HashSet[Selector]]
    .withDefault(_ => new mutable.HashSet[Selector])
  protected val ctorFound     = new mutable.HashSet[TermRef]
  protected val instantiated  = new mutable.HashSet[TermRef]

  protected def newCtorRefSet(sorts: Set[CtorRef]): CtorRefSet = {
    new mutable.BitSet(sorts map (_.toLong) toArray)
  }

  protected def resetInternalState(): Unit = {
    nextTermId = 0

    sig = null
    declaredTypes = null

    terms.clear()
    termRefs.clear()

    eqClasses.clear()
    eqClassSizes.clear()
    eqClassConsts.clear()
    labels.clear()

    outEdges.clear()
    inEdges.clear()
    sources.clear()
    sinks.clear()
    sharedSets.clear()

//    selectorsOf.clear()
//    instantiated.clear() // Why is this commented out???
    ctorFound.clear()
  }

  protected def allTermRefs: Seq[TermRef] = (0 until nextTermId).toSeq

  protected def getOrCreateTermRef(term: Term): TermRef =
    termRefs.getOrElse(term, {registerTerm(term)})

  protected def registerTerm(term: Term): TermRef = {
    if (termRefs contains term)
      return termRefs(term)

    val subTerms    = term.subTerms
    val subTermRefs = subTerms map registerTerm

    val id = nextTermId
    terms(id)         = term
    termRefs(term)    = id
    eqClasses(id)     = id
    eqClassSizes(id)  = 1
    eqClassConsts(id) = term match {
      case Constant(constId)  => Some(constId)
      case _                  => None
    }

    term match {
      case Constructor(sort, ctor, _) =>
        labels(id) = Some((sort, newCtorRefSet(Set(ctor))))
      case term @ Selector(sort, ctor, index0, arg) =>
//        labels(id) = None // overwritten below
//        // NOTE: Here we also create (& register) selector terms for all
//        //  other argument positions of (sort, ctor)!
//        sig.argIndices(sort, ctor) foreach { index =>
//          val sel     = Selector(sort, ctor, index, arg)
//          val selRef  = getOrCreateTermRef(sel)
//          val argSort = sig.argSort(sort, ctor, index)
//          label(selRef, argSort, sig.ctorRefs(argSort))
//        }
        val argSort = sig.argSort(sort, ctor, index0)
        label(id, argSort, sig.ctorRefs(argSort))
        val selectee = subTermRefs.head
        selectorsOf.getOrElseUpdate(selectee, selectorsOf(selectee)).add(term)
      case _ =>
        declaredTypes.get(term) match {
          case Some(sort) =>
            labels(id) = Some((sort, sig.ctorRefs(sort)))
          case None =>
            labels(id) = None // meaning "of any sort and ctor"
        }
    }
    // Is the term's ctor now unambiguous?
    labels(id) match {
      case Some((_, ctors)) if ctors.size == 1 =>
        ctorFound.add(id)
    }

    val out = new ArrayBuffer[TermRef]()
    outEdges(id) = out
    term match {
      case _: Constructor =>
        out.sizeHint(subTerms.size)
        subTermRefs foreach { subRef =>
          out.append(subRef)
          inEdges(subRef).add(id)
        }
    }
    inEdges(id) = new mutable.HashSet[TermRef]()

    nextTermId += 1
    id
  }

  protected def representative(ref: TermRef): TermRef = {
    var _ref = ref
    // TODO: Can we optimize this once fast union-find is implemented?
    while (eqClasses(_ref) != _ref) {
      _ref = eqClasses(_ref)
    }
    _ref
  }

  protected def ctorOf(ref: TermRef): Option[(SortRef, CtorRef)] = {
    labels(ref) match {
      case None => None
      case Some((_, ctors)) if ctors.size != 1 => None
      case Some((sort, ctors)) => Some((sort, ctors.head))
    }
  }

//  protected def _arrayBufferPop[A](buf: ArrayBuffer[A]): A = {
//    // Make-shift pop():
//    val x = buf(buf.size - 1)
//    buf.reduceToSize(buf.size - 1)
//    x
//  }

  protected def pathExists(from: TermRef, to: TermRef): Boolean = {
    // TODO: Substitute with some efficient data structure + algorithm
    val work = new mutable.ArrayStack[TermRef]()
    work.push(from)
    while (work.nonEmpty) {
      val t = work.pop()
      if (t == to)
        return true
      work ++= outEdges(t)
    }
    false
  }

  protected def _topoTerms(initial: mutable.HashSet[TermRef],
                           edges: ArrayBuffer[Iterable[TermRef]],
                           backEdges: ArrayBuffer[Iterable[TermRef]],
                           f: (TermRef) => Unit): Unit = {
    val work = initial.clone()
    val degrees = ArrayBuffer(allTermRefs.map(t => backEdges(t).size) : _*)

    while (work.nonEmpty) {
      val t: TermRef = work.head
      work.remove(t)

      for (s <- edges(t)) {
        degrees(s) -= 1
        if (degrees(s) == 0)
          work.add(s)
      }

      f(t)
    }
  }

  // Calls f with each term in topological order
  protected def topoTerms(f: (TermRef) => Unit): Unit =
    _topoTerms(sources,
      outEdges.asInstanceOf[ArrayBuffer[Iterable[TermRef]]],
      inEdges.asInstanceOf[ArrayBuffer[Iterable[TermRef]]], f)

  // Calls f with each term in reverse topological order
  protected def reverseTopoTerms(f: (TermRef) => Unit): Unit =
    _topoTerms(sinks,
      inEdges.asInstanceOf[ArrayBuffer[Iterable[TermRef]]],
      outEdges.asInstanceOf[ArrayBuffer[Iterable[TermRef]]], f)

  // Returns false if as a result of the labelling we detected unsat
  //  and true otherwise.
  protected def label(t: TermRef, sort: SortRef, ctors: CtorRefSet): Boolean =
  {
    val rt = representative(t)
    val stillSat = labels(rt) match {
      case None =>
        labels(rt) = Some((sort, ctors))
        ctors.isEmpty
      case Some((`sort`, ctors0)) =>
        val ctors1 = ctors0 &~ ctors
        labels(rt) = Some((sort, ctors1))
        ctors1.isEmpty
      case Some((sort0, _)) => // sort0 != sort
        labels(rt) = Some((sort0, mutable.BitSet.empty))
        false
    }
    // Is the term's ctor now unambiguous?
    labels(rt) match {
      case Some((_, ctors1)) if ctors1.size == 1 =>
        ctorFound.add(rt)
    }

    // [Selector rules / Collapse 2]
    // TODO: Make this more efficient by grouping elems in the hashset by ctor?
    labels(rt) match {
      case Some((_, ctors1)) =>
        selectorsOf(t)
          .filter(s => s.sort != sort || !ctors1.contains(s.ctor))
          .foreach(s => merge(s.ref, sig.designatedTerm(s.sort, s.ctor)))
    }

    stillSat
  }

  // Merge equivalence class representative rj *into* rep. ri, i.e. ri will be
  //  the representative of the resulting equivalence class.
  private def _merge(ri: TermRef, rj: TermRef): Option[TermRef] = {
    // TODO: Do path compression ("fast union-find")

    eqClasses(rj) = ri
    eqClassSizes(ri) += eqClassSizes(rj)
    (eqClassConsts(ri), eqClassConsts(rj)) match {
      case (_, None) =>
        // No additional information about representative constants
      case (None, cj) =>
        eqClassConsts(ri) = cj
      case _ =>
        // [Unification closure rules / Clash]
        return None
    }

    labels(rj) match {
      case None =>
        // No additional labelling information
      case Some((sort, ctors)) =>
        if (!label(ri, sort, ctors))
          return None
    }

    if (pathExists(ri, rj) || pathExists(rj, ri))
      return None

    inEdges(ri) ++= inEdges(rj)
    if (sources.contains(ri) && inEdges(ri).nonEmpty)
      sources -= ri

    // [Unification closure / Decompose]
    val esi = outEdges(ri)
    val esj = outEdges(rj)
    if (esi.isEmpty && esj.nonEmpty) {
      esi ++= esj
      if (sinks.contains(ri))
        sinks -= ri
    } else if (esi.nonEmpty && esj.nonEmpty) {
      assert(esi.size == esj.size)
      if ((esi zip esj) exists { case (ti, tj) => merge(ti, tj).isEmpty })
        return None
    }

    Some(ri)
  }

  // Merges the equivalence classes of terms i and j (and additionally does all
  //  sorts of bookkeeping on internal data structures).
  // Returns Some(t) if the merge did not violate any constraints and t is
  //  the equality class' new representative.
  // Returns None if the merge if we detected unsat.
  protected def merge(i: TermRef, j: TermRef): Option[TermRef] = {
    val ri = representative(i)
    val rj = representative(j)
    if (ri == rj)
      Some(ri)
    else if (eqClassSizes(rj) <= eqClassSizes(ri))
      _merge(ri, rj)
    else
      _merge(rj, ri)
  }

  def solve(inst: Instance): Boolean = {
    // Prepare internal state
    resetInternalState()

    sig = inst.sig
    declaredTypes = inst.declaredTypes

    inst.allTopLevelTerms foreach registerTerm
    allTermRefs filter(inEdges(_).isEmpty) foreach sources.add
    allTermRefs filter(outEdges(_).isEmpty) foreach sinks.add

    // Actual algorithm
    // = Process literals

    // [Lit-level rules / Orient]
    inst.eqs foreach { case (s, t) =>
      merge(s.ref, t.ref)
    }

    // [Lit-level rules / Remove]
    inst.tests foreach {case Tester(sort, ctor, t) =>
      label(t.ref, sort, newCtorRefSet(Set(ctor)))
    }

    // NOTE: Does not exactly match rule 'Remove 2' in the paper
    //  (note difference between sort(v) vs. sort of tester)
    inst.negtests foreach {case Tester(sort, ctor, t) =>
      val ctorRefs = sig.ctorRefs(sort) - ctor
      label(t.ref, sort, ctorRefs)
    }

    // = Apply 'normal' rules

    // [Congruence closure / Simplify 1, Superpose, Compose]
    //  ... are covered by merge()

    // Alternate between computing unification and congruence closures
    while (true) {
      // [Selector rules / Instantiate 1 & 2]
      for (t <- ctorFound) {
        ctorOf(t) match { case Some(sc @ (sort, ctor)) =>
          val instantiate =
            // Instantiate 1
            (selectorsOf.get(t) match {
              case Some(selectors) =>
                selectors exists {s => s.sort == sort && s.ctor == ctor}
              case _ => false
            }) ||
            // Instantiate 2
            sig.isFiniteCtor(sort, ctor)
          if (instantiate) {
            ??? // TODO: Implement instantiation
          }
        }
      }
      ctorFound.clear()

      // [Congruence closure / Simplify 2]

    }


    // = Check inequalities
    if (inst.ineqs exists
        {case (s, t) => representative(s.ref) == representative(t.ref)}) {
      return false
    }

    // Success!
    true
  }
}
