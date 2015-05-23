package sav

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

/**
 * Created by Georg Schmid on 24.04.15.
 *
 * An implementation of the decision procedure for abstract datatypes described
 *  in "An Abstract Decision Procedure for Satisfiability in the Theory of
 *  Recursive Data Types" by Barret et al.
 * Parts of the implementation that correspond to rules described in the paper
 *  are headed by comments of form "// [*Rule*]".
 */

package object types {
  type Index      = Int
  type CtorRef    = Int
  type SortRef    = Int
  type TermRef    = Int
  type CtorRefSet = mutable.BitSet
  type VarId      = Int
  type ConstId    = Int
  type Labels     = Option[(SortRef, CtorRefSet)]
  type Typing     = Map[Term, SortRef]

  def newCtorRefSet(sorts: Set[CtorRef]): CtorRefSet = {
    new mutable.BitSet ++ sorts
  }
}

import types._

case class Instance(sig: Signature,
                    // FIXME: declaredTypes is redundant b/c of [neg]tests!
                    declaredTypes: Typing,
                    eqs: Seq[(Term, Term)], ineqs: Seq[(Term, Term)],
                    tests: Seq[Tester], negtests: Seq[Tester]) {
  def allTopLevelTerms =
    (eqs ++ ineqs).foldLeft(Seq[Term]()){
      case (seq, (s, t)) => s +: t +: seq
    } ++ (tests ++ negtests).foldLeft(Seq[Term]()){
      case (seq, Tester(_, _, t)) => t +: seq
    }
}
// Signature =^ seq of sorts, sort =^ seq of ctors, ctor =^ seq of arg. sorts
case class Signature(sorts: Seq[Seq[Seq[SortRef]]]) {
  val sortRefs: Set[SortRef] = (0 until sorts.size).toSet

  require(sorts forall { ctors =>
    ctors forall { args =>
      args forall sortRefs.contains
    }
  })

  // FIXME: Inefficient to generate Sets here.
  def ctorRefs(sort: SortRef): CtorRefSet = {
    // sort \in sortRefs
    val ctors = (0 until sorts(sort).size).toSet
    newCtorRefSet(ctors)
  }
  def argIndices(sort: SortRef, ctor: CtorRef): Seq[Index] = {
    // sort \in sortRefs, ctor in \in ctorRefs(sort)
    (0 until sorts(sort)(ctor).size).toSeq
  }
  def argSort(sort: SortRef, ctor: CtorRef, index: Index): SortRef = {
    // sort \in sortRefs, ctor in \in ctorRefs(sort),
    //  index \in argIndices(sort, ctor)
    sorts(sort)(ctor)(index)
  }

  def isNullaryCtor(sort: SortRef, ctor: CtorRef): Boolean =
    sorts(sort)(ctor).isEmpty

  def isFiniteSort(sort: SortRef, from: Set[SortRef] = Set.empty): Boolean = {
    (0 until sorts(sort).size) forall (isFiniteCtor(sort, _, from))
  }

  def isFiniteCtor(sort: SortRef, ctor: CtorRef,
                   from0: Set[SortRef] = Set.empty): Boolean = {
    val argSorts = sorts(sort)(ctor)
    val from = from0 + sort
    argSorts.isEmpty ||
      (argSorts forall (as => !from.contains(as) && isFiniteSort(as, from)))
  }

  // TODO: Implement designated terms for selectors applied to terms of the
  //  'wrong' sort/ctor and add appropriate test cases.
  def designatedTerm(sort: SortRef, ctor: CtorRef): TermRef = ???
}

sealed abstract class Term {
  def subTerms = Seq[Term]()
}
case class Variable(varId: VarId) extends Term
case class Constant(constId: ConstId) extends Term
case class Constructor(sort: SortRef, ctor: CtorRef,
                       args: List[Term]) extends Term {
  override def subTerms = args.toSeq
}
case class Selector(sort: SortRef, ctor: CtorRef,
                    index: Index, arg: Term) extends Term {
  override def subTerms = Seq(arg)
}

case class Tester(sort: SortRef, ctor: CtorRef, arg: Term)


abstract class Result
case class Sat() extends Result
case class Unsat(reason: UnsatReason) extends Result

abstract class UnsatReason
case class Clash(ri: TermRef, rj: TermRef) extends UnsatReason
case class Cyclic(ri: TermRef, rj: TermRef) extends UnsatReason
case class EmptyLabelling(r: TermRef) extends UnsatReason
case class InvalidEquality(i: TermRef, j: TermRef) extends UnsatReason


class AdtSolver() {

  // TODO: Consider special case of a single sort with a single constructor,
  //  that is, labels(t) == None -- which then is the implicit representation of
  //  labels(t) == {the single constructor} -- might allow rule Instantiate 2
  //  (and others?).

  // Invariant: size of {terms, eqClass[Siz]es, labels, ...} == nextTermId
  protected var nextTermId: TermRef = 0
  protected var maxVarId: VarId = 0

  protected var sig: Signature = null
  protected var declaredTypes: Typing = null

  protected val terms         = new ArrayBuffer[Term]
  protected val termRefs      = new mutable.HashMap[Term, TermRef]

  protected val eqClasses     = new ArrayBuffer[TermRef]
  protected val eqClassSizes  = new ArrayBuffer[Int]
  protected val eqClassConsts = new ArrayBuffer[Option[ConstId]]
  protected val labels        = new ArrayBuffer[Labels]

  // >> DISREGARD THIS FOR NOW.
  // NOTE: On the right data structure for edge lists:
  //  We operate on these edge lists in two ways,
  //    a) we iterate over them (in no particular order), and
  //    b) we merge them (when merging equivalence classes and thus the
  //        representatives' data structures, incl. edge lists).
  //  TODO: Thus, use linked lists (which can be merged in O(n)).
  // <<
  protected val outEdges      = new ArrayBuffer[ArrayBuffer[TermRef]]
  protected val inEdges       = new ArrayBuffer[mutable.HashSet[TermRef]]
  //  protected val sources       = new mutable.HashSet[TermRef]
  //  protected val sinks         = new mutable.HashSet[TermRef]
  protected val sharedSets    = new mutable.HashMap[(TermRef, TermRef), mutable.HashSet[Index]]

  // selectorsOf maps uninstantiated terms to the set of selectors referring to them
  //  Invariant: outEdges(t).isEmpty || !selectorsOf.contains(t)
  type SelectorMap = mutable.HashMap[(SortRef, CtorRef, Index), Selector]
  protected val selectorsOf       = new mutable.HashMap[TermRef, SelectorMap]
  protected val emptySelectorMap  = new SelectorMap
  protected val potentialInst     = new mutable.HashSet[TermRef]
  protected val instantiated      = new mutable.ArrayBuffer[Boolean]
  protected val downSet           = new mutable.ArrayStack[(TermRef, TermRef)]

  protected var debug = false

  protected def resetInternalState(): Unit = {
    nextTermId  = 0
    maxVarId    = 0

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
    //    sources.clear()
    //    sinks.clear()
    sharedSets.clear()

    selectorsOf.clear()
    instantiated.clear()
    potentialInst.clear()
    downSet.clear()
  }

  protected def allTermRefs: Seq[TermRef] = (0 until nextTermId).toSeq

//  protected def getOrCreateTermRef(term: Term): TermRef =
//    termRefs.getOrElse(term, {registerTerm(term)})

  protected def freshVariable(): Variable = {
    maxVarId += 1
    Variable(maxVarId)
  }

  // Registers a given term and all of its subterms in the solver's internal
  //  data structures. In particular, an id is given to the term -- its
  //  term ref(erence) -- and is returned.
  protected def registerTerm(term: Term): TermRef = {
    if (termRefs contains term)
      return termRefs(term)

    val subTerms    = term.subTerms
    val subTermRefs = subTerms map registerTerm

    val id = nextTermId
    terms             += term
    termRefs(term)    = id
    eqClasses         += id
    eqClassSizes      += 1
    eqClassConsts     += (term match {
      case Constant(constId)  => Some(constId)
      case _                  => None
    })

    labels        += None
    instantiated  += false
    term match {
      case Constructor(sort, ctor, _) =>
        instantiated(id) = true // (must be set before label to avoid marking for potentialInst)
        labels(id) = Some((sort, newCtorRefSet(Set(ctor))))
      case term@Selector(sort, ctor, index0, arg) =>
        val argSort = sig.argSort(sort, ctor, index0)
        label(id, argSort, sig.ctorRefs(argSort))
        val selectee = subTermRefs.head
        if (instantiated(selectee)) {
          downSet push(id, outEdges(selectee)(index0))
        } else {
          selectorsOf.getOrElseUpdate(selectee, new mutable.HashMap) += (sort, ctor, index0) -> term
//          potentialInst add id
        }
      case _ =>
        declaredTypes.get(term) match {
          case Some(sort) =>
            labels(id) = Some((sort, sig.ctorRefs(sort)))
          case None =>
            labels(id) = None // meaning "of any sort and ctor"
        }
    }
    // Is the term's ctor now unambiguous?
    if (!instantiated(id)) {
      labels(id) match {
        case Some((_, ctors)) if ctors.size == 1 =>
          potentialInst add id
        case _ =>
        //
      }
    }
//    printDebug(s"Init ${id} @ ${term} w/ labels ${labels(id)}")

    term match {
      case Variable(varId) if varId > maxVarId => maxVarId = varId
      case _ =>
    }

    val out = new ArrayBuffer[TermRef]()
    outEdges += out
    term match {
      case _: Constructor =>
        out.sizeHint(subTerms.size)
        subTermRefs foreach { subRef =>
          out.append(subRef)
          inEdges(subRef).add(id)
        }
      case _ =>
      // NOTE: We explicitly do not add edges from selector arguments to
      //  selectors here! See instantiation below.
    }
    inEdges += new mutable.HashSet[TermRef]()

    nextTermId += 1
    id
  }

  // Returns the reference (i.e. id) of a term
  protected def ref(term: Term): TermRef = {
    termRefs.get(term).head
  }

  // Returns the representative of a term's equivalence class
  protected def repr(ref: TermRef): TermRef = {
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

  protected def sharedSetOf(ri: TermRef, rj: TermRef): mutable.HashSet[Index] = {
    assert(ri != rj)
    val sharedRef = if (ri <= rj) (ri, rj) else (rj, ri)
    sharedSets.getOrElseUpdate(sharedRef, new mutable.HashSet[Index])
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

  //  protected def _topoTerms(initial: mutable.HashSet[TermRef],
  //                           edges: ArrayBuffer[Iterable[TermRef]],
  //                           backEdges: ArrayBuffer[Iterable[TermRef]],
  //                           f: (TermRef) => Unit): Unit = {
  //    val work = initial.clone()
  //    val degrees = ArrayBuffer(allTermRefs.map(t => backEdges(t).size) : _*)
  //
  //    while (work.nonEmpty) {
  //      val t: TermRef = work.head
  //      work.remove(t)
  //
  //      for (s <- edges(t)) {
  //        degrees(s) -= 1
  //        if (degrees(s) == 0)
  //          work.add(s)
  //      }
  //
  //      f(t)
  //    }
  //  }
  //
  //  // Calls f with each term in topological order
  //  protected def topoTerms(f: (TermRef) => Unit): Unit =
  //    _topoTerms(sources,
  //      outEdges.asInstanceOf[ArrayBuffer[Iterable[TermRef]]],
  //      inEdges.asInstanceOf[ArrayBuffer[Iterable[TermRef]]], f)
  //
  //  // Calls f with each term in reverse topological order
  //  protected def reverseTopoTerms(f: (TermRef) => Unit): Unit =
  //    _topoTerms(sinks,
  //      inEdges.asInstanceOf[ArrayBuffer[Iterable[TermRef]]],
  //      outEdges.asInstanceOf[ArrayBuffer[Iterable[TermRef]]], f)

  // Restricts the labelling of term t to the intersection of the previously
  //  known labels of t and the given labels (ctors of the given sort).
  // Returns an UnsatReason if as a result of labelling we detected unsat and
  //  None otherwise.
  protected def label(t: TermRef, sort: SortRef, ctors: CtorRefSet):
      Option[UnsatReason] =
  {
    val rt = repr(t)
    val stillSat = labels(rt) match {
      case None =>
        labels(rt) = Some((sort, ctors))
        ctors.nonEmpty
      case Some((`sort`, ctors0)) =>
        val ctors1 = ctors0 & ctors
        labels(rt) = Some((sort, ctors1))
        ctors1.nonEmpty
      case Some((sort0, _)) => // sort0 != sort
        labels(rt) = Some((sort0, mutable.BitSet.empty))
        false
    }
    // Is the term's ctor now unambiguous?
    if (!instantiated(rt)) {
      labels(rt) match {
        case Some((_, ctors1)) if ctors1.size == 1 =>
          potentialInst add rt
        case _ =>
        //
      }
    }

    // [Selector rules / Collapse 2]
    // TODO: Make this more efficient by grouping elems in the set by ctor?
    labels(rt) match {
      case Some((_, ctors1)) =>
        // Equate all selectors of this term that do not select arguments of one of the
        //  still-feasible constructors with their respective designated term.
        selectorsOf.get(t)
          .map( _
              .collect {case ((_sort, _ctor, _), sel) if _sort != sort || !ctors1.contains(_ctor) => sel}
              .foreach {sel => downSet.push((ref(sel), sig.designatedTerm(sel.sort, sel.ctor)))}
            )
      case _ =>
        //
    }

    if (stillSat) None else Some(EmptyLabelling(rt))
  }

  // Merge equivalence class representative rj *into* rep. ri, i.e. ri will be
  //  the representative of the resulting equivalence class.
  private def _merge(ri: TermRef, rj: TermRef): Either[(TermRef, TermRef), UnsatReason] = {
    // TODO: Do path compression ("fast union-find")
    printDebug(s"Merging $ri and $rj")
    printDebug(s"\tBefore: ${labels(ri)} & ${labels(rj)}")

    eqClasses(rj) = ri
    eqClassSizes(ri) += eqClassSizes(rj)
    (eqClassConsts(ri), eqClassConsts(rj)) match {
      case (_, None) =>
        // No additional information about representative constants
      case (None, cj) =>
        eqClassConsts(ri) = cj
      case _ =>
        // [Unification closure rules / Clash]
        return Right(Clash(ri, rj))
    }

    labels(rj) match {
      case None =>
      // No additional labelling information
      case Some((sort, ctors)) =>
        val unsatReason = label(ri, sort, ctors)
        if (unsatReason.isDefined)
          return Right(unsatReason.head)
    }
    printDebug(s"\tAfter: ${labels(ri)}")

    val alreadyInstantiated = instantiated(ri) || instantiated(rj)
    instantiated(ri) = alreadyInstantiated

    if (pathExists(ri, rj) || pathExists(rj, ri))
      return Right(Cyclic(ri, rj))

    //    // Update shared sets of parents
    //    // TODO: Covers only the case of merges due to congruence so far ... right?
    //    for (pi <- inEdges(ri)) {
    //      val rpi = representative(pi)
    //      val (sortpi, ctorpi) = ctorOf(rpi).head
    //      for (pj <- inEdges(rj)) {
    //        val rpj = representative(pj)
    //        val (sortpj, ctorpj) = ctorOf(rpj).head
    //        // TODO: Cut down on cases where rpi == rpj
    //        if (rpi != rpj && sortpi == sortpj && ctorpi == ctorpj) {
    //          // TODO: Inefficient. Should only have to traverse relevant indices
    //          for (index <- sig.argIndices(sortpi, ctorpi)) {
    //            if (outEdges(rpi).contains(pi) && outEdges(rpj).contains(pj)) {
    //              sharedSetOf(rpi, rpj).add(index)
    //            }
    //          }
    //        }
    //      }
    //    }

    inEdges(ri) ++= inEdges(rj)
    //    if (sources.contains(ri) && inEdges(ri).nonEmpty)
    //      sources -= ri

    // FIXME: References in edgelists should be updated to their representatives -- generally in _merge?

    val esi = outEdges(ri)
    val esj = outEdges(rj)
//    if (esi.isEmpty && esj.nonEmpty) {
//      // FIXME: When combining (out?) edgelists the reference should be updated to their representatives
//      esi ++= esj
//      //      if (sinks.contains(ri))
//      //        sinks -= ri
//    }

    // A term either is already instantiated (and thus has arguments connected to it)
    //  or is uninstantiated and in that case *may* have selectors referring to it.
    assert(esi.isEmpty || !selectorsOf.contains(ri))
    assert(esj.isEmpty || !selectorsOf.contains(rj))

    if (esi.nonEmpty && esj.nonEmpty) {
      assert(alreadyInstantiated)
      assert(esi.size == esj.size)
      downSet ++= esi zip esj

    } else {
      // Potentially merge selectors
      // selectorsOf are implicit (i.e. not yet connected) children that we also need to merge
      (selectorsOf.get(ri), selectorsOf.get(rj)) match {
        // Merge selectors with selectors
        case (Some(selectorsi), Some(selectorsj)) =>
          val keysi = selectorsi.keySet
          val keysj = selectorsj.keySet
          for (key <- keysi intersect keysj)
            downSet push (ref(selectorsi(key)), ref(selectorsj(key)))
          for (key <- keysj diff keysi)
            selectorsi += key -> selectorsj(key)
          if (ctorOf(ri).isDefined)
            potentialInst add ri

        // Merge selectors with children
        case (Some(selectors), _) if esj.nonEmpty =>
          ctorOf(rj) match { case Some((sort, ctor)) =>
            for (((`sort`, `ctor`, index), sel) <- selectors)
              downSet push (ref(sel), esj(index))
          }
          selectorsOf.remove(ri)
        case (_, Some(selectors)) if esi.nonEmpty =>
          ctorOf(rj) match { case Some((sort, ctor)) =>
            for (((`sort`, `ctor`, index), sel) <- selectors)
              downSet push (ref(sel), esi(index))
          }
          // No need to remove selectors of rj, since ri will be the representative

        case _ =>
          selectorsOf.remove(ri)
      }

      if (esi.isEmpty && esj.nonEmpty)
        esi ++= esj
    }


    Left((ri, rj))
  }

  // Merges the equivalence classes of terms i and j (and additionally does all
  //  sorts of bookkeeping on internal data structures).
  // Returns Some((ri, rj)) if the merge did not violate any constraints, ri is
  //  the equality class' new representative and rj was the (old)
  //  representative of the equality class that was merged into ri's.
  // Returns an UnsatReason if as a result of the merge if we detected unsat.
  protected def merge(i: TermRef, j: TermRef): Either[(TermRef, TermRef), UnsatReason] = {
    val ri = repr(i)
    val rj = repr(j)
    if (ri == rj)
      Left((ri, rj))
    else if (eqClassSizes(rj) <= eqClassSizes(ri))
      _merge(ri, rj)
    else
      _merge(rj, ri)
  }

  def solve(inst: Instance): Result = {
    // Prepare internal state
    resetInternalState()

    sig = inst.sig
    declaredTypes = inst.declaredTypes

    inst.allTopLevelTerms foreach registerTerm
    printDebug(dumpTerms())
    //    allTermRefs filter(inEdges(_).isEmpty) foreach sources.add
    //    allTermRefs filter(outEdges(_).isEmpty) foreach sinks.add

    // Actual algorithm
    // = Process literals

    // [Lit-level rules / Orient]
    inst.eqs foreach { case (s, t) =>
      downSet.push((ref(s), ref(t)))
    }

    // [Lit-level rules / Remove]
    // TODO: Needs test cases
    inst.tests foreach {case Tester(sort, ctor, t) =>
      val res = label(ref(t), sort, newCtorRefSet(Set(ctor)))
      if (res.isDefined)
        return Unsat(res.head)
    }

    // TODO: Needs test cases
    // NOTE: Does not exactly match rule 'Remove 2' in the paper
    //  (note difference between sort(v) vs. sort of tester)
    inst.negtests foreach {case Tester(sort, ctor, t) =>
      val ctorRefs = sig.ctorRefs(sort) - ctor
      val res = label(ref(t), sort, ctorRefs)
      if (res.isDefined)
        return Unsat(res.head)
    }

    // = Apply 'normal' rules

    // [Congruence closure / Simplify 1, Superpose, Compose]
    //  ... are covered by merge()

    // Alternate between computing unification (downward) and
    //  congruence (upward) closures
    var splittingConverged = false
    while (!splittingConverged) {
      splittingConverged = true

      var closuresConverged = false
      while (!closuresConverged) {
        closuresConverged = true

        // [Selector rules / Instantiate 1 & 2]
        // TODO: Go through occasions on which potentialInst is populated and perhaps cut them down.
        // A term is added to potentialInst only once, i.e. as soon as a single labels is associated
        //  with it.
        // Terms are never added to potentialInst when they have already been instantiated.
        // However: Due to merges queued up in the downSet, some terms in potentialInst will --
        //  by the time we run this loop -- in fact be in an instantiated equivalence class.
        for (t <- potentialInst if !instantiated(t)) {
          printDebug(s"Potential instantiation of $t")
          closuresConverged = false
          ctorOf(t) match {
            case Some(sc @ (sort, ctor)) =>
              val instantiate =
                !sig.isNullaryCtor(sort, ctor) && (
                  // Instantiate 1
                  (selectorsOf.get(t) match {
                    case Some(selectors) =>
                      // WRONG?
                      //                  selectors exists {case (i,s) => s.sort == sort && s.ctor == ctor}
                      sig.argIndices(sort, ctor).toSet subsetOf
                        (selectors.keysIterator collect {case (`sort`,`ctor`,i) => i} toSet)
                    case _ => false
                  }) ||
                    // Instantiate 2
                    sig.isFiniteCtor(sort, ctor)
                  )
              if (instantiate) {
                printDebug(s"\tdone!")
                val selectors = selectorsOf.getOrElse(t, emptySelectorMap)
                val args = sig.argIndices(sort, ctor) map { index =>
                  selectors.getOrElse((sort, ctor, index), freshVariable())
                }
                val newConstructor = Constructor(sort, ctor, args.toList)
                downSet push (t, registerTerm(newConstructor))
                selectorsOf.remove(t)
                //            instantiated(t) = true // Implied by merge later on
              }
            //          case None =>
            //            //
          }
        }
        potentialInst.clear()

        // [Unification closure / Decompose]
        while (downSet.nonEmpty) {
          closuresConverged = false
          val (i, j) = downSet.pop()

          //        val (ri, rj) = (repr(i), repr(j))
          //        {
          //          // If r and j are equivalent, so must be their corresponding children (i.e., we merge)
          //          val esi = outEdges(ri)
          //          val esj = outEdges(rj)
          //
          //          // A term either is already instantiated (and thus has arguments connected to it)
          //          //  or is uninstantiated and in that case *may* have selectors referring to it.
          //          assert(esi.isEmpty || !selectorsOf.contains(ri))
          //          assert(esj.isEmpty || !selectorsOf.contains(rj))
          //
          //          if (esi.nonEmpty && esj.nonEmpty) {
          //            assert(esi.size == esj.size)
          //            downSet ++= esi zip esj
          //          } else {
          //            // selectorsOf are implicit (i.e. not yet connected) children that we also need to merge
          //            (selectorsOf.get(ri), selectorsOf.get(rj)) match {
          //              case (Some(selectorsi), Some(selectorsj)) =>
          //
          //              case (Some(selectors), _) if esj.nonEmpty =>
          //              case (_, Some(selectors)) if esi.nonEmpty =>
          //              case _ =>
          //              //
          //            }
          //          }
          //        }

          merge(i, j) match {
            case Left(_) =>
            //
            case Right(unsatReason) =>
              return Unsat(unsatReason)
          }
        }

        // TODO: Instantiate here as well?

        // [Congruence closure / Simplify 2]
        //      while (upSet.nonEmpty) {
        //        converged = false
        //        val (i, j) = upSet.pop()
        //        merge(i, j) match {
        //          case Some((ri, rj)) =>
        //            //
        //          case None =>
        //            return false
        //        }
        //      }
        // TODO: Don't rebuild repsWithCtors every time
        val reps =
          (eqClasses.iterator.zipWithIndex filter {case (s,i) => s == i} map(_._2)).toSeq
        val repsWithCtors =
        //        (reps zip (reps map ctorOf) collect {case (r, Some(sc)) => (r, sc)}).toSeq
          (reps zip (reps filter(instantiated(_)) map ctorOf) collect {case (r, Some(sc)) => (r, sc)}).toSeq
        for ((ri, (sorti, ctori)) <- repsWithCtors) {
          val esi = outEdges(ri)
          for ((rj, (sortj, ctorj)) <- repsWithCtors) {
            // TODO: Avoid symmetrical cases, e.g. (0,1) and (1,0)
            if (ri != rj && sorti == sortj && ctori == ctorj) {
              val esj = outEdges(rj)
              val sharedSet = sharedSetOf(ri, rj)
              val indices = sig.argIndices(sorti, ctori).toSet
              for (index <- indices diff sharedSet) {
                if (repr(esi(index)) == repr(esj(index))) {
                  sharedSet.add(index)
                }
              }
              //            printDebug(s"sharedSet($ri, $rj) = $sharedSet")
              if (sharedSet.size == indices.size) {
                closuresConverged = false
                merge(ri, rj) match {
                  case Right(unsatReason) =>
                    return Unsat(unsatReason)
                  case _ =>
                  //
                }
              }
            }
          }
        }
      } // << while (!converged)

//      val reps =
//        (eqClasses.iterator.zipWithIndex filter {case (s,i) => s == i} map(_._2)).toSeq
//      reps find { r => !instantiated(r) && ctorOf(r).isEmpty } map { r =>
//        splittingConverged = false
//        // TODO: Implement splitting
//      }
    } // << while (!splittingConverged)


    // = Check inequalities
    inst.ineqs.find {case (s, t) => repr(ref(s)) == repr(ref(t))} match {
      case Some((s,t)) =>
        return Unsat(InvalidEquality(ref(s), ref(t)))
      case _ =>
      //
    }

    printDebug(dumpTerms())
    printDebug(dumpEqClasses())

    // Success!
    Sat()
  }


  def dumpTerms(): String =
    (terms.zipWithIndex map { case (term, i) =>
      val strI = i.formatted("%2d")
      s"   $strI: $term"
    }).mkString("Terms:\n", "\n", "")

  def dumpEqClasses(): String = {
    val equalSets = new mutable.HashMap[TermRef, mutable.HashSet[TermRef]]
    for (t <- allTermRefs)
      equalSets.getOrElseUpdate(repr(t), new mutable.HashSet()) += t
    equalSets.map({case (r, set) => s"   $r: $set"}).mkString("Equivalence classes:\n", "\n", "")
  }

  def debugOn(): Unit = debug = true
  def debugOff(): Unit = debug = false

  protected def printDebug(s: String) =
    if (debug) println(s)
}
