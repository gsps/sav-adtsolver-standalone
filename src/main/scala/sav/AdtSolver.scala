package sav

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

/**
 * Created by gs on 22.03.15.
 */
class AdtSolver(k: Int) {
  sealed abstract class Expr { def isAtomic = false }
  case class Variable(name: Int) extends Expr { override def isAtomic = true }
  case class Constant(name: Int) extends Expr { override def isAtomic = true }
  case class Selector(index: Int, arg: Expr) extends Expr
  case class Constructor(args: List[Expr]) extends Expr

//  sealed abstract class Vertex
//  case class LabeledVertex(label: Expr) extends Vertex // Atomic expression
//  case class UnlabeledVertex() extends Vertex
  case class Vertex(labels: ArrayBuffer[Expr])
  object Vertex {
    def newPseudo() = Vertex(new ArrayBuffer[Expr](0))
    def newFromExpr(expr: Expr) = Vertex(new ArrayBuffer[Expr](1) += expr)
  }

  // TODO: Replace HashMaps by id-indexed ArrayBuffers
  // TODO: Replace inefficient eq. class merge by something like union-find
  // TODO: Could we just embed edge lists in Vertex?
  //  That would be inconsistent with parentMap (which we can't move into Vertex,
  //    i.e. a case class)

//  protected val eqClassMap = new mutable.HashMap[Expr, Option[Expr]]
//  protected val edgeMap = new mutable.HashMap[Expr, ArrayBuffer[Expr]]
  protected val parentMap = new mutable.HashMap[Vertex, Vertex]
  protected val edgeMap = new mutable.HashMap[Vertex, ArrayBuffer[Vertex]]
  protected val exprMap = new mutable.HashMap[Expr, Vertex]

  def solve(eqs: Seq[(Expr, Expr)], iqs: Seq[(Expr, Expr)]): Boolean = {

//    def eqLookup(expr: Expr): Expr = {
//      val repr = eqClassMap.getOrElse[Option[Expr]](expr, {Some(expr)})
//      repr match {
//        case None => expr
//        case Some(parent) => eqLookup(parent)
//      }
//    }
//    // Merges eq. classes of a and b, assuming a and b are respective representatives
//    def eqMerge(a: Expr, b: Expr): Expr = {
////      eqClassMap foreach { case (key, value) =>
////        if (value == b) {
////          eqClassMap.put(key, a)
////        }
////      }
//      eqClassMap.put(b, Some(a))
//      a
//    }

    // TODO: What we want is a check whether a and b lie in the same weakly connected
    //  component. Can we solve this efficiently by means of union-find?
    //  If so, our problem with multiple parents below would be solved as well.
    def isReachableFrom(a: Vertex, b: Vertex): Boolean = {
      if (a == b)
        return true
      parentMap.get(a) match {
        case None => false
        case Some(parent) => isReachableFrom(parent, b)
      }
    }

    // Merges Vertices a and b.
    //  Returns the remaining Vertex if successful and
    //  returns None if the merge would create a cycle.
    def merge(a: Vertex, b: Vertex): Option[Vertex] = {
//      assert(edgeMap.get(a).head.length == edgeMap.get(b).head.length)

      // FIXME: Slow acyclicity check
      if (isReachableFrom(a,b) || isReachableFrom(b,a))
        return None

      // Merge b into a
      a.labels ++= b.labels
      parentMap.remove(b)
      edgeMap.remove(b)
      b.labels foreach { expr => exprMap.put(expr, a) }

      // FIXME FIXME FIXME: Need to keep b's parent too.
      //  ! This makes our current acyclicity check infeasible.
      //  ! Also, we should keep in mind our checks for congruity.

      // Merge children
      val childrenA = edgeMap.get(a).head
      val childrenB = edgeMap.get(b).head
      // FIXME: Should actually check whether a and b are of
      //  the same constructor
      if (childrenA.length == childrenB.length) {
        childrenA zip childrenB foreach { case (ca,cb) => merge(ca,cb) }
      }

      Some(a)
    }

    // Computes the congruence closure of the given internal graph.
    //  Returns true on success and false if cycles are introduced.
    def computeCongruenceClosure(): Boolean = {

    }

    // Adds expr to the internal graph
//    def registerExpr(expr: Expr): Unit = {
//      if (edgeMap.contains(expr)) {
//        return
//      }
//
//      val edges = edgeMap.getOrElseUpdate(expr, {new ArrayBuffer[Expr](k)})
//      eqClassMap.put(expr, None)
//
//      expr match {
//        case Variable(_) =>
//        case Constant(_) =>
//        case Selector(arg) => {
//          if (arg.isAtomic) {
//            // TODO: Insert pseudo-constructor
//          }
//          registerExpr(arg)
//          // TODO: Add edges
//        }
//        case Constructor(args) => {
//          args foreach registerExpr
//          edges ++= args
//        }
//      }
//    }
    def registerExpr(expr: Expr): Vertex = {
      exprMap.get(expr) match {
        case Some(v) => return v
      }

      lazy val noEdges  = new ArrayBuffer[Vertex](0)

      val vertex        = Vertex.newFromExpr(expr)
      exprMap.put(expr, vertex)

      expr match {
        case Variable(_) =>
          edgeMap.put(vertex, noEdges)
        case Constant(_) =>
          edgeMap.put(vertex, noEdges)
        case Selector(index, arg) =>
          val constructor = registerExpr(arg)
          val children    = edgeMap.get(constructor).head
          if (arg.isAtomic) {
            // Insert pseudo-children of atomic constructor
            children ++= (1 to k) map { _ => Vertex.newPseudo() }
          }
          children(index).labels += expr
        case Constructor(args) =>
          val children = args map registerExpr
          children foreach { child => parentMap.put(child, vertex) }
          edgeMap.put(vertex, new ArrayBuffer[Vertex](k) ++= children)
      }

      vertex
    }

    // Reset internal state

    parentMap.clear()
    edgeMap.clear()
//    eqClassMap.clear()
    exprMap.clear()

    // Actual algorithm

    eqs ++ iqs foreach { case (a,b) => registerExpr(a); registerExpr(b) }

    // Merge explicitly equivalent expressions,
    //  i.e. compute the unification closure
    val cyclic = eqs exists { case(a,b) =>
      merge(exprMap.get(a).head, exprMap.get(b).head) == None
    }
    if (cyclic)
      return false

    if (!computeCongruenceClosure())
      return false

    val violatesInEq = iqs exists { case(a,b) =>
      exprMap.get(a) == exprMap.get(b)
    }
    !violatesInEq
  }
}