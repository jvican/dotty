package dotty.tools.dotc
package transform

import TreeTransforms._
import core._
import Symbols._
import Contexts._
import Types._
import Flags._
import ast.Trees._
import dotty.tools.dotc.ast.tpd
import dotty.tools.dotc.transform.IdempotentTree.IdempotentTree

import scala.annotation.tailrec

/** This phase performs Common Subexpression Elimination (CSE) that
  * precomputes an expression into a new variable when it's used
  * several times within the same scope.
  *
  * This optimization is applied for either lazy vals or expressions
  * that are annotated with `Idempotent`. Such annotation is used to
  * ensure to the compiler that a concrete expression has no side
  * effects.
  *
  * For instance, the following code:
  * {{{
  *   val a = 1
  *   val b = a + a + 2
  *   val c = a + a + 4
  * }}}
  *
  * will be transformed to:
  * {{{
  *   val a = 1
  *   val a1 = a + a
  *   val b = a1 + 2
  *   val c = a1 + 2
  * }}}
  *
  * Originally written by @allanrenucci, refactored by @jvican.
  *
  */
class ElimCommonSubexpression extends MiniPhaseTransform {

  import ast._
  import ast.tpd._

  override def phaseName = "elimCommonSubexpression"

  override def runsAfter = Set(classOf[ElimByName])

  /* Imitate `Simplify` structure for the moment being */
  type Visitor = Tree => Unit
  val NoVisitor: Visitor = (_) => ()
  type Transformer = () => (Tree => Tree)
  type Optimization = (Context) => (String, Visitor, Transformer)

  override def transformDefDef(tree: tpd.DefDef)(
      implicit ctx: Context,
      info: TransformerInfo): tpd.Tree = {
    if (!tree.symbol.is(Flags.Label)) {
      var rhs0 = tree.rhs
      var rhs1: Tree = null
      while (rhs1 ne rhs0) {
        rhs1 = rhs0
        val (name, nextVisitor, nextTransformer) =
          elimCommonSubexpression(ctx.withOwner(tree.symbol))
        rhs0.foreachSubTree(nextVisitor)
        val transformer = nextTransformer()
        val rhst = new TreeMap() {
          override def transform(tree: tpd.Tree)(
              implicit ctx: Context): tpd.Tree =
            transformer(super.transform(tree))
        }.transform(rhs0)
        if (rhst ne rhs0)
          println(s"${tree.symbol} after $name became ${rhst.show}")
        rhs0 = rhst
      }
      if (rhs0 ne tree.rhs) cpy.DefDef(tree)(rhs = rhs0)
      else tree
    } else tree
  }

  /** Lifted up val def and tree referencing to it */
  type Optimized = (ValDef, Tree)

  def elimCommonSubexpression: Optimization = (ctx0: Context) => {
    implicit val ctx = ctx0

    val parents = collection.mutable.HashMap[Tree, Tree]()
    val replacements = collection.mutable.HashMap[Tree, Optimized]()

    val childParents = collection.mutable.HashMap[Tree, Tree]()
    val visited = collection.mutable.HashSet[Tree]()
    val cached = collection.mutable.HashMap[Tree, List[IdempotentTree]]()
    val appearances = collection.mutable.HashMap[IdempotentTree, Int]()

    @scala.annotation.tailrec
    def linkChildsToParents(trees: List[IdempotentTree]): Unit = {
      trees match {
        case child :: parent :: tail =>
          parents += (child.tree -> parent.tree)
          linkChildsToParents(tail)
        case _ =>
      }
    }

    val analyzer: Visitor = {
      case tree: Tree if !visited.contains(tree) =>
          IdempotentTree.from(tree) match {
            case Some(idempotent) =>
              println(s"idempotent: ${idempotent.tree}")
              val allSubTrees = IdempotentTree.allIdempotentTrees(idempotent)
              cached += idempotent.tree -> allSubTrees
              linkChildsToParents(allSubTrees.reverse)
              allSubTrees.foreach { st =>
                val tree = st.tree
                visited += tree
                val current = appearances.getOrElse(st, 0)
                appearances += st -> (current + 1)
              }

              println(allSubTrees.map(_.tree).mkString("\n"))
            case None =>
          }

      case _ =>
    }

    val visitor: Visitor = {
      // Optimizing within blocks for the moment
      case b: Block => b.foreachSubTree(analyzer)
      case t =>
    }

    val optimized = collection.mutable.HashMap[Tree, Optimized]()

    val transformer: Transformer = () => {
      println(s"got $parents")

      val optimizationTargets = appearances.filter(_._2 > 1)
      val candidates = optimizationTargets.toList.sortBy(_._2).map(_._1)

      @tailrec
      def getOptimizedParent(tree: Tree): Option[Tree] = {
        childParents.get(tree) match {
          case hit @ Some(parent) =>
            if (optimized.contains(tree)) hit
            else getOptimizedParent(parent)
          case None => None
        }
      }

      candidates.foreach { c =>
        val tree = c.tree
        if (!optimized.contains(tree)) {
          getOptimizedParent(tree) match {
            case Some(parent) =>
              val (parentValDef, parentRef) = optimized(parent)

            case None =>
              println("HIT")
              println(s"$tree can be optimized")
              // Introduce new ValDef
              // tpd.SyntheticValDef()
              //
          }
        }
      }

      // TODO: Continue algorithm
      println(s"got ${appearances.map(p => p._1.tree -> p._2)}")

      val transformation: Tree => Tree = {
        case t => t
      }
      transformation
    }

    ("elimCommonSubexpression", visitor, transformer)
  }

}

object IdempotentTree {

  import ast.tpd._

  class IdempotentTree(val tree: tpd.Tree)(implicit ctx: Context) {

    import scala.util.hashing.MurmurHash3.{seqHash, mix}

    /** Witness of structural equality by inspecting the tree */
    def idempotentHashCode(t: Tree)(implicit ctx: Context): Int = {
      t match {
        case EmptyTree => EmptyTree.hashCode()
        case _: This => t.symbol.hashCode()
        case _: Super => t.symbol.hashCode()
        case _: Ident => t.symbol.hashCode()
        case Literal(constant) => constant.value.hashCode()
        case Select(qual, name) =>
          mix(name.hashCode(), idempotentHashCode(qual))
        case Apply(fun1, args1) =>
          val idempotents = seqHash(args1.map(idempotentHashCode))
          mix(idempotentHashCode(fun1), idempotents)
        case TypeApply(fun1, targs1) =>
          val idempotents = seqHash(targs1.map(idempotentHashCode))
          mix(idempotentHashCode(fun1), idempotents)
        // TODO: Case for `Typed`
        case _ => 0 // impossible case
      }
    }

    override def hashCode(): Int = idempotentHashCode(this.tree)

    /** Compare idempotent trees by structural equality */
    override def equals(that: Any): Boolean = that match {
      case thatIdempotent: IdempotentTree =>
        this.hashCode() == thatIdempotent.hashCode()
      case _ => false
    }
  }

  import ast._
  import ast.tpd._

  // Never call directly without having checked that it's indeed idempotent
  def apply(tree: Tree)(implicit ctx: Context): IdempotentTree =
    new IdempotentTree(tree)

  def from(tree: Tree)(implicit ctx: Context): Option[IdempotentTree] =
    if (isIdempotent(tree)) Some(new IdempotentTree(tree)) else None

  def isIdempotent(tree: Tree)(implicit ctx: Context): Boolean = {
    /** We consider idempotent expressions known to be initialized once
      * (lazy vals and vals), and methods annotated with `Idempotent` */
    def isIdempotentRef(tree: Tree): Boolean = {
      val sym = tree.symbol
      if (sym hasAnnotation defn.IdempotentAnnot) true // @Idempotent
      else if (sym is Lazy) true // lazy val and singleton objects
      else !(sym is Mutable) && !(sym is Method) // val
    }

    tree match {
      case EmptyTree | This(_) | Super(_, _) | Literal(_) => true
      case Ident(_) => isIdempotentRef(tree)
      case Select(qual, _) => isIdempotent(qual) && isIdempotentRef(tree)
      case TypeApply(fn, _) => isIdempotent(fn)
      case Apply(fn, args) => isIdempotent(fn) && (args forall isIdempotent)
      case Typed(expr, _) => isIdempotent(expr)
      case _ => false
    }
  }

  /** Collects all the idempotent sub trees, including the original tree. */
  def allIdempotentTrees(t1: IdempotentTree)
                        (implicit ctx: Context): List[IdempotentTree] = {
    // TODO: Pending to remove Typed casts to remove comparison failures
    def collect(isTopTree: Boolean, tree: Tree): List[IdempotentTree] = tree match {
      case EmptyTree | This(_) | Super(_, _) | Literal(_) | Ident(_) => Nil
      case Select(qual, _) =>
        if (isTopTree) IdempotentTree(tree) :: collect(isTopTree = false, qual)
        else collect(isTopTree, qual)
      case TypeApply(fn, _) =>
        if(isTopTree) IdempotentTree(tree) :: collect(isTopTree = false, fn)
        else collect(isTopTree, fn)
      case Apply(fn, args) =>
        val branched = args.map(collect(true, _)).reduce(_ ++ _)
        if(isTopTree) IdempotentTree(tree) :: collect(isTopTree = false, fn) ::: branched
        else collect(isTopTree, fn) ::: branched
      case Typed(expr, _) =>
        if(isTopTree) IdempotentTree(tree) :: collect(isTopTree = false, expr)
        else collect(isTopTree, expr)
      case _ => Nil // Impossible case, t1 is idempotent
    }

    collect(isTopTree = true, t1.tree)
  }

}

