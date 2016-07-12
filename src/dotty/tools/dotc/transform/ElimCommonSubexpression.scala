package dotty.tools.dotc
package transform

import TreeTransforms._
import core._
import DenotTransformers._
import Symbols._
import SymDenotations._
import Contexts._
import Types._
import Flags._
import Decorators._
import SymUtils._
import util.Attachment
import core.StdNames.nme
import ast.Trees._

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
          println(s"${tree.symbol} after ${name} became ${rhst.show}")
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
    // TODO: Should go away with the notion of a new stopping `foreachSubTree`
    val alreadyProcessed = collection.mutable.HashMap[Tree, Idempotent]()
    // TODO: Long instead of Int? Unlikely, but just as a precaution
    val idempotentCounters = collection.mutable.HashMap[Idempotent, Int]()

    @scala.annotation.tailrec
    def linkChildToParent(trees: List[Tree]): Unit = {
      trees match {
        case child :: parent :: tail =>
          parents += (child -> parent)
          linkChildToParent(tail)
        case _ =>
      }
    }

    val analyzer: Visitor = {
      case tree: Tree
        if Idempotent.isIdempotent(tree) && !alreadyProcessed.contains(tree) =>

          val idempotentPairs = Idempotent.from(tree)
          val orderedTrees = idempotentPairs.map(_._1).reverse
          linkChildToParent(orderedTrees)

          idempotentPairs.foreach { p =>
            alreadyProcessed += p
            val (_, idempotent) = p
            val currentCounter = idempotentCounters.getOrElse(idempotent, 0)
            // TODO: Reorder depending on probability of the predicate
            if (currentCounter == 0) {
              idempotentCounters += (idempotent -> 1)
            } else {
              idempotentCounters += (idempotent -> (currentCounter + 1))
            }
          }
      case _ =>
    }

    val visitor: Visitor = {
      // Optimizing within blocks for the moment
      case b: Block => b.foreachSubTree(analyzer)
      case t =>
    }

    val transformer: Transformer = () => {
      println(s"got $candidates")
      println(s"got $parents")

      val canBeOptimized = idempotentCounters.filter(_._2 > 1)
      val candidates = canBeOptimized.toList.sortBy(_._2)

      val alreadyOptimized = collection.mutable.HashSet[Idempotent]()
      // TODO: Continue algorithm
      
      val transformation: Tree => Tree = {
        case t => t
      }
      transformation
    }

    ("elimCommonSubexpression", visitor, transformer)
  }

  /** TODO: Document this and especially the depth field */
  case class Idempotent(fun: Symbol,
                        qual: Symbol,
                        depth: Int,
                        typeParams: List[Type],
                        args: List[List[Type]])(implicit ctx: Context) {

    override def equals(that: Any): Boolean = that match {
      case that: Idempotent =>
        if (this eq that) true
        else if (fun != that.fun) false
        else if (depth != that.depth) false
        else if (qual != that.qual) false
        else if (typeParams.size != that.typeParams.size) false
        else if (typeParams zip that.typeParams exists (t => !(t._1 =:= t._2)))
          false
        else if (args.size != that.args.size) false
        else
          (args zip that.args) forall {
            case (a1s, a2s) =>
              a1s.size == a2s.size && (a1s zip a2s).forall(t => t._1 =:= t._2)
          }

      case _ => false
    }

    override def hashCode: Int = fun.hashCode + qual.hashCode
  }

  object Idempotent {

    /** Return *all* the possible idempotent instances paired up
      * with the original trees from which they were generating.
      *
      * The passed [[tree]] must be idempotent.
      *
      * The list of idempotent instances needs to be ordered by
      * instances built from the outside to the inside.
      */
    def from(tree: Tree)(implicit ctx: Context): List[(Tree, Idempotent)] = {
      def canBeFactoredOut(sym: Symbol) =
        if (sym is Method) true
        else (sym is Lazy) && !(sym is JavaDefined)

      def accumulate(tree: Tree,
                     original: Tree,
                     qual: Symbol,
                     depth: Int,
                     typeParams: List[Type],
                     argss: List[List[Type]]): List[(Tree, Idempotent)] = {
        tree match {
          case i: Ident if canBeFactoredOut(tree.symbol) =>
            List(original -> Idempotent(tree.symbol, qual, depth, typeParams, argss))

          case Apply(fun, args) =>
            val tpes = args.map(_.tpe)
            val withoutApply = args.map(a => accumulate(a, a, NoSymbol, depth + 1, Nil, Nil))
            val withApply = accumulate(fun, original, qual, depth, typeParams, tpes :: argss)
            withApply ::: withoutApply.reduce(_ ++ _)

          case TypeApply(fun, targs) =>
            accumulate(fun, original, qual, depth, targs.map(_.tpe) ::: typeParams, argss)

          case Select(qual, _) if canBeFactoredOut(tree.symbol) =>
            val withoutSelect = accumulate(qual, qual, NoSymbol, depth + 1, Nil, Nil)
            val withSelect = original -> Idempotent(tree.symbol, qual.symbol, depth, typeParams, argss)
            withSelect :: withoutSelect

          case Typed(expr, _) => accumulate(expr, tree, qual, depth, typeParams, argss)

          case _ => Nil
        }
      }

      // Assume that tree is idempotent
      accumulate(tree, tree, NoSymbol, 0, Nil, Nil)
        .filter(tp => isValid(tp._2))
    }

    def isValid(idem: Idempotent): Boolean =
      idem.typeParams.nonEmpty || idem.args.nonEmpty

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

  }

}
