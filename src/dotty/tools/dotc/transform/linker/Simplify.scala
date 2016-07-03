package dotty.tools.dotc.transform.linker

import dotty.tools.dotc.{ast, core}
import core._
import Contexts._
import dotty.tools.dotc.ast.Trees._
import StdNames._
import NameOps._
import dotty.tools.dotc.ast.{tpd, untpd}
import Symbols._
import dotty.tools.dotc.core.Types.{ExprType, MethodType, NoPrefix, TermRef, ThisType}
import dotty.tools.dotc.transform.{Erasure, TreeTransforms}
import dotty.tools.dotc.transform.TreeTransforms.{MiniPhaseTransform, TransformerInfo}
import dotty.tools.dotc.transform.SymUtils._
import Decorators._
import dotty.tools.dotc.core.DenotTransformers.IdentityDenotTransformer

import scala.collection.mutable
import scala.collection.mutable.ListBuffer
import dotty.tools.dotc.core.Types.Type
import dotty.tools.dotc.core.Types.MethodParam


class Simplify extends MiniPhaseTransform with IdentityDenotTransformer {

  import tpd._

  override def phaseName: String = "simplify"

  private def desugarIdent(i: Ident)(implicit ctx: Context): Option[tpd.Select] = {
    i.tpe match {
      case TermRef(prefix: TermRef, name) =>
        Some(tpd.ref(prefix).select(i.symbol))
      case TermRef(prefix: ThisType, name) =>
        Some(tpd.This(prefix.cls).select(i.symbol))
      case _ => None
    }
  }

  private def dropCasts(t: Tree)(implicit ctx: Context): Tree = t match {
    //case TypeApply(aio@Select(rec, nm), _) if aio.symbol == defn.Any_asInstanceOf => dropCasts(rec)
    case Typed(t, tpe) => t
    case _ => t
  }

  private def readingOnlyVals(t: Tree)(implicit ctx: Context): Boolean = dropCasts(t) match {
    case Typed(exp, tpe) => readingOnlyVals(exp)
    case Apply(Select(rec, _), Nil) =>
      if (t.symbol.isGetter && !t.symbol.is(Flags.Mutable)) readingOnlyVals(rec) // getter of a immutable field
      else if (t.symbol.owner.derivesFrom(defn.ProductClass) && t.symbol.owner.is(Flags.CaseClass) && t.symbol.name.isProductAccessorName)
        readingOnlyVals(rec) // accessing a field of a product
      else if (t.symbol.is(Flags.CaseAccessor) && !t.symbol.is(Flags.Mutable))
        readingOnlyVals(rec)
      else false
    case Select(rec, _) if t.symbol.is(Flags.Method) =>
      if (t.symbol.isGetter && !t.symbol.is(Flags.Mutable)) readingOnlyVals(rec) // getter of a immutable field
      else if (t.symbol.owner.derivesFrom(defn.ProductClass) && t.symbol.owner.is(Flags.CaseClass) && t.symbol.name.isProductAccessorName)
        readingOnlyVals(rec) // accessing a field of a product
      else if (t.symbol.is(Flags.CaseAccessor) && !t.symbol.is(Flags.Mutable))
        readingOnlyVals(rec)
      else false
    case Select(qual, _) if !t.symbol.is(Flags.Mutable) =>
      readingOnlyVals(qual)
    case t: Ident if !t.symbol.is(Flags.Mutable) && !t.symbol.is(Flags.Method) =>
      desugarIdent(t) match {
        case Some(t) => readingOnlyVals(t)
        case None => true
      }
    case t: This => true
    case _ => false
  }

  type Visitor = Tree => Unit
  type ErasureCompatibility = Int
  val BeforeErasure: ErasureCompatibility = 1
  val AfterErasure: ErasureCompatibility  = 2
  val BeforeAndAfterErasure: ErasureCompatibility  = BeforeErasure | AfterErasure

  val NoVisitor: Visitor = (_) => ()
  type Transformer = () => (Tree => Tree)
  type Optimization = (Context) => (String, ErasureCompatibility, Visitor, Transformer)

  private lazy val _optimizations = Seq(inlineCaseIntrinsics, inlineLabelsCalledOnce, devalify, dropNoEffects, inlineLocalObjects, specializeBodiesOfInstanceChecks /*, varify*/)
  override def transformDefDef(tree: tpd.DefDef)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = {
    if (!tree.symbol.is(Flags.Label)) {
      var rhs0 = tree.rhs
      var previousRhs: Tree = null
      val erasureCompatibility = if (ctx.erasedTypes) AfterErasure else BeforeErasure
      while (previousRhs ne rhs0) {
        val initialized = _optimizations.map(x =>x(ctx.withOwner(tree.symbol)))
        var (names, erasureSupport , visitors, transformers) = unzip4(initialized)
        // todo: fuse for performance
        while (names.nonEmpty) {
          val nextVisitor = visitors.head
          val supportsErasure = erasureSupport.head
          if ((supportsErasure & erasureCompatibility) > 0) {
            rhs0.foreachSubTree { st =>
              // rhs0 can be a thicket and contains a previous rhs
              if(st eq previousRhs) ()
              else nextVisitor(st)
            }
            val nextTransformer = transformers.head()
            val name = names.head
            val rhst = new TreeMap() {
              override def transform(tree: tpd.Tree)(implicit ctx: Context): tpd.Tree = nextTransformer(super.transform(tree))
            }.transform(rhs0)
            if (rhst ne rhs0) println(s"${tree.symbol} after ${name} became ${rhst.show}")
            rhs0 = rhst
          }
          previousRhs = rhs0
          names = names.tail
          visitors = visitors.tail
          erasureSupport = erasureSupport.tail
          transformers = transformers.tail
        }
      }
      if (rhs0 ne tree.rhs) cpy.DefDef(tree)(rhs = rhs0)
      else tree
    } else tree
  }

  val inlineCaseIntrinsics: Optimization = { (ctx0: Context) => {
    implicit val ctx = ctx0
    val transformer: Transformer = () => {
      case a: Apply if a.symbol.is(Flags.Synthetic) && a.symbol.owner.is(Flags.Module) &&
        (a.symbol.name == nme.apply) && a.symbol.owner.companionClass.is(Flags.CaseClass) =>
        tpd.New(a.tpe, a.args)
      case a: Apply if a.symbol.is(Flags.Synthetic) && a.symbol.owner.is(Flags.Module) &&
        (a.symbol.name == nme.unapply) && a.symbol.owner.companionClass.is(Flags.CaseClass) && !a.symbol.owner.is(Flags.Scala2x) =>
        a.args.head
      case t => t
    }
    ("inlineCaseIntrinsics", BeforeAndAfterErasure, NoVisitor, transformer)
  }}

  val inlineLocalObjects: Optimization = { (ctx0: Context) => {
    implicit val ctx = ctx0
    val hasPerfectRHS = collection.mutable.HashMap[Symbol, Boolean]() // in the end only calls constructor. Reason for unconditional inlining
    val checkGood = collection.mutable.HashMap[Symbol, Symbol]() // if key has perfect RHS than value has perfect RHS
    val gettersCalled = collection.mutable.HashSet[Symbol]()
    def followTailPerfect(t: Tree, symbol: Symbol): Unit = {
      t match {
        case Block(_, expr) => followTailPerfect(expr, symbol)
        case If(_, thenp, elsep) => followTailPerfect(thenp, symbol); followTailPerfect(elsep, symbol);
        case Apply(fun, _) if fun.symbol.isConstructor && t.tpe.widenDealias == symbol.info.widenDealias.finalResultType.widenDealias =>
          hasPerfectRHS(symbol) = true
        case Apply(fun, _) if fun.symbol.is(Flags.Label) && (fun.symbol ne symbol) =>
          checkGood.put(fun.symbol, symbol)
        case t: Ident if !t.symbol.owner.isClass =>
          checkGood.put(t.symbol, symbol)
        case _ =>
      }
    }
    val visitor: Visitor = {
      case vdef: ValDef if vdef.symbol.info.classSymbol is Flags.CaseClass  =>
        followTailPerfect(vdef.rhs, vdef.symbol)
      case Assign(lhs, rhs) if !lhs.symbol.owner.isClass =>
        checkGood.put(rhs.symbol, lhs.symbol)
      case t @ Select(qual, _) if (t.symbol.isGetter && !t.symbol.is(Flags.Mutable)) ||
      (t.symbol.owner.derivesFrom(defn.ProductClass) && t.symbol.owner.is(Flags.CaseClass) && t.symbol.name.isProductAccessorName) ||
        (t.symbol.is(Flags.CaseAccessor) && !t.symbol.is(Flags.Mutable)) =>
        gettersCalled(qual.symbol) = true
      case t: DefDef if t.symbol.is(Flags.Label) =>
        followTailPerfect(t.rhs, t.symbol)
      case _ =>
    }

    val transformer: Transformer = () =>{
        var hasChanged = true
        while(hasChanged) {
          hasChanged = false
          checkGood.foreach{case (key, value) =>
            if (hasPerfectRHS.getOrElse(key, false)) {
              hasChanged = !hasPerfectRHS.put(value, true).getOrElse(false)
            }
          }
        }

      val newMappings: Map[Symbol, Map[Symbol, Symbol]] =
        hasPerfectRHS.iterator.map(x => x._1).filter(x => !x.is(Flags.Method) && !x.is(Flags.Label) && gettersCalled.contains(x.symbol) && (x.symbol.info.classSymbol is Flags.CaseClass))
        .map{ refVal =>
          val fields = refVal.info.classSymbol.caseAccessors.filter(_.isGetter) // todo: drop mutable ones
          val productAccessors = (1 to fields.length).map(i => refVal.info.member(nme.productAccessorName(i)).symbol) // todo: disambiguate
          val newLocals = fields.map(x =>
            ctx.newSymbol(refVal.owner, (refVal.name + "$" + x.name).toTermName, Flags.Synthetic | Flags.Mutable, x.asSeenFrom(refVal.info).info.finalResultType.widenDealias)
          )
          val fieldMapping = fields zip newLocals
          val productMappings = productAccessors zip newLocals
          (refVal, (fieldMapping ++ productMappings).toMap)
        }.toMap
      val toSplit: mutable.Set[Symbol] = mutable.Set.empty ++ newMappings.keySet

      def splitWrites(t: Tree, target: Symbol): Tree = {
        t match {
          case tree@ Block(stats, expr) => cpy.Block(tree)(stats, splitWrites(expr, target))
          case tree@ If(_, thenp, elsep) => cpy.If(tree)(thenp = splitWrites(thenp, target), elsep =  splitWrites(elsep, target))
          case Apply(sel , args) if sel.symbol.isConstructor && t.tpe.widenDealias == target.info.widenDealias.finalResultType.widenDealias =>
            val fieldsByAccessors = newMappings(target)
            val accessors = target.info.classSymbol.caseAccessors.filter(_.isGetter)
            val assigns = (accessors zip args) map (x => ref(fieldsByAccessors(x._1)).becomes(x._2))
            val recreate = sel.appliedToArgs(accessors.map(x => ref(fieldsByAccessors(x))))
            Block(assigns, recreate)
          case Apply(fun, _) if fun.symbol.is(Flags.Label) =>
            t // do nothing. it will do on its own
          case t: Ident if !t.symbol.owner.isClass && newMappings.contains(t.symbol) && t.symbol.info.classSymbol == target.info.classSymbol =>
            val fieldsByAccessorslhs = newMappings(target)
            val fieldsByAccessorsrhs = newMappings(t.symbol)
            val accessors = target.info.classSymbol.caseAccessors.filter(_.isGetter)
            val assigns = accessors map (x => ref(fieldsByAccessorslhs(x)).becomes(ref(fieldsByAccessorsrhs(x))))
            Block(assigns, t)
          // if t is itself split, push writes
          case _ =>
            evalOnce(t){ev =>
              val fieldsByAccessors = newMappings(target)
              val accessors = target.info.classSymbol.caseAccessors.filter(_.isGetter)
              val assigns = accessors map (x => ref(fieldsByAccessors(x)).becomes(ev.select(x)))
              Block(assigns, ev)
            } // need to eval-once and update fields

        }
      }

      def followCases(t: Symbol): Symbol = if (t.symbol.is(Flags.Label)) {
        followCases(checkGood.getOrElse(t, NoSymbol))
      } else t

      { (t: Tree) => t match {
        case ddef: DefDef if ddef.symbol.is(Flags.Label) =>
          newMappings.get(followCases(ddef.symbol)) match {
            case Some(mappings) =>
              cpy.DefDef(ddef)(rhs = splitWrites(ddef.rhs, followCases(ddef.symbol)))
            case _ => ddef
          }
      case a: ValDef if toSplit.contains(a.symbol) =>
        toSplit -= a.symbol
        // break ValDef apart into fields + boxed value
        val newFields = newMappings(a.symbol).values.toSet
        Thicket(
          newFields.map(x => tpd.ValDef(x.asTerm, EmptyTree)).toList :::
            List(cpy.ValDef(a)(rhs = splitWrites(a.rhs, a.symbol))))
      case ass: Assign =>
        newMappings.get(ass.lhs.symbol) match {
          case None =>   ass
          case Some(mapping) =>
            val updates = mapping.filter(x => x._1.is(Flags.CaseAccessor)).map(x => ref(x._2).becomes(ref(ass.lhs.symbol).select(x._1))).toList
            Thicket(ass :: updates)
        }
      case sel @ Select(rec, _) if (t.symbol.isGetter && !t.symbol.is(Flags.Mutable)) ||
        (t.symbol.owner.derivesFrom(defn.ProductClass) && t.symbol.owner.is(Flags.CaseClass) && t.symbol.name.isProductAccessorName) ||
        (t.symbol.is(Flags.CaseAccessor) && !t.symbol.is(Flags.Mutable)) =>
        newMappings.getOrElse(rec.symbol, Map.empty).get(sel.symbol) match {
          case None => t
          case Some(newSym) => ref(newSym)
        }
      case t => t
    }}}
    ("inlineLocalObjects", BeforeAndAfterErasure, visitor, transformer)
  }}

  private def keepOnlySideEffects(t: Tree)(implicit ctx: Context): Tree = {
    t match {
      case t: Literal => EmptyTree
      case Typed(exp, tpe) =>
        keepOnlySideEffects(exp)
      case t @ If(cond, EmptyTree, EmptyTree) =>
        keepOnlySideEffects(cond)
      case t @ If(cond, thenp, elsep) =>
        cpy.If(t)(thenp = keepOnlySideEffects(thenp), elsep = keepOnlySideEffects(elsep))
      case Select(rec, _) if (t.symbol.isGetter && !t.symbol.is(Flags.Mutable)) ||
        (t.symbol.owner.derivesFrom(defn.ProductClass) && t.symbol.owner.is(Flags.CaseClass) && t.symbol.name.isProductAccessorName) ||
        (t.symbol.is(Flags.CaseAccessor) && !t.symbol.is(Flags.Mutable))=>
          keepOnlySideEffects(rec) // accessing a field of a product
      case Select(qual, _) if !t.symbol.is(Flags.Mutable) && (!t.symbol.is(Flags.Method) || t.symbol.isGetter) =>
        keepOnlySideEffects(qual)
      case Block(List(t: DefDef), s: Closure) => EmptyTree
      case bl@Block(stats, expr) =>
        val stats1 = stats.mapConserve(keepOnlySideEffects)
        val stats2 = if (stats1 ne stats) stats1.filter(x=>x ne EmptyTree) else stats1
        val expr2: tpd.Tree = expr match {
          case t: Literal if t.tpe.derivesFrom(defn.UnitClass) => expr
          case _ => keepOnlySideEffects(expr).orElse(unitLiteral)
        }
        cpy.Block(bl)(stats2, expr2)
      case t: Ident if !t.symbol.is(Flags.Method) =>
        desugarIdent(t) match {
          case Some(t) => t
          case None => EmptyTree
        }
      case app: Apply if app.fun.symbol.is(Flags.Label) && !app.tpe.finalResultType.derivesFrom(defn.UnitClass) =>
        val denot = app.fun.symbol.denot
        //println(s"replacing ${app.symbol}")
        if (!denot.info.finalResultType.derivesFrom(defn.UnitClass)) {
          val newLabelType = app.symbol.info match {
            case mt: MethodType =>
              mt.derivedMethodType(mt.paramNames, mt.paramTypes, defn.UnitType)
            case et: ExprType =>
              et.derivedExprType(defn.UnitType)
          }
          val newD = app.symbol.asSymDenotation.copySymDenotation(info = newLabelType)
          newD.installAfter(this)
        }

        ref(app.symbol).appliedToArgs(app.args)
      case t @ Apply(fun, _) if Analysis.effectsDontEscape(t) =>
        def getArgsss(a: Tree): List[Tree] = a match {
          case a: Apply => getArgsss(a.fun) ::: a.args
          case _ => Nil
        }
        def getSel(t: Tree): Tree = {t match {
          case t: Apply => getSel(t.fun)
          case t: Select => t.qualifier
          case t: TypeApply => getSel(t.fun)
          case _ => t
        }}
        val args = getArgsss(t)
        val rec = getSel(t)
        val prefix = rec match {
          case t: New =>
            args.map(keepOnlySideEffects)
          case _ =>
            rec :: args.map(keepOnlySideEffects)
        }
        Block(prefix, tpd.unitLiteral)
      case _ => t
    }
  }

  val bubbleUpNothing: Optimization = { (ctx0: Context) => {
    implicit val ctx = ctx0
    val transformer: Transformer = () => {
      case Apply(Select(qual, _), args)  if qual.tpe.derivesFrom(defn.NothingClass) => qual
      case Apply(Select(qual, _), args)  if args.exists(x => x.tpe.derivesFrom(defn.NothingClass)) =>
        val (keep, noth:: other) = args.span(x => !x.tpe.derivesFrom(defn.NothingClass))
        Block(qual :: keep, noth)
      case Assign(_, rhs) if rhs.tpe.derivesFrom(defn.NothingClass) =>
        rhs
      case If(cond, _, _) if cond.tpe.derivesFrom(defn.NothingClass) => cond
      case a: Block if a.stats.exists(x => x.tpe.derivesFrom(defn.NothingClass))  =>
        val (keep, noth:: other) = a.stats.span(x => !x.tpe.derivesFrom(defn.NothingClass))
        Block(keep, noth)
      case t => t
    }
    ("bubbleUpNothing", BeforeAndAfterErasure, NoVisitor, transformer)
  }}

  val dropNoEffects: Optimization = { (ctx0: Context) => {
    implicit val ctx = ctx0

    val transformer: Transformer = () => {
      case Block(Nil, expr) => expr
      case a: Block  =>
        cpy.Block(a)(stats = a.stats.mapConserve(keepOnlySideEffects), a.expr)
      case a: DefDef =>
        if (a.symbol.info.finalResultType.derivesFrom(defn.UnitClass) && !a.rhs.tpe.derivesFrom(defn.UnitClass)) {
          cpy.DefDef(a)(rhs = keepOnlySideEffects(a.rhs), tpt = tpd.TypeTree(defn.UnitType))
        } else a
      case t => t
    }
    ("dropNoEffects", BeforeAndAfterErasure, NoVisitor, transformer)
  }}

  val inlineLabelsCalledOnce: Optimization = { (ctx0: Context) => {
    implicit val ctx = ctx0
    val timesUsed = collection.mutable.HashMap[Symbol, Int]()
    val defined = collection.mutable.HashMap[Symbol, DefDef]()

    val visitor: Visitor = {
      case defdef: DefDef if defdef.symbol.is(Flags.Label)  =>
        var isRecursive = false
        defdef.rhs.foreachSubTree(x => if (x.symbol == defdef.symbol) isRecursive = true)
        if (!isRecursive) defined.put(defdef.symbol, defdef)
      case t: Apply if t.symbol.is(Flags.Label) =>
        val b4 = timesUsed.getOrElseUpdate(t.symbol, 0)
        timesUsed.put(t.symbol, b4 + 1)
      case _ =>
    }

    val transformer: Transformer = () => {
      case a: Apply if a.symbol.is(Flags.Label) && timesUsed.getOrElse(a.symbol, 0) == 1 && a.symbol.info.paramTypess == List(Nil)=>
        defined.get(a.symbol) match {
          case None => a
          case Some(defDef) =>
            //println(s"Inlining ${defDef.name}")
            defDef.rhs.changeOwner(defDef.symbol, ctx.owner)
        }
      case a: DefDef if (a.symbol.is(Flags.Label) && timesUsed.getOrElse(a.symbol, 0) == 1 && defined.contains(a.symbol)) =>
        //println(s"Dropping ${a.name} ${timesUsed.get(a.symbol)}")
        defined.put(a.symbol, a)
        EmptyTree
      case a: DefDef if (a.symbol.is(Flags.Label) && timesUsed.getOrElse(a.symbol, 0) == 0 && defined.contains(a.symbol)) =>
        //println(s"Dropping ${a.name} ${timesUsed.get(a.symbol)}")
        EmptyTree
      case t => t
    }
    ("inlineLabelsCalledOnce", BeforeAndAfterErasure, visitor, transformer)
  }}

  val devalify: Optimization = { (ctx0: Context) => {
    implicit val ctx = ctx0
    val timesUsed = collection.mutable.HashMap[Symbol, Int]()
    val defined = collection.mutable.HashSet[Symbol]()
    val copies = collection.mutable.HashMap[Symbol, Tree]() // either a duplicate or a read through series of immutable fields
    val visitor: Visitor = {
      case valdef: ValDef if !valdef.symbol.is(Flags.Param) && !valdef.symbol.is(Flags.Mutable) && (valdef.symbol.exists && !valdef.symbol.owner.isClass) =>
        defined += valdef.symbol

        dropCasts(valdef.rhs) match {
          case t: Tree if readingOnlyVals(t) =>
            copies.put(valdef.symbol, valdef.rhs)
          case _ =>
        }
      case valdef: ValDef  if valdef.symbol.exists && !valdef.symbol.owner.isClass && !valdef.symbol.is(Flags.Param) =>
        //todo: handle params after constructors. Start changing public signatures by eliminating unused arguments.
        defined += valdef.symbol

      case t: RefTree =>
        val b4 = timesUsed.getOrElseUpdate(t.symbol, 0)
        timesUsed.put(t.symbol, b4 + 1)
      case _ =>
    }

    val transformer: Transformer = () => {

      val valsToDrop = defined -- timesUsed.keySet
      val copiesToReplaceAsDuplicates = copies.filter { x =>
        val rhs = dropCasts(x._2)
        !rhs.symbol.owner.isClass && !rhs.symbol.is(Flags.Method) && !rhs.symbol.is(Flags.Mutable)
      }
      // todo: if a non-synthetic val is duplicate of a synthetic one, rename a synthetic one and drop synthetic flag?

      val copiesToReplaceAsUsedOnce =
        timesUsed.filter(x => x._2 == 1).
          flatMap(x => copies.get(x._1) match {
            case Some(tr) => List((x._1, tr));
            case None => Nil
          })


      val replacements = copiesToReplaceAsDuplicates ++ copiesToReplaceAsUsedOnce

      val transformation: Tree => Tree = {
        case t: ValDef if valsToDrop.contains(t.symbol) =>
          // println(s"droping definition of ${t.symbol.showFullName} as not used")
          t.rhs
        case t: ValDef if replacements.contains(t.symbol) =>
          // println(s"droping definition of ${t.symbol.showFullName} as an alias")
          EmptyTree
        case t: Block => // drop non-side-effecting stats
          t
        case t: RefTree if !t.symbol.is(Flags.Method) && !t.symbol.is(Flags.Param) && !t.symbol.is(Flags.Mutable) =>
          replacements.getOrElse(t.symbol, t)
        case tree => tree
      }

      transformation
    }
    ("devalify", BeforeAndAfterErasure, visitor, transformer)
  }}

  val varify: Optimization = { (ctx0: Context) => {
    implicit val ctx = ctx0
    val paramsTimesUsed = collection.mutable.HashMap[Symbol, Int]()
    val possibleRenames = collection.mutable.HashMap[Symbol, Set[Symbol]]()
    val visitor: Visitor = {
      case t: ValDef
        if t.symbol.is(Flags.Param) =>
          paramsTimesUsed += (t.symbol -> 0)
      case valDef: ValDef
        if valDef.symbol.is(Flags.Mutable) =>
          valDef.rhs.foreachSubTree { subtree =>
            if (paramsTimesUsed.contains(subtree.symbol) &&
              valDef.symbol.info.widenDealias <:< subtree.symbol.info.widenDealias) {
              val newSet = possibleRenames.getOrElse(valDef.symbol, Set.empty) + subtree.symbol
              possibleRenames.put(valDef.symbol, newSet)
            }
          }
      case t: RefTree
        if paramsTimesUsed.contains(t.symbol) =>
          val param = t.symbol
          val current = paramsTimesUsed.get(param)
          current foreach { c => paramsTimesUsed += (param -> (c + 1)) }
      case _ =>
    }
    val transformer = () => {
      val paramCandidates = paramsTimesUsed.filter(kv => kv._2 == 1).keySet
      val renames = possibleRenames.iterator.map(kv => (kv._1, kv._2.intersect(paramCandidates))).
        filter(x => x._2.nonEmpty).map(x => (x._1, x._2.head)).toMap
      val transformation: Tree => Tree = {
        case t: RefTree
          if renames.contains(t.symbol) =>
            ref(renames(t.symbol))
        case t: ValDef
          if renames.contains(t.symbol) =>
            val replaced = renames(t.symbol)
            if (t.rhs.symbol == replaced) EmptyTree
            else ref(replaced).becomes(t.rhs)
        case t: ValDef
          if paramCandidates.contains(t.symbol) =>
            t.symbol.flags = Flags.Mutable
            t
        case t => t
      }
      transformation
    }
    ("varify", AfterErasure, visitor, transformer)
  }}

  private def unzip4[A, B, C, D](seq: Seq[(A, B, C, D)]): (Seq[A], Seq[B], Seq[C], Seq[D]) = {
    val listBuilderA = new ListBuffer[A]()
    val listBuilderB = new ListBuffer[B]()
    val listBuilderC = new ListBuffer[C]()
    val listBuilderD = new ListBuffer[D]()
    seq.foreach { x =>
      listBuilderA += x._1
      listBuilderB += x._2
      listBuilderC += x._3
      listBuilderD += x._4
    }
    (listBuilderA.toList, listBuilderB.toList, listBuilderC.toList, listBuilderD.toList)
  }

  /** Hoist up bodies of if expressions whose predicate use `isInstanceOf` to
    * an outer scope as functions specialized for the type in the predicate.
    *
    * The following tree:
    *
    *   def target[T](d: D, t: T) =
    *     if (d.isInstanceOf[A]) bodyTrue
    *     else bodyFalse
    *
    * will be transformed to:
    *
    *   def target$d[T](d: A, t: T) = bodyTrue
    *   def target[T](d: D, t: T) =
    *     if (d.isInstanceOf[A]) target$d(d)
    *     else bodyFalse
    */
  val specializeBodiesOfInstanceChecks: Optimization = (ctx0: Context) => {
    implicit val ctx = ctx0

    def isInstanceCheck(t: Tree): Boolean = {
      dropCasts(t) match {
        case ta @ TypeApply(select, _) =>
          select.symbol.name.show == "isInstanceOf"
        case t => false
      }
    }

    val targetsToHoistUp = collection.mutable.HashSet[Symbol]()
    val visitor: Visitor = {
      case defdef: DefDef => defdef.rhs match {
        case i @ If(cond, thenp, elsep)
          /* The transformation is enabled only for methods
           * with if expressions and not blocks with ifs. */
          if isInstanceCheck(cond) =>
            targetsToHoistUp += defdef.symbol
        case _ =>
      }
      case _ =>
    }
    val transformer = () => {
      val transformation: Tree => Tree = {
        case defdef: DefDef
          if targetsToHoistUp.contains(defdef.symbol) =>
            targetsToHoistUp -= defdef.symbol
            val If(cond, thenp, elsep) = defdef.rhs
            val TypeApply(Select(param, _), List(castedTree)) = cond
            val specializedTpe = castedTree.tpe.finalResultType

            val oldMethodSigTpe = defdef.symbol.info
            val paramNamess = oldMethodSigTpe.paramNamess
            val paramTypess = oldMethodSigTpe.paramTypess.iterator
            val idxs = paramNamess.iterator.map(_.indexWhere(_ == param.symbol.name))
            val newParamTypess: List[List[Type]] = (idxs zip paramTypess).map { t =>
              val (idx, pts) = t
              if(idx == -1) pts
              else pts.updated(idx, specializedTpe)
            }.toList

            // Temporary flattening, figure out how to play with
            // MethodType to represent different lists of parameters
            val newMethodSigTpe = MethodType(paramNamess.flatten, newParamTypess.flatten, oldMethodSigTpe.resultType)
            val newMethodSym = ctx.newSymbol(
              defdef.symbol.owner, ctx.freshName(defdef.name).toTermName,
              defdef.symbol.flags | Flags.Synthetic, newMethodSigTpe).asTerm
            val specializedMethod = tpd.polyDefDef(newMethodSym,
              (tparams: List[Type]) => {
                (paramss: List[List[Tree]]) =>
                  paramss.foldLeft(thenp){ (acc, ps) =>
                    ps.foldLeft(acc) { (acc2, p) =>
                      if(p.symbol.name == param.symbol.name)
                        acc2.subst(List(param.symbol), List(p.symbol))
                      else acc2
                    }
                  }
              }
            )

            val specializedParam = param.asInstance(specializedTpe)
            val applied = tpd.ref(specializedMethod.symbol).appliedTo(specializedParam)
            val rewrittenBody = If(cond, applied, elsep)
            val newDefDef = cpy.DefDef(defdef)(rhs = rewrittenBody)
            tpd.Thicket(specializedMethod, newDefDef)
        case t => t
      }
      transformation
    }
    ("specializeBodiesOfInstanceChecks", BeforeErasure, visitor, transformer)
  }

}
