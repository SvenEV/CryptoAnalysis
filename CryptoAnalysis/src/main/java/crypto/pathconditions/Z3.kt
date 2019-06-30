package crypto.pathconditions.z3

import com.google.common.cache.CacheBuilder
import com.google.common.cache.CacheLoader
import com.google.common.cache.LoadingCache
import com.microsoft.z3.*
import com.microsoft.z3.Context
import com.microsoft.z3.Expr
import crypto.pathconditions.expressions.*
import soot.*
import soot.jimple.*

//
// Provides functions to convert between JExpressions and Z3 expressions and to simplify them.
//

// TODO: Is it a problem that we don't distinguish float/double (byte/int/long) in Z3 encoding?

data class Z3Solver(
    val context: Context,
    val symbols: MutableMap<JExpression, Symbol>,
    val trueExpr: BoolExpr,
    val falseExpr: BoolExpr,
    val nullSymbol: Symbol,
    val objSort: Sort,
    val cache: LoadingCache<BoolExpr, Status> // TODO: populate cache
)

fun createSolver(): Z3Solver {
    val context = Context()
    val cache = CacheBuilder.newBuilder().build<BoolExpr, Status>(CacheLoader.from { expr ->
        val solver = context.mkSolver()
        solver.add(expr)
        solver.check()
    })
    val objSort = context.mkUninterpretedSort("Object")
    return Z3Solver(
        context,
        mutableMapOf(),
        context.mkTrue(),
        context.mkFalse(),
        context.mkSymbol("null"),
        objSort,
        cache
    )
}

fun Z3Solver.isSatisfiable(expr: BoolExpr) = when (cache.get(expr)) {
    Status.SATISFIABLE -> true
    Status.UNSATISFIABLE -> false
    Status.UNKNOWN -> false
    null -> false
}

fun Z3Solver.simplify(expr: BoolExpr) = when {
    expr == trueExpr -> expr
    expr == falseExpr -> expr
    !isSatisfiable(expr) -> falseExpr
    else -> {
        val goal = context.mkGoal(false, false, false)
        goal.add(expr)
        val tactic = context.mkTactic("ctx-solver-simplify")
        val a = tactic.apply(goal)
        when (a.subgoals.size) {
            0 -> falseExpr
            else -> {
                var ret: BoolExpr? = null
                for (subgoal in a.subgoals) {
                    val formulas = subgoal.formulas
                    if (formulas.isNotEmpty()) {
                        ret = formulas[0]
                        if (formulas.size > 1) {
                            for (i in 1 until formulas.size) {
                                ret = context.mkAnd(ret, formulas[i])
                            }
                        }
                    }
                }
                ret ?: trueExpr
            }
        }
    }
}

//
// Encode Jimple as Z3
//

// Checks if one of two types (in a binary operation) is of type boolean/String. If so, both operands should be
// interpreted as a boolean/String, even if they are the integer 0 or 1 or the null constant or something else.
private fun Z3Solver.getExpectedSort(t1: Type, t2: Type) = when {
    t1 == BooleanType.v() || t2 == BooleanType.v() -> context.boolSort
    t1.toString() == "java.lang.String" || t2.toString() == "java.lang.String" -> context.stringSort
    else -> encodeType(t1)
}

/** Translates a Soot type to a Z3 sort (all reference types except String are mapped to objSort) */
private fun Z3Solver.encodeType(t: Type) = when {
    t == BooleanType.v() -> context.boolSort
    t == IntType.v() -> context.intSort
    t == LongType.v() -> context.intSort
    t == ShortType.v() -> context.intSort
    t == ByteType.v() -> context.intSort
    t == CharType.v() -> context.intSort
    t == FloatType.v() -> context.realSort
    t == DoubleType.v() -> context.realSort
    t.toString() == "java.lang.String" -> context.stringSort
    else -> objSort
}

/**
 * Creates a Z3 symbol for a value that cannot better be translated to a Z3 expression.
 * Value-to-symbol mappings are stored in the [Z3Solver] instance so that symbols can be mapped back to their
 * original Jimple representations in [decode] (e.g. after simplification).
 * @return A constant expression of the existing or newly created symbol
 */
private fun Z3Solver.getOrCreateSymbol(v: JExpression, sort: Sort): Expr {
    val symbol = symbols.computeIfAbsent(v) { context.mkSymbol(it.toString(ContextFormat.Default)) }
    return context.mkConst(symbol, sort)
}

private fun Z3Solver.tryEncodeWellKnownCall(expr: JVirtualInvoke): Expr? = when {
    expr.method.toString() == "<java.lang.String: boolean equals(java.lang.Object)>" -> {
        val base = (expr.base as? JConstant)?.value as? StringConstant
        val other = (expr.args.elementAtOrNull(0) as? JConstant)?.value as? StringConstant
        when {
            base != null && other != null -> if (base.value == other.value) trueExpr else falseExpr
            else -> null
        }
    }
    else -> null
}

private fun Z3Solver.tryEncodeWellKnownStaticCall(expr: JStaticInvoke): Expr? = when {
    expr.method.toString() == "<kotlin.jvm.internal.Intrinsics: boolean areEqual(java.lang.Object,java.lang.Object)>" -> {
        val op1 = (expr.args.elementAtOrNull(0) as? JConstant)?.value as? StringConstant
        val op2 = (expr.args.elementAtOrNull(0) as? JConstant)?.value as? StringConstant
        when {
            op1 != null && op2 != null -> if (op1.value == op2.value) trueExpr else falseExpr
            else -> null
        }
    }
    else -> null
}

/**
 * Recursively translates a JExpression to a Z3 boolean expression.
 * Some expressions cannot be mapped to Z3 properly, including e.g. method calls and instanceof-expressions.
 * Instead, a new symbol is introduced for each such expression, allowing us to preserve those expressions as is during
 * encoding/decoding, even though Z3 can't do anything useful with them.
 */
fun Z3Solver.encode(expr: JExpression, expectedSort: Sort): Expr =
    try {
        when (expr) {
            is JTrue -> trueExpr
            is JFalse -> falseExpr
            is JNull -> context.mkConst(nullSymbol, expectedSort)
            is JNot -> context.mkNot(encode(expr.op, context.boolSort) as BoolExpr)
            is JAnd -> context.mkAnd(
                encode(expr.left, context.boolSort) as BoolExpr,
                encode(expr.right, context.boolSort) as BoolExpr
            )
            is JOr -> context.mkOr(
                encode(expr.left, context.boolSort) as BoolExpr,
                encode(expr.right, context.boolSort) as BoolExpr
            )
            is JAdd -> context.mkAdd(
                encode(expr.left, expectedSort) as ArithExpr,
                encode(expr.right, expectedSort) as ArithExpr
            )
            is JSubtract -> context.mkSub(
                encode(expr.left, expectedSort) as ArithExpr,
                encode(expr.right, expectedSort) as ArithExpr
            )
            // TODO: Can we guarantee that Z3 calculates exactly like Java? Otherwise, Z3 might simplify something to
            // TODO: true or false which Java would not do at runtime. Soundness at risk!
            is JMultiply -> context.mkMul(
                encode(expr.left, expectedSort) as ArithExpr,
                encode(expr.right, expectedSort) as ArithExpr
            )
            is JDivide -> context.mkDiv(
                encode(expr.left, expectedSort) as ArithExpr,
                encode(expr.right, expectedSort) as ArithExpr
            )
            is JRemainder -> context.mkRem(
                encode(expr.left, expectedSort) as IntExpr,
                encode(expr.right, expectedSort) as IntExpr
            )
            is JCondition -> {
                val expectedOpSort = getExpectedSort(expr.left.type, expr.right.type)
                val op1 = encode(expr.left, expectedOpSort)
                val op2 = encode(expr.right, expectedOpSort)
                when {
                    expr.symbol is JEquals -> context.mkEq(op1, op2)
                    expr.symbol is JNotEquals -> context.mkNot(context.mkEq(op1, op2))
                    expr.symbol is JGreaterThan -> context.mkGt(op1 as ArithExpr, op2 as ArithExpr)
                    expr.symbol is JGreaterOrEqual -> context.mkGe(op1 as ArithExpr, op2 as ArithExpr)
                    expr.symbol is JLessThan -> context.mkLt(op1 as ArithExpr, op2 as ArithExpr)
                    expr.symbol is JLessOrEqual -> context.mkLe(op1 as ArithExpr, op2 as ArithExpr)

                    else -> TODO("Can't happen")
                }
            }
            is JConstant -> {
                // Even though we have JTrue and JFalse, we might still encounter an integer constant with
                // expectedSort == BoolSort here (nothing in parseJimpleExpression can prevent this).
                // Example: parseJimpleExpression('$i0 == 0') --> since we can't know that $i0 is really a Bool here,
                // '0' is parsed as an integer constant. During refinement, however, inlining of '$i0' might reveal that
                // it's a Bool variable, hence the integer constant must be interpreted as a Bool as well.
                val const = expr.value
                when (const) {
                    is IntConstant -> when (expectedSort) {
                        context.intSort -> context.mkInt(const.value)
                        context.boolSort -> intToBool(const.value)
                        context.realSort -> context.mkReal(const.value)
                        else -> throw IllegalArgumentException("Unexpected 'expectedSort == $expectedSort' when encoding int constant")
                    }
                    is LongConstant -> context.mkInt(const.value)
                    is FloatConstant -> context.mkReal(const.value.toString())
                    is DoubleConstant -> context.mkReal(const.value.toString())
                    is StringConstant -> context.mkString(const.value)
                    else -> TODO("Missing case for ${expr.value.javaClass.name}")
                }
            }
            is JLocal -> getOrCreateSymbol(expr, expectedSort)
            is JInstanceFieldRef -> getOrCreateSymbol(expr, expectedSort)
            is JStaticFieldRef -> getOrCreateSymbol(expr, expectedSort)

            // TODO: Coerce to correct sort! Alternatively (or additionally?) make sure that float constants
            // are encoded as integers if they receive expectedSort==intSort
            is JCast -> {
                val v = encode(expr.expr, expectedSort)
                when {
                    v is IntNum && expectedSort == context.realSort -> context.mkReal(v.int)
                    v is RatNum && expectedSort == context.intSort -> TODO("context.mkInt(???)")
                    else -> v
                }
            }

            is JConditional -> {
                val condition = encode(expr.condition, context.boolSort) as BoolExpr
                val resultSort = getExpectedSort(expr.trueExpr.type, expr.falseExpr.type)
                val trueExpr = encode(expr.trueExpr, resultSort)
                val falseExpr = encode(expr.falseExpr, resultSort)
                context.mkITE(condition, trueExpr, falseExpr)
            }

            is JInstanceOf -> getOrCreateSymbol(expr, expectedSort) // TODO: This could be improved for certain cases
            is JVirtualInvoke -> tryEncodeWellKnownCall(expr) ?: getOrCreateSymbol(expr, expectedSort)
            is JSpecialInvoke -> getOrCreateSymbol(expr, expectedSort)
            is JInterfaceInvoke -> getOrCreateSymbol(expr, expectedSort)
            is JStaticInvoke -> tryEncodeWellKnownStaticCall(expr) ?: getOrCreateSymbol(expr, expectedSort)
            is JDynamicInvoke -> getOrCreateSymbol(expr, expectedSort)
            is JCompare -> throw IllegalArgumentException("${expr.javaClass.name} can't be Z3-encoded and should be eliminated beforehand")
            is JCompareGreater -> throw IllegalArgumentException("${expr.javaClass.name} can't be Z3-encoded and should be eliminated beforehand")
            is JCompareLess -> throw IllegalArgumentException("${expr.javaClass.name} can't be Z3-encoded and should be eliminated beforehand")
            is JNew -> getOrCreateSymbol(expr, expectedSort)
            is JThisRef -> getOrCreateSymbol(expr, expectedSort)
            is JParameterRef -> getOrCreateSymbol(expr, expectedSort)
        }
    } catch (e: Exception) {
        throw Exception("Failed to Z3-encode '$expr' (expectedSort: $expectedSort)", e)
    }

private fun Z3Solver.intToBool(v: Int) = when (v) {
    0 -> context.mkBool(false)
    1 -> context.mkBool(true)
    else -> throw IllegalArgumentException("Cannot interpret '$v' as boolean")
}


//
// Decode Z3 to Jimple
//

private fun Z3Solver.decodeValue(expr: Expr): JExpression = when {
    expr is IntNum ->
        // TODO: Choose int or long on Z3-decode?
        //JConstant(IntConstant.v(Integer.parseInt(expr.toString())))
        JConstant(LongConstant.v(expr.int64))
    expr is RatNum ->
        JConstant(DoubleConstant.v(expr.numerator.int.toDouble() / expr.denominator.int.toDouble()))
    expr.isString -> JConstant(StringConstant.v(expr.string))
    expr.isBool && expr.toString() == "true" -> JTrue
    expr.isBool && expr.toString() == "false" -> JFalse
    expr.isConst && expr.toString() == "null" -> JNull
    expr.isConst -> {
        // From 'this.symbols', find the ValueWithContext corresponding to the symbol used in the const-expr here
        val symbolName = expr.toString().trim('|')
        symbols.asIterable().firstOrNull { it.value.toString() == symbolName }?.key
            ?: throw Exception("Can't decode $expr")
    }
    else -> throw NotImplementedError("Not implemented: Translation of Z3 '$expr' to Jimple equivalent")
}

fun Z3Solver.decode(expr: Expr): JExpression =
    try {
        // TODO: Make more operators support >2 arguments
        when {
            expr.isAnd -> expr.args.map(::decode).fold(JTrue, ::and)
            expr.isOr -> expr.args.map(::decode).fold(JFalse, ::or)
            expr.isEq -> JCondition(decode(expr.args[0]), decode(expr.args[1]), JEquals)
            expr.isNot && expr.args[0].isEq -> JCondition(decode(expr.args[0].args[0]), decode(expr.args[0].args[1]), JNotEquals)
            expr.isGT -> JCondition(decode(expr.args[0]), decode(expr.args[1]), JGreaterThan)
            expr.isGE -> JCondition(decode(expr.args[0]), decode(expr.args[1]), JGreaterOrEqual)
            expr.isLT -> JCondition(decode(expr.args[0]), decode(expr.args[1]), JLessThan)
            expr.isLE -> JCondition(decode(expr.args[0]), decode(expr.args[1]), JLessOrEqual)
            expr.isNot -> not(decode(expr.args[0]))
            expr.isAdd -> JAdd(decode(expr.args[0]), decode(expr.args[1]))
            expr.isSub -> JSubtract(decode(expr.args[0]), decode(expr.args[1]))
            expr.isMul -> JMultiply(decode(expr.args[0]), decode(expr.args[1]))
            expr.isDiv -> JDivide(decode(expr.args[0]), decode(expr.args[1]))
            expr.isITE -> {
                val condition = decode(expr.args[0])
                val trueExpr = decode(expr.args[1])
                val falseExpr = decode(expr.args[2])
                conditional(condition, trueExpr, falseExpr)
            }
            else -> decodeValue(expr)
        }
    } catch (e: Exception) {
        throw Exception("Failed to Z3-decode '$expr'", e)
    }
