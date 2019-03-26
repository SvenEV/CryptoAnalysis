package crypto.pathconditions.z3

import crypto.pathconditions.expressions.*
import com.google.common.cache.*
import com.microsoft.z3.*
import com.microsoft.z3.Context
import com.microsoft.z3.Expr
import com.microsoft.z3.enumerations.Z3_decl_kind
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
    val floatSort: FPSort,
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
    val floatSort = context.mkFPSortDouble()
    return Z3Solver(
        context,
        mutableMapOf(),
        context.mkTrue(),
        context.mkFalse(),
        context.mkSymbol("null"),
        objSort,
        floatSort,
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
    t == FloatType.v() -> floatSort
    t == DoubleType.v() -> floatSort
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
    val symbol = symbols.computeIfAbsent(v) { context.mkSymbol(it.toString(WithContextFormat.Default)) }
    return context.mkConst(symbol, sort)
}

private fun Z3Solver.tryEncodeWellKnownCall(expr: JVirtualInvoke): Expr? = when {
    expr.method.toString() == "<java.lang.String: boolean equals(java.lang.Object)>" -> {
        val base = (expr.base as? JConstant)?.v?.value as? StringConstant
        val other = (expr.args.elementAtOrNull(0) as? JConstant)?.v?.value as? StringConstant
        when {
            base != null && other != null -> if (base.value == other.value) trueExpr else falseExpr
            else -> null
        }
    }
    else -> null
}

private fun Z3Solver.tryEncodeWellKnownStaticCall(expr: JStaticInvoke): Expr? = when {
    expr.method.toString() == "<kotlin.jvm.internal.Intrinsics: boolean areEqual(java.lang.Object,java.lang.Object)>" -> {
        val op1 = (expr.args.elementAtOrNull(0) as? JConstant)?.v?.value as? StringConstant
        val op2 = (expr.args.elementAtOrNull(0) as? JConstant)?.v?.value as? StringConstant
        when {
            op1 != null && op2 != null -> if (op1.value == op2.value) trueExpr else falseExpr
            else -> null
        }
    }
    else -> null
}

/** Helper function that produces either an integer or a floating point operation, depending on the sort of operands */
private fun Context.mkArithOrFPOp(
    arithOp: (Array<ArithExpr>) -> ArithExpr,
    fpOp: (FPRMExpr, FPExpr, FPExpr) -> FPExpr
) = { left: Expr, right: Expr ->
    when {
        left is ArithExpr && right is ArithExpr -> arithOp(arrayOf(left, right))
        left is FPExpr && right is FPExpr -> fpOp(mkFPRoundNearestTiesToEven(), left, right) // TODO: Extract constant
        else -> throw IllegalArgumentException("Can't combine expressions of type '${left.javaClass.name}' and '${right.javaClass.name}'")
    }
}

private val Context.mkAddOrFPAdd get() = mkArithOrFPOp(::mkAdd, ::mkFPAdd)
private val Context.mkSubOrFPSub get() = mkArithOrFPOp(::mkSub, ::mkFPSub)
private val Context.mkMulOrFPMul get() = mkArithOrFPOp(::mkMul, ::mkFPMul)
private val Context.mkDivOrFPDiv get() = mkArithOrFPOp({ ops -> mkDiv(ops[0], ops[1]) }, ::mkFPDiv)

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
            is JAdd -> context.mkAddOrFPAdd(
                encode(expr.left, expectedSort),
                encode(expr.right, expectedSort)
            )
            is JSubtract -> context.mkSubOrFPSub(
                encode(expr.left, expectedSort),
                encode(expr.right, expectedSort)
            )
            // TODO: Can we guarantee that Z3 calculates exactly like Java? Otherwise, Z3 might simplify something to
            // TODO: true or false which Java would not do at runtime. Soundness at risk!
            is JMultiply -> context.mkMulOrFPMul(
                encode(expr.left, expectedSort),
                encode(expr.right, expectedSort)
            )
            is JDivide -> context.mkDivOrFPDiv(
                encode(expr.left, expectedSort),
                encode(expr.right, expectedSort)
            )
            is JRemainder -> context.mkRem(
                encode(expr.left, expectedSort) as IntExpr,
                encode(expr.right, expectedSort) as IntExpr
            )
            is JCondition -> {
                val expectedOpSort = getExpectedSort(expr.left.type, expr.right.type)
                val isFP = expectedOpSort == floatSort
                val op1 = encode(expr.left, expectedOpSort)
                val op2 = encode(expr.right, expectedOpSort)
                when {
                    expr.symbol is JEquals -> context.mkEq(op1, op2)
                    expr.symbol is JNotEquals -> context.mkNot(context.mkEq(op1, op2))

                    isFP && expr.symbol is JGreaterThan -> context.mkFPGt(op1 as FPExpr, op2 as FPExpr)
                    isFP && expr.symbol is JGreaterOrEqual -> context.mkFPGEq(op1 as FPExpr, op2 as FPExpr)
                    isFP && expr.symbol is JLessThan -> context.mkFPLt(op1 as FPExpr, op2 as FPExpr)
                    isFP && expr.symbol is JLessOrEqual -> context.mkFPLEq(op1 as FPExpr, op2 as FPExpr)

                    expr.symbol is JGreaterThan -> context.mkGt(op1 as IntExpr, op2 as IntExpr)
                    expr.symbol is JGreaterOrEqual -> context.mkGe(op1 as IntExpr, op2 as IntExpr)
                    expr.symbol is JLessThan -> context.mkLt(op1 as IntExpr, op2 as IntExpr)
                    expr.symbol is JLessOrEqual -> context.mkLe(op1 as IntExpr, op2 as IntExpr)

                    else -> TODO("Can't happen")
                }
            }
            is JConstant -> {
                // Even though we have JTrue and JFalse, we might still encounter an integer constant with
                // expectedSort == BoolSort here (nothing in parseJimpleExpression can prevent this).
                // Example: parseJimpleExpression('$i0 == 0') --> since we can't know that $i0 is really a Bool here,
                // '0' is parsed as an integer constant. During refinement, however, inlining of '$i0' might reveal that
                // it's a Bool variable, hence the integer constant must be interpreted as a Bool as well.
                val const = expr.v.value
                when (const) {
                    is IntConstant -> when (expectedSort) {
                        context.intSort -> context.mkInt(const.value)
                        context.boolSort -> intToBool(const.value)
                        floatSort -> context.mkFP(const.value, floatSort)
                        else -> throw IllegalArgumentException("Unexpected 'expectedSort == $expectedSort' when encoding int constant")
                    }
                    is LongConstant -> context.mkInt(const.value)
                    is FloatConstant -> context.mkFP(const.value, floatSort)
                    is DoubleConstant -> context.mkFP(const.value, floatSort)
                    is StringConstant -> context.mkString(const.value)
                    else -> TODO("Missing case for ${expr.v.value.javaClass.name}")
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
                    v is IntNum && expectedSort == floatSort -> context.mkFP(v.int, floatSort)
                    v is FPNum && expectedSort == context.intSort -> TODO("context.mkInt(v.???)...")
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
    expr.isIntNum ->
        // TODO: Choose int or long on Z3-decode?
        //JConstant(WithContext(IntConstant.v(Integer.parseInt(expr.toString())), null, null))
        JConstant(WithContext(LongConstant.v(expr.toString().toLong()), null, null))
    expr.isFloatNum -> {
        val v = constructDouble(expr as FPNum)
        JConstant(WithContext(DoubleConstant.v(v), null, null))
    }
    expr.isString -> JConstant(WithContext(StringConstant.v(expr.string), null, null))
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
        when {
            expr.isAnd -> JAnd(decode(expr.args[0]), decode(expr.args[1]))
            expr.isOr -> JOr(decode(expr.args[0]), decode(expr.args[1]))
            expr.isEq -> JCondition(decode(expr.args[0]), decode(expr.args[1]), JEquals)
            expr.isNot && expr.args[0].isEq -> JCondition(decode(expr.args[0].args[0]), decode(expr.args[0].args[1]), JNotEquals)
            expr.isGT || expr.isFPGT -> JCondition(decode(expr.args[0]), decode(expr.args[1]), JGreaterThan)
            expr.isGE || expr.isFPGE -> JCondition(decode(expr.args[0]), decode(expr.args[1]), JGreaterOrEqual)
            expr.isLT || expr.isFPLT -> JCondition(decode(expr.args[0]), decode(expr.args[1]), JLessThan)
            expr.isLE || expr.isFPLE -> JCondition(decode(expr.args[0]), decode(expr.args[1]), JLessOrEqual)
            expr.isNot -> not(decode(expr.args[0]))
            expr.isAdd -> JAdd(decode(expr.args[0]), decode(expr.args[1]))
            expr.isSub -> JSubtract(decode(expr.args[0]), decode(expr.args[1]))
            expr.isMul -> JMultiply(decode(expr.args[0]), decode(expr.args[1]))
            expr.isDiv -> JDivide(decode(expr.args[0]), decode(expr.args[1]))
            expr.isFPAdd -> JAdd(decode(expr.args[1]), decode(expr.args[2]))
            expr.isFPSub -> JSubtract(decode(expr.args[1]), decode(expr.args[2]))
            expr.isFPMul -> JMultiply(decode(expr.args[1]), decode(expr.args[2]))
            expr.isFPDiv -> JDivide(decode(expr.args[1]), decode(expr.args[2]))
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

val Expr.isFPGT get() = isApp && funcDecl.declKind == Z3_decl_kind.Z3_OP_FPA_GT
val Expr.isFPGE get() = isApp && funcDecl.declKind == Z3_decl_kind.Z3_OP_FPA_GE
val Expr.isFPLT get() = isApp && funcDecl.declKind == Z3_decl_kind.Z3_OP_FPA_LT
val Expr.isFPLE get() = isApp && funcDecl.declKind == Z3_decl_kind.Z3_OP_FPA_LE
val Expr.isFPAdd get() = isApp && funcDecl.declKind == Z3_decl_kind.Z3_OP_FPA_ADD
val Expr.isFPSub get() = isApp && funcDecl.declKind == Z3_decl_kind.Z3_OP_FPA_SUB
val Expr.isFPMul get() = isApp && funcDecl.declKind == Z3_decl_kind.Z3_OP_FPA_MUL
val Expr.isFPDiv get() = isApp && funcDecl.declKind == Z3_decl_kind.Z3_OP_FPA_DIV
val Expr.isFloatNum get() = funcDecl.declKind == Z3_decl_kind.Z3_OP_FPA_NUM

fun constructDouble(num: FPNum): Double {
    // Adapted from https://github.com/delcypher/jfs/blob/4cb90edfc3ea89ce5477a15a4102d7f3bb5bdb61/runtime/SMTLIB/SMTLIB/NativeFloat.cpp#L666
    // (found via https://stackoverflow.com/questions/48930084/z3-smt-solver-how-can-i-extract-the-value-of-a-floating-point-number-in-fpa)
    val sign = if (num.sign) 1L else 0L // true <=> negative <=> 1L
    val exponent = num.getExponentInt64(true) // biased = true
    val significand = num.significandUInt64
    return Double.fromBits(significand or (exponent shl 52) or (sign shl 63))
}