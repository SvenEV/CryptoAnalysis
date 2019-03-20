package crypto.pathconditions.expressions

import crypto.pathconditions.debug.prettyPrint
import crypto.pathconditions.ofType
import soot.*
import soot.Unit
import soot.jimple.*
import soot.jimple.internal.JLengthExpr

//
// This file contains a custom Java expression tree object model.
// Jimple expressions and Z3 expressions can be parsed into instances of this model
// and it supports String formatting that produces readable Java code.
//
// Why do we need an intermediary tree model between Jimple and Z3?
// 1. We can't represent expression inlining in Jimple due to the 3-address format. For example, `if (a.equals(b))` is
//    unrepresentable – putting such conditions into an `IfStmt` throws
// 2. Z3 does not provide a proper object model that we could use
//

/**
 * A Jimple 'Value' enriched with containing statement and method
 */
typealias ValueWithContext = WithContext<Value>

data class WithContext<T : Value>(val value: T, val unit: Unit?, val method: SootMethod?) {
    override fun equals(other: Any?) = other?.javaClass == javaClass &&
        other is WithContext<*> &&
        other.value.equivTo(value) &&
        other.unit == unit &&
        other.method == method

    override fun hashCode(): Int {
        var result = value.hashCode()
        result = 31 * result + (unit?.hashCode() ?: 0)
        result = 31 * result + (method?.hashCode() ?: 0)
        return result
    }

    override fun toString() = prettyPrint(WithContextFormat.Default)

    fun prettyPrint(format: WithContextFormat) = when (format) {
        WithContextFormat.Default ->
            value.toString() + "-@-" +
                method?.name + ":" +
                method?.activeBody?.units?.indexOf(unit!!)
        WithContextFormat.Multiline ->
            value.toString() + "\n" +
                method?.name + ":" +
                method?.activeBody?.units?.indexOf(unit!!)
        WithContextFormat.ContextFree ->
            value.toString()
    }
}

/**
 * Options of how to format a [WithContext] as String.
 */
enum class WithContextFormat {
    Default, // 'x @ methodName:12'
    Multiline, // 'x\nmethodName:12'
    ContextFree // 'x'
}

private fun validateBool(t: Type) {
    if (t != BooleanType.v())
        throw IllegalArgumentException("Expected boolean expression but got expression of type '${t.prettyPrint()}'")
}

sealed class JExpression {
    override fun toString() = toString(WithContextFormat.Default)

    // For Java interop:
    fun prettyPrint(format: WithContextFormat) = toString(format)

    fun getType() = type
}

// CONSTANTS
object JTrue : JExpression()

object JFalse : JExpression()

object JNull : JExpression()

data class JConstant(val v: WithContext<Constant>) : JExpression() {
    init {
        if (v.value is NullConstant) throw IllegalArgumentException("Use JNull instead")
    }

    override fun toString() = super.toString()
}

// LOCAL
data class JLocal(val v: WithContext<Local>, val actualType: Type) : JExpression() {
    override fun toString() = super.toString()
}

// VARIOUS OPERATORS
data class JCast(val expr: JExpression, val castType: Type) : JExpression() {
    override fun toString() = super.toString()
}

data class JInstanceOf(val expr: JExpression, val checkType: Type) : JExpression() {
    override fun toString() = super.toString()
}

data class JConditional(val condition: JExpression, val trueExpr: JExpression, val falseExpr: JExpression) : JExpression() {
    init {
        if (condition.type != BooleanType.v()) throw IllegalArgumentException("Condition must be of type Boolean")
        if (trueExpr.type != falseExpr.type) throw IllegalArgumentException("True and false parts of a JConditional must have the same type (got '${trueExpr.type}' and '${falseExpr.type}')")
    }

    override fun toString() = super.toString()
}

// INVOKEEXPRS
data class JVirtualInvoke(val base: JExpression, val method: SootMethod, val args: List<JExpression>) :
    JExpression() {
    override fun toString() = super.toString()
}

data class JSpecialInvoke(val base: JExpression, val method: SootMethod, val args: List<JExpression>) :
    JExpression() {
    override fun toString() = super.toString()
}

data class JInterfaceInvoke(val base: JExpression, val method: SootMethod, val args: List<JExpression>) :
    JExpression() {
    override fun toString() = super.toString()
}

data class JStaticInvoke(val method: SootMethod, val args: List<JExpression>) :
    JExpression() {
    override fun toString() = super.toString()
}

data class JDynamicInvoke(val method: SootMethod, val args: List<JExpression>) :
    JExpression() {
    override fun toString() = super.toString()
}

data class JNew(val args: List<JExpression>, val baseType: Type) : JExpression() {
    override fun toString() = super.toString()
}

// REF
data class JInstanceFieldRef(val base: JExpression, val field: SootField) : JExpression() {
    override fun toString() = super.toString()
}

data class JStaticFieldRef(val field: SootField) : JExpression() {
    override fun toString() = super.toString()
}

data class JThisRef(val thisType: Type) : JExpression() {
    override fun toString() = super.toString()
}

data class JParameterRef(val index: Int, val paramType: Type) : JExpression() {
    override fun toString() = super.toString()
}

// UNOPEXPR
data class JNot(val op: JExpression) : JExpression() {
    init {
        validateBool(op.type)
    }

    override fun toString() = super.toString()
}

// BINOPEXPR
data class JCompareGreater(val left: JExpression, val right: JExpression) : JExpression() {
    override fun toString() = super.toString()
}

data class JCompareLess(val left: JExpression, val right: JExpression) : JExpression() {
    override fun toString() = super.toString()
}

data class JAdd(val left: JExpression, val right: JExpression) : JExpression() {
    override fun toString() = super.toString()
}

data class JSubtract(val left: JExpression, val right: JExpression) : JExpression() {
    override fun toString() = super.toString()
}

data class JMultiply(val left: JExpression, val right: JExpression) : JExpression() {
    override fun toString() = super.toString()
}

data class JDivide(val left: JExpression, val right: JExpression) : JExpression() {
    override fun toString() = super.toString()
}

data class JRemainder(val left: JExpression, val right: JExpression) : JExpression() {
    override fun toString() = super.toString()
}

data class JAnd(val left: JExpression, val right: JExpression) : JExpression() {
    init {
        validateBool(left.type)
        validateBool(right.type)
    }

    override fun toString() = super.toString()
}

data class JOr(val left: JExpression, val right: JExpression) : JExpression() {
    init {
        validateBool(left.type)
        validateBool(right.type)
    }

    override fun toString() = super.toString()
}

/** Represents ==, !=, >, >=, < and <= expressions */
data class JCondition(val left: JExpression, val right: JExpression, val symbol: LeafConditionSymbol) : JExpression() {
    override fun toString() = super.toString()
}

sealed class LeafConditionSymbol(val symbol: String, val precedence: Int, val associativity: Associativity, negate: () -> LeafConditionSymbol) {
    val negated by lazy(negate)
    override fun toString() = symbol
}

object JEquals : LeafConditionSymbol("==", 8, Associativity.LeftToRight, { JNotEquals })
object JNotEquals : LeafConditionSymbol("!=", 8, Associativity.LeftToRight, { JEquals })
object JGreaterThan : LeafConditionSymbol(">", 9, Associativity.NotAssociative, { JLessOrEqual })
object JGreaterOrEqual : LeafConditionSymbol(">=", 9, Associativity.NotAssociative, { JLessThan })
object JLessThan : LeafConditionSymbol("<", 9, Associativity.NotAssociative, { JGreaterOrEqual })
object JLessOrEqual : LeafConditionSymbol("<=", 9, Associativity.NotAssociative, { JGreaterThan })


//
// Parsing/construction functions
//

fun Sequence<JExpression>.joinAnd() = fold(JTrue, ::and)

fun JExpression.replace(cond: JExpression, replacement: JExpression): JExpression =
    if (this == cond)
        replacement
    else
        when (this) {
            JTrue -> JTrue
            JFalse -> JFalse
            is JAnd -> and(left.replace(cond, replacement), right.replace(cond, replacement))
            is JOr -> or(left.replace(cond, replacement), right.replace(cond, replacement))
            else -> this
        }

fun and(left: JExpression, right: JExpression): JExpression = when {
    left is JTrue -> right
    right is JTrue -> left
    left is JFalse -> JFalse
    right is JFalse -> JFalse
    left == not(right) -> JFalse
    right == not(left) -> JFalse
    else -> {
        // When constructing 'expr && term', replace 'expr' with 'true' in 'term'
        val rightRefined = right.replace(left, JTrue)
        if (rightRefined == right)
            JAnd(left, right)
        else
            and(left, rightRefined)
    }
}

fun or(left: JExpression, right: JExpression): JExpression = when {
    left is JTrue -> JTrue
    right is JTrue -> JTrue
    left is JFalse -> right
    right is JFalse -> left
    left == not(right) -> JTrue
    right == not(left) -> JTrue
    else -> {
        // When constructing 'expr || term', replace 'expr' with 'false' in 'term'
        val rightRefined = right.replace(left, JFalse)
        if (rightRefined == right)
            JOr(left, right)
        else
            or(left, rightRefined)
    }
}

/**
 * Contains a targeted workaround for bool/int type incompatibility when constructing a [JConditional]:
 * If one part is of type Boolean, treat the other as Boolean, too.
 */
fun conditional(condition: JExpression, trueExpr: JExpression, falseExpr: JExpression): JExpression {
    val leftIsBool = trueExpr.type == BooleanType.v()
    val rightIsBool = falseExpr.type == BooleanType.v()
    val leftAsInt = (trueExpr as? JConstant)?.v?.value as? IntConstant
    val rightAsInt = (falseExpr as? JConstant)?.v?.value as? IntConstant
    return when {
        leftIsBool && rightAsInt != null -> JConditional(condition, trueExpr, intToBool(rightAsInt.value))
        rightIsBool && leftAsInt != null -> JConditional(condition, intToBool(leftAsInt.value), falseExpr)
        else -> JConditional(condition, trueExpr, falseExpr)
    }
}

fun not(cond: JExpression): JExpression = when (cond) {
    is JTrue -> JFalse
    is JFalse -> JTrue
    is JNot -> cond.op
    is JAnd -> JOr(not(cond.left), not(cond.right))
    is JOr -> JAnd(not(cond.left), not(cond.right))
    is JCondition -> JCondition(cond.left, cond.right, cond.symbol.negated)
    else -> JNot(cond)
}

sealed class TypeHint
object NoTypeHint : TypeHint()
object ForceBool : TypeHint()

fun intToBool(i: Int) = when (i) {
    0 -> JFalse
    1 -> JTrue
    else -> throw IllegalArgumentException("Cannot interpret '$i' as boolean")
}

/**
 * Turns a Jimple 'Value' into an instance of our custom expression tree model.
 */
fun parseJimpleExpression(expr: ValueWithContext, typeHint: TypeHint): JExpression {
    try {
        val v = expr.value
        return when (v) {
            is IntConstant -> when (typeHint) {
                NoTypeHint -> JConstant(WithContext(v, expr.unit, expr.method))
                ForceBool -> intToBool(v.value)
            }

            is NullConstant -> JNull

            is Constant -> JConstant(WithContext(v, expr.unit, expr.method))

            is CastExpr -> JCast(parseJimpleExpression(expr.copy(value = v.op), NoTypeHint), v.castType)
            is InstanceOfExpr -> JInstanceOf(parseJimpleExpression(expr.copy(value = v.op), NoTypeHint), v.checkType)
            is Local -> JLocal(WithContext(v, expr.unit, expr.method), when (typeHint) {
                is ForceBool -> BooleanType.v()
                is NoTypeHint -> v.type
            })

            is InstanceFieldRef -> JInstanceFieldRef(parseJimpleExpression(expr.copy(value = v.base), NoTypeHint), v.field)
            is StaticFieldRef -> JStaticFieldRef(v.field)

            is VirtualInvokeExpr -> JVirtualInvoke(
                parseJimpleExpression(expr.copy(value = v.base), NoTypeHint),
                v.method,
                v.args.map { parseJimpleExpression(expr.copy(value = it), NoTypeHint) })

            is SpecialInvokeExpr -> JSpecialInvoke(
                parseJimpleExpression(expr.copy(value = v.base), NoTypeHint),
                v.method,
                v.args.map { parseJimpleExpression(expr.copy(value = it), NoTypeHint) })

            is InterfaceInvokeExpr -> JInterfaceInvoke(
                parseJimpleExpression(expr.copy(value = v.base), NoTypeHint),
                v.method,
                v.args.map { parseJimpleExpression(expr.copy(value = it), NoTypeHint) })

            is StaticInvokeExpr -> JStaticInvoke(
                v.method,
                v.args.map { parseJimpleExpression(expr.copy(value = it), NoTypeHint) })

            is DynamicInvokeExpr -> JDynamicInvoke(
                v.method,
                v.args.map { parseJimpleExpression(expr.copy(value = it), NoTypeHint) })

            is NewExpr -> {
                // Find constructor call statement to get constructor arguments
                val targetVariable = (expr.unit as AssignStmt).leftOp
                val constructorCall = expr.method!!.activeBody.units
                    .ofType<InvokeStmt>()
                    .single { it.invokeExpr is SpecialInvokeExpr && it.invokeExpr.method.isConstructor && (it.invokeExpr as SpecialInvokeExpr).base == targetVariable }
                JNew(
                    constructorCall.invokeExpr.args.map { parseJimpleExpression(expr.copy(value = it), NoTypeHint) },
                    v.baseType
                )
            }

            is NegExpr -> JNot(parseJimpleExpression(expr.copy(value = v.op), ForceBool))

            is BinopExpr -> {
                val typeHint = if (v.op1.type == BooleanType.v() || v.op2.type == BooleanType.v()) ForceBool else NoTypeHint
                val op1 = parseJimpleExpression(expr.copy(value = v.op1), typeHint)
                val op2 = parseJimpleExpression(expr.copy(value = v.op2), typeHint)
                when (v) {
                    is CmpgExpr -> JCompareGreater(op1, op2)
                    is CmplExpr -> JCompareLess(op1, op2)
                    is AddExpr -> JAdd(op1, op2)
                    is SubExpr -> JSubtract(op1, op2)
                    is MulExpr -> JMultiply(op1, op2)
                    is DivExpr -> JDivide(op1, op2)
                    is RemExpr -> JRemainder(op1, op2)
                    is ConditionExpr -> JCondition(op1, op2, when (v) {
                        is EqExpr -> JEquals
                        is NeExpr -> JNotEquals
                        is GtExpr -> JGreaterThan
                        is GeExpr -> JGreaterOrEqual
                        is LtExpr -> JLessThan
                        is LeExpr -> JLessOrEqual
                        else -> TODO("Can't happen")
                    })
                    else -> TODO("Parsing of Jimple '${v.javaClass.name}' (example: '${v.prettyPrint()}')")
                }
            }

            is JLengthExpr -> {
                val op = parseJimpleExpression(expr.copy(value = v.op), NoTypeHint)
                JInstanceFieldRef(op, SootField("length", IntType.v()))
            }

            is ThisRef -> JThisRef(v.type)
            is ParameterRef -> JParameterRef(v.index, v.type)

            else -> TODO("Parsing of Jimple '${v.javaClass.name}' (example: '${v.prettyPrint()}')")
        }
    } catch (e: Exception) {
        throw Exception("Failed to parse Jimple expression '$expr'", e)
    }
}


//
// Type, precedence, associativity and pretty printing of JExpressions
//

val JExpression.type
    get(): Type = when (this) {
        JTrue -> BooleanType.v()
        JFalse -> BooleanType.v()
        JNull -> NullType.v()
        is JConstant -> v.value.type
        is JLocal -> actualType
        is JCast -> castType
        is JInstanceOf -> BooleanType.v()
        is JConditional -> trueExpr.type
        is JVirtualInvoke -> method.returnType
        is JSpecialInvoke -> method.returnType
        is JInterfaceInvoke -> method.returnType
        is JStaticInvoke -> method.returnType
        is JDynamicInvoke -> method.returnType
        is JNew -> baseType
        is JInstanceFieldRef -> field.type
        is JStaticFieldRef -> field.type
        is JThisRef -> thisType
        is JParameterRef -> paramType
        is JNot -> BooleanType.v()
        is JCompareGreater -> left.type
        is JCompareLess -> left.type
        is JAdd -> left.type
        is JSubtract -> left.type
        is JMultiply -> left.type
        is JDivide -> left.type
        is JRemainder -> left.type
        is JAnd -> BooleanType.v()
        is JOr -> BooleanType.v()
        is JCondition -> BooleanType.v()
    }

/**
 * Taken from https://introcs.cs.princeton.edu/java/11precedence/.
 * Note: Only operators have a precedence. For terminals like constants, locals and 'this' we just assign
 * the maximum value.
 */
const val MAX_PRECEDENCE = 20
val JExpression.precedence
    get() = when (this) {
        JTrue -> MAX_PRECEDENCE
        JFalse -> MAX_PRECEDENCE
        JNull -> MAX_PRECEDENCE
        is JConstant -> MAX_PRECEDENCE
        is JLocal -> MAX_PRECEDENCE
        is JCast -> 13
        is JInstanceOf -> 9
        is JConditional -> 2
        is JVirtualInvoke -> MAX_PRECEDENCE
        is JSpecialInvoke -> MAX_PRECEDENCE
        is JInterfaceInvoke -> MAX_PRECEDENCE
        is JStaticInvoke -> MAX_PRECEDENCE
        is JDynamicInvoke -> MAX_PRECEDENCE
        is JNew -> 13
        is JInstanceFieldRef -> 16
        is JStaticFieldRef -> 16
        is JThisRef -> MAX_PRECEDENCE
        is JParameterRef -> MAX_PRECEDENCE
        is JNot -> 14
        is JCompareGreater -> 9
        is JCompareLess -> 9
        is JAdd -> 11
        is JSubtract -> 11
        is JMultiply -> 12
        is JDivide -> 12
        is JRemainder -> 12
        is JAnd -> 4
        is JOr -> 3
        is JCondition -> symbol.precedence
    }

/*
 * Taken from https://introcs.cs.princeton.edu/java/11precedence/.
 */
enum class Associativity { LeftToRight, RightToLeft, NotAssociative }

val JExpression.associativity
    get() = when (this) {
        JTrue -> Associativity.NotAssociative
        JFalse -> Associativity.NotAssociative
        JNull -> Associativity.NotAssociative
        is JConstant -> Associativity.NotAssociative
        is JLocal -> Associativity.NotAssociative
        is JCast -> Associativity.RightToLeft
        is JInstanceOf -> Associativity.NotAssociative
        is JConditional -> Associativity.RightToLeft
        is JVirtualInvoke -> Associativity.LeftToRight
        is JSpecialInvoke -> Associativity.LeftToRight
        is JInterfaceInvoke -> Associativity.LeftToRight
        is JStaticInvoke -> Associativity.LeftToRight
        is JDynamicInvoke -> Associativity.LeftToRight
        is JNew -> Associativity.RightToLeft
        is JInstanceFieldRef -> Associativity.LeftToRight
        is JStaticFieldRef -> Associativity.LeftToRight
        is JThisRef -> Associativity.NotAssociative
        is JParameterRef -> Associativity.NotAssociative
        is JNot -> Associativity.RightToLeft
        is JCompareGreater -> Associativity.NotAssociative
        is JCompareLess -> Associativity.NotAssociative
        is JAdd -> Associativity.LeftToRight
        is JSubtract -> Associativity.LeftToRight
        is JMultiply -> Associativity.LeftToRight
        is JDivide -> Associativity.LeftToRight
        is JRemainder -> Associativity.LeftToRight
        is JAnd -> Associativity.LeftToRight
        is JOr -> Associativity.LeftToRight
        is JCondition -> symbol.associativity
    }

fun JExpression.toString(format: WithContextFormat): String = when (this) {
    JTrue -> "true"
    JFalse -> "false"
    JNull -> "null"
    is JConstant -> v.value.prettyPrint()
    is JLocal -> v.prettyPrint(format)
    is JCast -> "(${castType.prettyPrint()}) ${expr.toString(format)}"
    is JInstanceOf -> "${childToString(expr, format)} instanceof ${checkType.prettyPrint()}"
    is JConditional -> "${childToString(condition, format)} ? ${childToString(trueExpr, format)} : ${childToString(falseExpr, format)}"
    is JVirtualInvoke -> "${childToString(base, format, OpPos.Left)}.${method.name}(${args.joinToString { it.toString(format) }})"
    is JSpecialInvoke -> "${childToString(base, format, OpPos.Left)}.${method.name}(${args.joinToString { it.toString(format) }})"
    is JInterfaceInvoke -> "${childToString(base, format, OpPos.Left)}.${method.name}(${args.joinToString { it.toString(format) }})"
    is JStaticInvoke -> "${method.declaringClass.type.prettyPrint()}.${method.name}(${args.joinToString { it.toString(format) }})"
    is JDynamicInvoke -> "${method.declaringClass.type.prettyPrint()}.${method.name}(${args.joinToString { it.toString(format) }})"
    is JNew -> "new ${baseType.prettyPrint()}(${args.joinToString { it.toString(format) }})"
    is JInstanceFieldRef -> "${childToString(base, format, OpPos.Left)}.${field.name}"
    is JStaticFieldRef -> "${field.declaringClass.type.prettyPrint()}.${field.name}"
    is JThisRef -> "this"
    is JParameterRef -> "\$param$index" // TODO: Parameter names seem not to be preserved in Soot
    is JNot -> "!${childToString(op, format, OpPos.Right)}"
    is JCompareGreater -> "${childToString(left, format)} cmpg ${childToString(right, format)}"
    is JCompareLess -> "${childToString(left, format)} cmpl ${childToString(right, format)}"
    is JAdd -> "${childToString(left, format, OpPos.Left)} + ${childToString(right, format, OpPos.Right)}"
    is JSubtract -> "${childToString(left, format, OpPos.Left)} - ${childToString(right, format, OpPos.Right)}"
    is JMultiply -> "${childToString(left, format, OpPos.Left)} * ${childToString(right, format, OpPos.Right)}"
    is JDivide -> "${childToString(left, format, OpPos.Left)} / ${childToString(right, format, OpPos.Right)}"
    is JRemainder -> "${childToString(left, format, OpPos.Left)} % ${childToString(right, format, OpPos.Right)}"
    is JAnd -> "${childToString(left, format, OpPos.Left)} && ${childToString(right, format, OpPos.Right)}"
    is JOr -> "${childToString(left, format, OpPos.Left)} || ${childToString(right, format, OpPos.Right)}"
    is JCondition -> "${childToString(left, format, OpPos.Left)} $symbol ${childToString(right, format, OpPos.Right)}"
}

/** Identifies the position of an operand in a (binary) operation */
enum class OpPos { Left, Right, NotApplicable }

/** Surrounds an operand with parentheses if necessary */
fun JExpression.childToString(child: JExpression, format: WithContextFormat, position: OpPos = OpPos.NotApplicable): String {
    val str = child.toString(format)
    fun strWithParens() = if (str.contains(" ")) "($str)" else str

    // Don't surround child with parentheses in the following cases:
    // - child operator binds stronger than parent
    // - child and parent have same precedence and their associativity allows us to leave out parentheses
    return when {
        precedence < child.precedence -> str
        precedence == child.precedence -> when {
            associativity == Associativity.LeftToRight && position == OpPos.Left -> str
            associativity == Associativity.RightToLeft && position == OpPos.Right -> str
            else -> strWithParens()
        }
        else -> strWithParens()
    }
}