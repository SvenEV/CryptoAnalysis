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
            value.toString() + " @ " +
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

sealed class JExpression(val type: Type) {
    override fun toString() = toString(WithContextFormat.Default)
    abstract fun toString(format: WithContextFormat): String
}

// CONSTANTS
object JTrue : JExpression(BooleanType.v()) {
    override fun toString(format: WithContextFormat) = "true"
}

object JFalse : JExpression(BooleanType.v()) {
    override fun toString(format: WithContextFormat) = "false"
}

object JNull : JExpression(NullType.v()) {
    override fun toString(format: WithContextFormat) = "null"
}

data class JConstant(val v: WithContext<Constant>) : JExpression(v.value.type) {
    init {
        if (v.value is NullConstant) throw IllegalArgumentException("Use JNull instead")
    }

    override fun toString() = super.toString()
    override fun toString(format: WithContextFormat) = v.value.prettyPrint()
}

// LOCAL
data class JLocal(val v: WithContext<Local>) : JExpression(v.value.type) {
    override fun toString() = super.toString()
    override fun toString(format: WithContextFormat) = v.prettyPrint(format)
}

data class JCast(val expr: JExpression, val castType: Type) : JExpression(castType) {
    override fun toString() = super.toString()
    override fun toString(format: WithContextFormat) = "(${castType.prettyPrint()}) ${expr.toString(format)}"
}

data class JInstanceOf(val expr: JExpression, val checkType: Type) : JExpression(BooleanType.v()) {
    override fun toString() = super.toString()
    override fun toString(format: WithContextFormat) = "${expr.toString(format)} instanceof ${checkType.prettyPrint()}"
}

// INVOKEEXPRS
data class JVirtualInvoke(val base: JExpression, val method: SootMethod, val args: List<JExpression>) :
    JExpression(method.returnType) {
    override fun toString() = super.toString()
    override fun toString(format: WithContextFormat) =
        "${base.toString(format)}.${method.name}(${args.joinToString { it.toString(format) }})"
}

data class JSpecialInvoke(val base: JExpression, val method: SootMethod, val args: List<JExpression>) :
    JExpression(method.returnType) {
    override fun toString() = super.toString()
    override fun toString(format: WithContextFormat) =
        "${base.toString(format)}.${method.name}(${args.joinToString { it.toString(format) }})"
}

data class JInterfaceInvoke(val base: JExpression, val method: SootMethod, val args: List<JExpression>) :
    JExpression(method.returnType) {
    override fun toString() = super.toString()
    override fun toString(format: WithContextFormat) =
        "${base.toString(format)}.${method.name}(${args.joinToString { it.toString(format) }})"
}

data class JStaticInvoke(val method: SootMethod, val args: List<JExpression>) : JExpression(method.returnType) {
    override fun toString() = super.toString()
    override fun toString(format: WithContextFormat) =
        "${method.declaringClass.type.prettyPrint()}.${method.name}(${args.joinToString { it.toString(format) }})"
}

data class JDynamicInvoke(val method: SootMethod, val args: List<JExpression>) : JExpression(method.returnType) {
    override fun toString() = super.toString()
    override fun toString(format: WithContextFormat) =
        "${method.declaringClass.type.prettyPrint()}.${method.name}(${args.joinToString { it.toString(format) }})"
}

data class JNew(val args: List<JExpression>, val baseType: Type) : JExpression(baseType) {
    override fun toString() = super.toString()
    override fun toString(format: WithContextFormat) =
        "new ${baseType.prettyPrint()}(${args.joinToString { it.toString(format) }})"
}

// REF
data class JInstanceFieldRef(val base: JExpression, val field: SootField) : JExpression(field.type) {
    override fun toString() = super.toString()
    override fun toString(format: WithContextFormat) = "${base.toString(format)}.${field.name}"
}

data class JStaticFieldRef(val field: SootField) : JExpression(field.type) {
    override fun toString() = super.toString()
    override fun toString(format: WithContextFormat) = "${field.declaringClass.type.prettyPrint()}.${field.name}"
}

data class JThisRef(val thisType: Type) : JExpression(thisType) {
    override fun toString() = super.toString()
    override fun toString(format: WithContextFormat) = "this"
}

data class JParameterRef(val index: Int, val paramType: Type) : JExpression(paramType) {
    override fun toString() = super.toString()
    override fun toString(format: WithContextFormat) =
        "\$param$index" // TODO: Parameter names seem not to be preserved in Soot
}

// UNOPEXPR
data class JNot(val op: JExpression) : JExpression(BooleanType.v()) {
    init {
        validateBool(op.type)
    }

    override fun toString() = super.toString()
    override fun toString(format: WithContextFormat) = "!(${op.toString(format)})"
}

// BINOPEXPR
data class JCompareGreater(val left: JExpression, val right: JExpression) : JExpression(left.type) {
    override fun toString() = super.toString()
    override fun toString(format: WithContextFormat) = "${left.toString(format)} cmpg ${right.toString(format)}"
}

data class JCompareLess(val left: JExpression, val right: JExpression) : JExpression(left.type) {
    override fun toString() = super.toString()
    override fun toString(format: WithContextFormat) = "${left.toString(format)} cmpl ${right.toString(format)}"
}

data class JAdd(val left: JExpression, val right: JExpression) : JExpression(left.type) {
    override fun toString() = super.toString()
    override fun toString(format: WithContextFormat) = "${left.toString(format)} + ${right.toString(format)}"
}

data class JSubtract(val left: JExpression, val right: JExpression) : JExpression(left.type) {
    override fun toString() = super.toString()
    override fun toString(format: WithContextFormat) = "${left.toString(format)} - ${right.toString(format)}"
}

data class JMultiply(val left: JExpression, val right: JExpression) : JExpression(left.type) {
    override fun toString() = super.toString()
    override fun toString(format: WithContextFormat) = "${left.toString(format)} * ${right.toString(format)}"
}

data class JDivide(val left: JExpression, val right: JExpression) : JExpression(left.type) {
    override fun toString() = super.toString()
    override fun toString(format: WithContextFormat) = "${left.toString(format)} / ${right.toString(format)}"
}

data class JRemainder(val left: JExpression, val right: JExpression) : JExpression(left.type) {
    override fun toString() = super.toString()
    override fun toString(format: WithContextFormat) = "${left.toString(format)} % ${right.toString(format)}"
}

data class JAnd(val left: JExpression, val right: JExpression) : JExpression(BooleanType.v()) {
    init {
        validateBool(left.type)
        validateBool(right.type)
    }

    override fun toString() = super.toString()
    override fun toString(format: WithContextFormat): String {
        val l = if (left is JOr) "(${left.toString(format)})" else left.toString(format)
        val r = if (right is JOr) "(${right.toString(format)})" else right.toString(format)
        return "$l && $r"
    }
}

data class JOr(val left: JExpression, val right: JExpression) : JExpression(BooleanType.v()) {
    init {
        validateBool(left.type)
        validateBool(right.type)
    }

    override fun toString() = super.toString()
    override fun toString(format: WithContextFormat): String {
        val l = if (left is JAnd) "(${left.toString(format)})" else left.toString(format)
        val r = if (right is JAnd) "(${right.toString(format)})" else right.toString(format)
        return "$l || $r"
    }
}

/**
 * Represents ==, !=, >, >=, < and <= expressions
 *
 * Called "LeafCondition" because instances of this type appear as leaves in our custom expression tree
 * (there's only "Jimple stuff" below them, as opposed to [JAnd] and [JOr] which have [JExpression] as children)
 */
data class JCondition(val left: JExpression, val right: JExpression, val symbol: LeafConditionSymbol) :
    JExpression(BooleanType.v()) {
    override fun toString() = super.toString()
    override fun toString(format: WithContextFormat) = "${left.toString(format)} $symbol ${right.toString(format)}"
}

sealed class LeafConditionSymbol(val symbol: String, negate: () -> LeafConditionSymbol) {
    val negated by lazy(negate)
    override fun toString() = symbol
}

object JEquals : LeafConditionSymbol("==", { JNotEquals })
object JNotEquals : LeafConditionSymbol("!=", { JEquals })
object JGreaterThan : LeafConditionSymbol(">", { JLessOrEqual })
object JGreaterOrEqual : LeafConditionSymbol(">=", { JLessThan })
object JLessThan : LeafConditionSymbol("<", { JGreaterOrEqual })
object JLessOrEqual : LeafConditionSymbol("<=", { JGreaterThan })

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

/**
 * Turns a Jimple 'Value' into an instance of our custom expression tree model.
 */
fun parseJimpleExpression(expr: ValueWithContext, typeHint: TypeHint): JExpression {
    val v = expr.value
    return when (v) {
        is IntConstant -> when (typeHint) {
            NoTypeHint -> JConstant(WithContext(v, expr.unit, expr.method))
            ForceBool -> when (v.value) {
                0 -> JFalse
                1 -> JTrue
                else -> throw IllegalArgumentException("Cannot interpret '${v.value}' as boolean")
            }
        }

        is NullConstant -> JNull

        is Constant -> JConstant(WithContext(v, expr.unit, expr.method))

        is CastExpr -> JCast(parseJimpleExpression(expr.copy(value = v.op), NoTypeHint), v.castType)
        is InstanceOfExpr -> JInstanceOf(parseJimpleExpression(expr.copy(value = v.op), NoTypeHint), v.checkType)
        is Local -> JLocal(WithContext(v, expr.unit, expr.method))

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
                is ConditionExpr -> {
                    val symbol = when (v) {
                        is EqExpr -> JEquals
                        is NeExpr -> JNotEquals
                        is GtExpr -> JGreaterThan
                        is GeExpr -> JGreaterOrEqual
                        is LtExpr -> JLessThan
                        is LeExpr -> JLessOrEqual
                        else -> TODO("Can't happen")
                    }
                    JCondition(op1, op2, symbol)
                }
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
}