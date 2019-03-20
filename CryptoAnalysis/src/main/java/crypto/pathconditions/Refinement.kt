package crypto.pathconditions.refinement

import crypto.pathconditions.expressions.*
import crypto.pathconditions.ofType
import soot.*
import soot.Unit
import soot.jimple.*

//
// Provides functionality to "refine" Java expressions.
//
// Currently, this is mostly about inlining effectively final local variables. Most notably, this eliminates
// occurrences of temporary variables introduced by Jimple (e.g. `$z0`), which is important because we do not want to
// present Jimple code to users, but readable Java code. Inlining can also go beyond that, though, and produce
// expressions that summarize multiple lines of Java source code.
//
// In the future, the refinement process may be extended to recursively trigger the whole analysis again.
//

/**
 * Gets a sequence of all units from a unit's direct predecessor up to the first unit.
 * Note: Removing the return type annotation results in an internal Kotlin compiler error
 */
private fun <E : Unit> PatchingChain<E>.getPredsOf(item: E): Sequence<E> = sequence {
    val pred = getPredOf(item)
    if (pred != null) {
        yield(pred)
        yieldAll(getPredsOf(pred))
    }
}

/**
 * Tries to discover the code pattern that Jimple produces for statements like 'String x = (i == 15) ? a : b'
 * where a and b are of type Boolean. This also covers simpler conditional assignments like 'boolean x = (i == 15)'.
 * The code pattern looks like this:
 *   if (i != 15) goto label1
 *   $v = a
 *   goto label2
 * label1:
 *   $v = b
 * label2:
 *   x = $v
 */
private fun tryFindConditionalAssignmentPattern(
    local: WithContext<Local>,
    trueAssignment: AssignStmt,
    falseAssignment: AssignStmt
): JExpression? {
    val units = local.method?.activeBody?.units
    val ifStmt = units?.getPredsOf(trueAssignment)?.ofType<IfStmt>()?.firstOrNull()
    val trueAssignmentSucc = units?.getSuccOf(trueAssignment) as? GotoStmt
    val falseAssignmentPred = units?.getPredOf(falseAssignment) as? GotoStmt
    val usage = units?.getSuccOf(falseAssignment)

    if (ifStmt != null && ifStmt.target == falseAssignment &&
        trueAssignmentSucc == falseAssignmentPred &&
        usage != null && usage.useBoxes.any { it.value == local.value }
    ) {
        val condition = parseJimpleExpression(ValueWithContext(ifStmt.condition, local.unit, local.method), ForceBool)
        val typeHint = if (local.value.type == BooleanType.v()) ForceBool else NoTypeHint
        val trueExpr = parseJimpleExpression(ValueWithContext(trueAssignment.rightOp, local.unit, local.method), typeHint)
        val falseExpr = parseJimpleExpression(ValueWithContext(falseAssignment.rightOp, local.unit, local.method), typeHint)

        // Note: 'condition' is always inverted ("if (condition) goto else branch")
        return JConditional(not(condition), trueExpr, falseExpr)
    }

    return null
}

// If 'expr' is a local variable and there's no reassignment of 'expr',
// returns the value 'expr' is bound to (initialized with).
// TODO: In the future, we might want to support member variables, field accesses, ...
fun tryFindDefinition(local: WithContext<Local>): JExpression? {
    // First, check if the local is bound to one of the method's parameters
    val paramBinding = local.method!!.activeBody.units
        .ofType<IdentityStmt>()
        .firstOrNull { it.leftOp.equivTo(local.value) }

    return if (paramBinding != null) {
        parseJimpleExpression(ValueWithContext(paramBinding.rightOp, paramBinding, local.method), NoTypeHint)
    } else {
        // If not bound to a method parameter:
        // Check how many assignments there are to the local variable
        // (due to loops, we must consider all statements, even those *after* the given statement)
        // TODO: We're actually trying to prove 'effectively final' -- here's the spec: https://docs.oracle.com/javase/specs/jls/se8/html/jls-4.html#jls-4.12.4
        val assignments = local.method.activeBody.units
            .ofType<AssignStmt>()
            .filter { it.leftOp.equivTo(local.value) }
            .toList()

        when (assignments.size) {
            1 -> parseJimpleExpression(ValueWithContext(assignments[0].rightOp, assignments[0], local.method), NoTypeHint)
            2 -> tryFindConditionalAssignmentPattern(local, assignments[0], assignments[1])
            else -> null
        }
    }
}

fun refine(expr: JExpression): JExpression =
    try {
        when (expr) {
            is JNot -> not(refine(expr.op))
            is JAnd -> and(refine(expr.left), refine(expr.right))
            is JOr -> or(refine(expr.left), refine(expr.right))
            is JCast -> JCast(refine(expr.expr), expr.castType)
            is JInstanceOf -> JInstanceOf(refine(expr.expr), expr.checkType)
            is JConditional -> JConditional(refine(expr.condition), refine(expr.trueExpr), refine(expr.falseExpr))
            is JAdd -> JAdd(refine(expr.left), refine(expr.right))
            is JSubtract -> JSubtract(refine(expr.left), refine(expr.right))
            is JMultiply -> JMultiply(refine(expr.left), refine(expr.right))
            is JDivide -> JDivide(refine(expr.left), refine(expr.right))
            is JRemainder -> JRemainder(refine(expr.left), refine(expr.right))
            is JCondition -> {
                var refined = JCondition(refine(expr.left), refine(expr.right), expr.symbol)
                when {
                    refined.symbol is JEquals && refined.right is JTrue -> refined.left
                    refined.symbol is JEquals && refined.left is JTrue -> refined.right
                    refined.symbol is JEquals && refined.right is JFalse -> JNot(refined.left)
                    refined.symbol is JEquals && refined.left is JFalse -> JNot(refined.right)
                    refined.symbol is JNotEquals && refined.right is JTrue -> JNot(refined.left)
                    refined.symbol is JNotEquals && refined.left is JTrue -> JNot(refined.right)
                    refined.symbol is JNotEquals && refined.right is JFalse -> refined.left
                    refined.symbol is JNotEquals && refined.left is JFalse -> refined.right

                    refined.left is JCompareGreater && ((refined.right as? JConstant)?.v?.value as? IntConstant)?.value == 0 -> {
                        // Turn '(x cmpg y) <= 0' into 'x <= y'
                        val cmpg = refined.left as JCompareGreater
                        JCondition(refine(cmpg.left), refine(cmpg.right), refined.symbol)
                    }
                    else -> refined
                }
            }
            is JLocal -> {
                val uniqueDefinition = tryFindDefinition(expr.v)
                if (uniqueDefinition != null)
                    refine(uniqueDefinition)
                else
                    expr
            }
            is JVirtualInvoke -> JVirtualInvoke(refine(expr.base), expr.method, expr.args.map(::refine))
            is JSpecialInvoke -> JSpecialInvoke(refine(expr.base), expr.method, expr.args.map(::refine))
            is JInterfaceInvoke -> JInterfaceInvoke(refine(expr.base), expr.method, expr.args.map(::refine))
            is JStaticInvoke -> JStaticInvoke(expr.method, expr.args.map(::refine))
            is JDynamicInvoke -> JDynamicInvoke(expr.method, expr.args.map(::refine))
            is JInstanceFieldRef -> JInstanceFieldRef(refine(expr.base), expr.field)
            else -> expr // can't refine
        }
    } catch (e: Exception) {
        throw Exception("Failed to refine '$expr'", e)
    }

fun refineUnitToString(stmt: Unit, method: SootMethod) = when (stmt) {
    is AssignStmt -> "${stmt.leftOp} = ${refine(parseJimpleExpression(ValueWithContext(stmt.rightOp, stmt, method), NoTypeHint))}"
    is InvokeStmt -> refine(parseJimpleExpression(ValueWithContext(stmt.invokeExpr, stmt, method), NoTypeHint)).toString()
    is IfStmt -> "if (${refine(parseJimpleExpression(ValueWithContext(stmt.condition, stmt, method), NoTypeHint))}) ..."
    is ReturnStmt -> "return ${refine(parseJimpleExpression(ValueWithContext(stmt.op, stmt, method), NoTypeHint))}"
    is ThrowStmt -> "throw ${refine(parseJimpleExpression(ValueWithContext(stmt.op, stmt, method), NoTypeHint))}"
    else -> stmt.toString()
}