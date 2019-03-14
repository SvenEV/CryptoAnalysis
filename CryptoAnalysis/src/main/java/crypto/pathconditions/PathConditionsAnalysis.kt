package crypto.pathconditions

import boomerang.jimple.Statement
import com.microsoft.z3.BoolExpr
import crypto.pathconditions.debug.prettyPrint
import crypto.pathconditions.expressions.*
import crypto.pathconditions.graphviz.*
import crypto.pathconditions.graphviz.DirectedGraph
import crypto.pathconditions.z3.*
import soot.*
import soot.Unit
import soot.jimple.IfStmt
import soot.toolkits.graph.*
import soot.toolkits.scalar.ForwardBranchedFlowAnalysis

//
// The intra-procedural path conditions analysis implemented as a standard Soot ForwardBranchedFlowAnalysis
//

/** Renders a JExpression to Graphviz DOT format with AND and OR nodes */
fun JExpression.toDotGraph(): DirectedUnlabeledGraph<Box<JExpression>> {
    fun DirectedUnlabeledGraph<Box<JExpression>>.buildTree(p: Box<JExpression>): DirectedUnlabeledGraph<Box<JExpression>> =
        when (p.content) {
            is JAnd -> {
                val left = Box(p.content.left)
                val right = Box(p.content.right)
                buildTree(left).buildTree(right)
                    .addEdge(left to p)
                    .addEdge(right to p)
                    .configureNode(p) {
                        label("&&")
                        fillColor("gold")
                    }
            }
            is JOr -> {
                val left = Box(p.content.left)
                val right = Box(p.content.right)
                buildTree(left).buildTree(right)
                    .addEdge(left to p)
                    .addEdge(right to p)
                    .configureNode(p) {
                        label("||")
                        fillColor("skyblue")
                    }
            }
            else -> configureNode(p) {
                label(p.content.toString())
                fillColor("whitesmoke")
            }
        }

    return DirectedGraph.emptyUnlabeled<Box<JExpression>>()
        .buildTree(Box(this))
}

/** A generic wrapper providing reference equality */
class Box<T>(val content: T) {
    override fun toString() = content?.toString() ?: "(empty box)"
}

/** A generic, mutable wrapper providing structural equality */
class MBox<T>(var content: T) {
    override fun toString() = content?.toString() ?: "(empty box)"
    override fun equals(other: Any?) = other is MBox<*> && other.content?.equals(content) ?: false
    override fun hashCode() = content?.hashCode() ?: 0
}

typealias PathConditionBox = MBox<JExpression>

private class PathConditionsAnalysis(graph: UnitGraph, private val method: SootMethod) :
    ForwardBranchedFlowAnalysis<PathConditionBox>(graph) {

    init {
        val prettyPrint = method.prettyPrint()
        doAnalysis()
    }

    override fun newInitialFlow() = PathConditionBox(JTrue)

    override fun merge(left: PathConditionBox?, right: PathConditionBox?, merged: PathConditionBox?) {
        merged!!.content = or(left!!.content, right!!.content)
    }

    override fun copy(source: PathConditionBox?, target: PathConditionBox?) {
        target!!.content = source!!.content
    }

    override fun flowThrough(
        input: PathConditionBox?,
        stmt: Unit?,
        fallOuts: List<PathConditionBox>?,
        branchOuts: List<PathConditionBox>?
    ) = when (stmt) {
        is IfStmt -> {
            val condition = parseJimpleExpression(ValueWithContext(stmt.condition, stmt, method), ForceBool)
            val trueCondition = and(input!!.content, condition)
            val falseCondition = and(input.content, not(condition))
            branchOuts!![0].content = trueCondition
            fallOuts!![0].content = falseCondition
            Unit
        }
        else -> {
            if (stmt!!.branches()) {
                if (branchOuts!!.any())
                    branchOuts[0].content = input!!.content
                Unit
            }
            else {
                if (fallOuts!!.any())
                    fallOuts[0].content = input!!.content
                Unit
            }
        }
    }
}

/** Analysis Step 3: Perform intra-procedural path conditions analysis */
fun simplifyTerm(term: JExpression): JExpression {
    val z3 = createSolver()
    val z3Term = z3.encode(term, z3.context.boolSort) as BoolExpr
    val z3Simplified = z3.simplify(z3Term)
    val jimpleSimplified = z3.decode(z3Simplified)
    return jimpleSimplified
}

data class PathConditionResult(val method: SootMethod, val condition: JExpression)

fun computePathConditions(relevantStatements: Iterable<Statement>) = relevantStatements
    .asSequence()
    .distinct()
    .groupBy { it.method }
    .map { (method, relevantStmts) ->
        val result = PathConditionsAnalysis(ExceptionalUnitGraph(method.activeBody), method)
        val methodCondition = relevantStmts
            .map { result.getFlowBefore(it.unit.get()).content }
            .filter { it != JTrue } // ignore relevant statements that are reached unconditionally
            .asSequence()
            .joinAnd()
        PathConditionResult(method, methodCondition)
    }
    .filter { it.condition != JTrue } // ignore relevant statements that are reached unconditionally
    .asSequence()