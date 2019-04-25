package crypto.pathconditions

import boomerang.jimple.Statement
import com.microsoft.z3.BoolExpr
import crypto.pathconditions.expressions.*
import crypto.pathconditions.graphviz.*
import crypto.pathconditions.graphviz.DirectedGraph
import crypto.pathconditions.refinement.refine
import crypto.pathconditions.z3.*
import soot.*
import soot.Unit
import soot.jimple.IfStmt
import soot.jimple.Stmt
import soot.jimple.spark.ondemand.genericutil.ImmutableStack
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

fun <T> ImmutableStack<T>.replaceTop(entry: T) = pop().push(entry)

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

data class Fact(
    val condition: JExpression,
    val branchStatements: Set<Statement>, // the if-statements the condition was constructed from
    val stack: ImmutableStack<BlockUsage>)

typealias FactBox = MBox<Fact>

/** The different ways a code block can be "used" by one or multiple data flows. */
enum class BlockUsage {
    None, // no own- and no foreign-statements in the code block
    Foreign, // no own-, but at least 1 foreign-statement in the code block
    Owned; // at least one own-statement in the code block

    companion object {
        /** Returns the maximum of two [BlockUsage] ([None] < [Foreign] < [Owned]) */
        fun max(x: BlockUsage, y: BlockUsage) = when (x to y) {
            None to None -> None
            None to Foreign -> Foreign
            None to Owned -> Owned
            Foreign to None -> Foreign
            Foreign to Foreign -> Foreign
            Foreign to Owned -> Owned
            Owned to None -> Owned
            Owned to Foreign -> Owned
            Owned to Owned -> Owned
            else -> throw Exception() // 'else' required (Kotlin can't prove exhaustion here)
        }

        fun max(vararg a: BlockUsage) = a.fold(None, ::max)
    }
}

private class PathConditionsAnalysis(
    graph: UnitGraph,
    private val method: SootMethod,
    private val ownRelevantStatements: Set<Statement>,
    private val foreignRelevantStatements: Set<Statement>) :
    ForwardBranchedFlowAnalysis<FactBox>(graph) {

    init {
        doAnalysis()
    }

    /** Creates a [DirectedUnlabeledGraph] suitable for visualizing the CFG and the flow facts at each statement. */
    fun resultsToDirectedGraph(): DirectedUnlabeledGraph<Unit> {
        fun traverseCfg(dotGraph: DirectedUnlabeledGraph<Unit>, u: Unit): DirectedUnlabeledGraph<Unit> {
            val fact = getFlowBefore(u)
            return graph.getSuccsOf(u)
                .fold(dotGraph) { g, succ -> traverseCfg(g, succ).addEdge(u to succ) }
                .configureNode(u) {
                    attr("xlabel", simplifyTerm(refine(fact.content.condition)).toString(ContextFormat.ContextFree) + "\n" + fact.content.stack)

                    if (u in ownRelevantStatements.map { it.unit.get() })
                        color("green")
                    else if (u in foreignRelevantStatements.map { it.unit.get() })
                        color("red")
                }
        }

        return graph.heads.fold(DirectedGraph.emptyUnlabeled(), ::traverseCfg)
    }

    override fun newInitialFlow() = FactBox(Fact(
        JTrue,
        emptySet(),
        ImmutableStack.emptyStack<BlockUsage>().push(BlockUsage.None)))

    override fun merge(left: FactBox, right: FactBox, merged: FactBox) {
        val outerUsageStack = (if (left.content.stack.size() > right.content.stack.size()) left else right).content.stack.pop()
        val outerUsage = outerUsageStack.peek()
        val leftUsage = left.content.stack.peek()
        val rightUsage = right.content.stack.peek()

        fun takeLeftCondition() = Fact(
            left.content.condition,
            left.content.branchStatements,
            outerUsageStack.replaceTop(BlockUsage.max(outerUsage, leftUsage)))

        fun takeRightCondition() = Fact(
            right.content.condition,
            right.content.branchStatements,
            outerUsageStack.replaceTop(BlockUsage.max(outerUsage, rightUsage)))

        fun takeBothConditions() = Fact(
            or(left.content.condition, right.content.condition),
            left.content.branchStatements + right.content.branchStatements,
            outerUsageStack.replaceTop(BlockUsage.max(outerUsage, leftUsage, rightUsage)))

        merged.content =
            when (leftUsage to rightUsage) {
                BlockUsage.None to BlockUsage.None -> takeBothConditions()
                BlockUsage.None to BlockUsage.Foreign -> takeLeftCondition()
                BlockUsage.None to BlockUsage.Owned -> takeRightCondition()
                BlockUsage.Foreign to BlockUsage.None -> takeRightCondition()
                BlockUsage.Foreign to BlockUsage.Foreign -> takeBothConditions() // can this even happen?
                BlockUsage.Foreign to BlockUsage.Owned -> takeRightCondition()
                BlockUsage.Owned to BlockUsage.None -> takeLeftCondition()
                BlockUsage.Owned to BlockUsage.Foreign -> takeLeftCondition()
                BlockUsage.Owned to BlockUsage.Owned -> takeBothConditions()
                else -> throw Exception() // 'else' required (Kotlin can't prove exhaustion here)
            }

        // println("MERGE '${left.content.condition.toString(ContextFormat.ContextFree)}' and '${right.content.condition.toString(ContextFormat.ContextFree)}' ==> '${merged.content.condition.toString(ContextFormat.ContextFree)}'")
    }

    override fun copy(source: FactBox?, target: FactBox?) {
        target!!.content = source!!.content
    }

    override fun flowThrough(
        input: FactBox,
        stmt: Unit?,
        fallOuts: List<FactBox>?,
        branchOuts: List<FactBox>?
    ) = when (stmt) {
        is IfStmt -> {
            val condition = parseJimpleExpression(stmt.condition, ProgramContext(stmt, method), ForceBool)
            val trueCondition = and(input.content.condition, condition)
            val falseCondition = and(input.content.condition, not(condition))

            val newStack = input.content.stack.push(BlockUsage.None)
            val newBranchStatements = input.content.branchStatements + Statement(stmt as Stmt, method)
            val trueFact = Fact(trueCondition, newBranchStatements, newStack)
            val falseFact = Fact(falseCondition, newBranchStatements, newStack)

            branchOuts!![0].content = trueFact
            fallOuts!![0].content = falseFact
            Unit
        }
        else -> {
            val currentUsage = input.content.stack.peek()!!
            val isOwnStmt = ownRelevantStatements.any { it.unit.get() == stmt }
            val isForeignStmt = foreignRelevantStatements.any { it.unit.get() == stmt }

            val usageToPropagate = when (currentUsage) {
                BlockUsage.Owned -> BlockUsage.Owned
                BlockUsage.Foreign -> when {
                    isOwnStmt -> BlockUsage.Owned
                    else -> BlockUsage.Foreign
                }
                BlockUsage.None -> when {
                    isOwnStmt -> BlockUsage.Owned
                    isForeignStmt -> BlockUsage.Foreign
                    else -> BlockUsage.None
                }
            }

            val newStack = input.content.stack.replaceTop(usageToPropagate)

            if (stmt!!.branches()) {
                if (branchOuts!!.any())
                    branchOuts[0].content = input.content.copy(stack = newStack)
                Unit
            } else {
                if (fallOuts!!.any())
                    fallOuts[0].content = input.content.copy(stack = newStack)
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

data class PathConditionResult(val method: SootMethod, val condition: JExpression, val branchStatements: Set<Statement>)

fun computePathConditions(
    sinkStatement: Unit,
    relevantStatements: Set<Statement>,
    foreignRelevantStatements: Set<Statement>) =
    relevantStatements
        .asSequence()
        .distinct()
        .groupBy { it.method }
        .map { (method, _) ->
            val cfg = ExceptionalUnitGraph(method.activeBody)
            val result = PathConditionsAnalysis(cfg, method, relevantStatements, foreignRelevantStatements)
            val flowAtSink = result.getFlowBefore(sinkStatement)
            val branchStatements = flowAtSink.content.branchStatements
            val methodCondition = flowAtSink.content.condition
            PathConditionResult(method, methodCondition, branchStatements)
        }
        .filter { it.condition != JTrue } // ignore relevant statements that are reached unconditionally
        .asSequence()