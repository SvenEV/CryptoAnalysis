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
    val usage: BlockUsage,
    val stack: ImmutableStack<BlockUsage>)

typealias FactBox = MBox<Fact>

enum class BlockUsage {
    None, // kein Eigen- und kein Fremd-Statement im Block
    Foreign, // kein Eigen-, aber mind. 1 Fremd-Statement im Block
    Owned // mind. 1 Eigen-Statement im Block
}

private class PathConditionsAnalysis(
    graph: UnitGraph,
    private val method: SootMethod,
    private val ownRelevantStatements: Set<Statement>,
    private val foreignRelevantStatements: Set<Statement>) :
    ForwardBranchedFlowAnalysis<FactBox>(graph) {

    init {
        val prettyPrint = method.prettyPrint()
        doAnalysis()
    }

    override fun newInitialFlow() = FactBox(Fact(JTrue, emptySet(), BlockUsage.None, ImmutableStack.emptyStack()))

    override fun merge(left: FactBox, right: FactBox, merged: FactBox) {
        val (condition, branchStatements) = when {
            left.content.usage == BlockUsage.Foreign ->
                right.content.condition to right.content.branchStatements // take only right condition (right can't be Foreign at this point)
            right.content.usage == BlockUsage.Foreign ->
                left.content.condition to left.content.branchStatements // take only left condition (left can't be Foreign at this point)
            else ->
                or(left.content.condition, right.content.condition) to (left.content.branchStatements + right.content.branchStatements)
        }

        // Assumption: left and right have the same stack, so just use left
        val parentUsage = left.content.stack.peek()
        val remainingStack = left.content.stack.pop()
        merged.content = Fact(condition, branchStatements, parentUsage, remainingStack)
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

            val newStack = input.content.stack.push(input.content.usage)
            val newBranchStatements = input.content.branchStatements + Statement(stmt as Stmt, method)
            val trueFact = Fact(trueCondition, newBranchStatements, BlockUsage.None, newStack)
            val falseFact = Fact(falseCondition, newBranchStatements, BlockUsage.None, newStack)

            branchOuts!![0].content = trueFact
            fallOuts!![0].content = falseFact
            Unit
        }
        else -> {
            val currentUsage = input.content.usage
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

            if (stmt!!.branches()) {
                if (branchOuts!!.any())
                    branchOuts[0].content = input.content.copy(usage = usageToPropagate)
                Unit
            }
            else {
                if (fallOuts!!.any())
                    fallOuts[0].content = input.content.copy(usage = usageToPropagate)
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

fun computePathConditions(relevantStatements: Set<Statement>, foreignRelevantStatements: Set<Statement>) = relevantStatements
    .asSequence()
    .distinct()
    .groupBy { it.method }
    .map { (method, relevantStmts) ->
        val cfg = ExceptionalUnitGraph(method.activeBody)
        val result = PathConditionsAnalysis(cfg, method, relevantStatements, foreignRelevantStatements)

        val methodCondition = relevantStmts
            .map { result.getFlowBefore(it.unit.get()).content.condition }
            .filter { it != JTrue } // ignore relevant statements that are reached unconditionally
            .asSequence()
            .joinAnd()

        val branchStatements = relevantStmts
            .flatMap { result.getFlowBefore(it.unit.get()).content.branchStatements }
            .toSet()

        PathConditionResult(method, methodCondition, branchStatements)
    }
    .filter { it.condition != JTrue } // ignore relevant statements that are reached unconditionally
    .asSequence()