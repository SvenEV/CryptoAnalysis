package crypto.pathconditions

import boomerang.jimple.Statement
import com.google.common.collect.ImmutableList
import com.microsoft.z3.BoolExpr
import crypto.pathconditions.expressions.*
import crypto.pathconditions.graphviz.DirectedGraph
import crypto.pathconditions.graphviz.DirectedUnlabeledGraph
import crypto.pathconditions.graphviz.addEdge
import crypto.pathconditions.graphviz.buildGraph
import crypto.pathconditions.refinement.refine
import crypto.pathconditions.z3.createSolver
import crypto.pathconditions.z3.decode
import crypto.pathconditions.z3.encode
import crypto.pathconditions.z3.simplify
import soot.SootMethod
import soot.Unit
import soot.jimple.IfStmt
import soot.jimple.Stmt
import soot.jimple.spark.ondemand.genericutil.ImmutableStack
import soot.toolkits.graph.ExceptionalUnitGraph
import soot.toolkits.graph.UnitGraph
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

fun <T> ImmutableStack<T>.replaceTop(entry: T) = pop().push(entry)!!

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

data class BranchingStackFrame(
    val blockUsage: BlockUsage,
    val surroundingIf: IfStmt?
)

data class Fact(
    val condition: JExpression,
    val branchStatements: Set<Statement>, // the if-statements the condition was constructed from
    val branchingStack: ImmutableStack<BranchingStackFrame>) // stack head represents the closest (i.e. innermost) if-statement relative to the current statement

typealias FactBox = MBox<ImmutableList<Fact>>

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

fun mergeFacts(factsToMerge: List<Fact>): Fact {
    fun doMerge(left: Fact, right: Fact): Fact {
        // 'left' and 'right' must belong to the same if
        assert(left.branchingStack.size() == right.branchingStack.size())
        assert(left.branchingStack.peek().surroundingIf == right.branchingStack.peek().surroundingIf)

        val leftUsage = left.branchingStack.peek().blockUsage
        val rightUsage = right.branchingStack.peek().blockUsage

        fun leftOrRight() = Fact(
            or(left.condition, right.condition),
            left.branchStatements + right.branchStatements,
            left.branchingStack) // same as right.branchingStack here

        return when (leftUsage to rightUsage) {
            BlockUsage.None to BlockUsage.None -> leftOrRight()
            BlockUsage.None to BlockUsage.Foreign -> left
            BlockUsage.None to BlockUsage.Owned -> right
            BlockUsage.Foreign to BlockUsage.None -> right
            BlockUsage.Foreign to BlockUsage.Foreign -> leftOrRight()
            BlockUsage.Foreign to BlockUsage.Owned -> right
            BlockUsage.Owned to BlockUsage.None -> left
            BlockUsage.Owned to BlockUsage.Foreign -> left
            BlockUsage.Owned to BlockUsage.Owned -> leftOrRight()
            else -> throw Exception() // 'else' required (Kotlin can't prove exhaustion here)
        }
    }

    fun popMax(fact: Fact): Fact {
        val reducedStack = fact.branchingStack.pop()
        val inner = fact.branchingStack.peek().blockUsage
        val outer = reducedStack.peek().blockUsage
        return fact.copy(branchingStack = reducedStack.replaceTop(
            reducedStack.peek().copy(blockUsage = BlockUsage.max(inner, outer))))
    }

    // Merging needs to go bottom-up: Facts of innermost ifs are merged first, resulting in a "higher-level" fact
    // which can then be merged with another one, etc.
    //
    // We group facts by their surrounding if-statement (or switch-, in theory) to obtain the correct merging order:
    // * A group of size >1 represents branches belonging to the same if/switch -- except for the top element, facts in
    //   the group have the same stack and can be merged into a single fact, reducing stack size by 1.
    // * A group of size 1 represents one of multiple branches belonging to the same if/switch. However, the other
    //   branches are still "missing" as they apparently have sub-branches which need to be merged first.
    var facts = factsToMerge
    while (facts.size > 1) {
        facts = facts
            .groupBy { fact -> fact.branchingStack.peek().surroundingIf }
            .flatMap { (_, factGroup) ->
                when (factGroup.size) {
                    1 -> factGroup // do nothing just yet, we'll get a second fact for this group after some more merging
                    else -> {
                        // (since we don't support 'switch' currently, the group size is at most 2)
                        val merged = factGroup.drop(1).fold(factGroup[0], ::doMerge)
                        listOf(popMax(merged))
                    }
                }
            }
    }

    return facts.single()
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
    fun resultsToDirectedGraph() =
        graph.heads.fold(DirectedGraph.emptyUnlabeled<Unit>()) { dotGraph, stmt ->
            buildGraph(stmt, dotGraph, { graph.getSuccsOf(it) },
                onNode = { u, graph ->
                    graph.configureNode(u) {
                        if (u in ownRelevantStatements.map { it.unit.get() })
                            fillColor("#ffffcc")
                        else if (u in foreignRelevantStatements.map { it.unit.get() })
                            fillColor("#ffcccc")
                    }
                },
                onEdge = { u, succ, graph ->
                    graph.configureEdge(u to succ) {
                        // val fact = getFlowBefore(succ)
                        val fact =
                            when (u) {
                                is IfStmt ->
                                    if (succ == u.target)
                                        getBranchFlowAfter(u).single()
                                    else
                                        getFallFlowAfter(u)
                                else ->
                                    getFallFlowAfter(u)
                            }.content.single()

                        val condition = simplifyTerm(refine(fact.condition)).toString(ContextFormat.ContextFree)
                        val stack = fact.branchingStack.asSequence().map { it.blockUsage }.toList()
                        label("$condition\n$stack")
                    }
                })
        }

    override fun newInitialFlow() = FactBox(ImmutableList.of(
        Fact(
            JTrue,
            emptySet(),
            ImmutableStack.emptyStack<BranchingStackFrame>().push(BranchingStackFrame(BlockUsage.None, null)))))

    override fun merge(left: FactBox, right: FactBox, merged: FactBox) {
        merged.content = ImmutableList.copyOf(left.content + right.content)
    }

    override fun copy(source: FactBox?, target: FactBox?) {
        target!!.content = source!!.content
    }

    override fun flowThrough(
        input: FactBox,
        stmt: Unit?,
        fallOuts: List<FactBox>?,
        branchOuts: List<FactBox>?
    ) {
        val fact = mergeFacts(input.content)

        return when (stmt) {
            is IfStmt -> {
                val condition = parseJimpleExpression(stmt.condition, ProgramContext(stmt, method), ForceBool)
                val trueCondition = and(fact.condition, condition)
                val falseCondition = and(fact.condition, not(condition))

                val newStack = fact.branchingStack.push(BranchingStackFrame(BlockUsage.None, stmt))
                val newBranchStatements = fact.branchStatements + Statement(stmt as Stmt, method)
                val trueFact = Fact(trueCondition, newBranchStatements, newStack)
                val falseFact = Fact(falseCondition, newBranchStatements, newStack)

                branchOuts!![0].content = ImmutableList.of(trueFact)
                fallOuts!![0].content = ImmutableList.of(falseFact)
                Unit
            }
            else -> {
                val stmtUsage = when {
                    ownRelevantStatements.any { it.unit.get() == stmt } -> BlockUsage.Owned
                    foreignRelevantStatements.any { it.unit.get() == stmt } -> BlockUsage.Foreign
                    else -> BlockUsage.None
                }

                val currentFrame = fact.branchingStack.peek()
                val usageToPropagate = BlockUsage.max(currentFrame.blockUsage, stmtUsage)
                val newStack = fact.branchingStack.replaceTop(currentFrame.copy(blockUsage = usageToPropagate))
                val newFacts = ImmutableList.of(fact.copy(branchingStack = newStack))

                if (stmt!!.branches()) {
                    if (branchOuts!!.any())
                        branchOuts[0].content = newFacts
                    Unit
                } else {
                    if (fallOuts!!.any())
                        fallOuts[0].content = newFacts
                    Unit
                }
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

data class PathConditionResult(
    val method: SootMethod,
    val condition: JExpression,
    val branchStatements: Set<Statement>,
    val asDirectedGraph: () -> DirectedUnlabeledGraph<Unit>)

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
            val flowAtSink = mergeFacts(result.getFlowBefore(sinkStatement).content)
            val branchStatements = flowAtSink.branchStatements ?: emptySet()
            val methodCondition = flowAtSink.condition ?: JTrue
            PathConditionResult(method, methodCondition, branchStatements) { result.resultsToDirectedGraph() }
        }
        .filter { it.condition != JTrue } // ignore relevant statements that are reached unconditionally
        .asSequence()