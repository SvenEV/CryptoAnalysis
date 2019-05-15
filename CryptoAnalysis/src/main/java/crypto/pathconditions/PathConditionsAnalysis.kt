package crypto.pathconditions

import boomerang.jimple.Statement
import com.google.common.collect.ImmutableList
import com.microsoft.z3.BoolExpr
import crypto.pathconditions.debug.prettyPrint
import crypto.pathconditions.expressions.*
import crypto.pathconditions.graphviz.DirectedGraph
import crypto.pathconditions.graphviz.DirectedUnlabeledGraph
import crypto.pathconditions.graphviz.addEdge
import crypto.pathconditions.graphviz.buildGraph
import crypto.pathconditions.refinement.refined
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
    val foundSource: Boolean,
    val expectingLoopCondition: Boolean, // true, iff the beginning of a loop was discovered, but we are still awaiting the breaking if-statement
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

fun mergeFacts(factsToMerge: List<Fact>, stmt: Unit, isLoop: Boolean): Fact {
    fun throwUnmergable(facts: List<Fact>): Nothing =
        throw IllegalStateException("Unmergable facts at '${stmt.prettyPrint()}':\n${facts.joinToString("\n")}")

    fun doMerge(left: Fact, right: Fact): Fact {
        // 'left' and 'right' must belong to the same if
        assert(left.branchingStack.size() == right.branchingStack.size())
        assert(left.branchingStack.peek().surroundingIf == right.branchingStack.peek().surroundingIf)

        val leftUsage = left.branchingStack.peek().blockUsage
        val rightUsage = right.branchingStack.peek().blockUsage
        val surroundingIf = left.branchingStack.peek().surroundingIf // same as right.branchingStack.peek().surroundingIf

        fun leftOrRight() = Fact(
            left.foundSource || right.foundSource,
            false,
            or(left.condition, right.condition).refined().simplified(),
            left.branchStatements + right.branchStatements,
            left.branchingStack.replaceTop(BranchingStackFrame(
                BlockUsage.max(leftUsage, rightUsage),
                surroundingIf)))

        if (!left.foundSource && !right.foundSource) {
            // We haven't reached the source of the data flow of interest yet,
            // so no need to discard any branches
            return leftOrRight()
        } else {
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
    }

    fun popMax(stack: ImmutableStack<BranchingStackFrame>): ImmutableStack<BranchingStackFrame> {
        val reducedStack = stack.pop()
        val inner = stack.peek().blockUsage
        val outer = reducedStack.peek().blockUsage
        return reducedStack.replaceTop(
            reducedStack.peek().copy(blockUsage = BlockUsage.max(inner, outer)))
    }

    return if (isLoop) {
        // At loop entry, the entry fact and the looping fact are merged as follows:
        //
        // if !factLoop.foundSource, propagate factEntry
        // if factLoop FOREIGN, propagate factEntry
        // if factLoop NONE, propagate factEntry
        // if factLoop OWNED,
        // 	- propagate
        // 		i: true
        // 		c: factEntry.c && factLoop.c
        // 		U: factEntry.U???                  <----------- That's the question
        // 		S: factLoop.S        <-- superset of factEntry.S
        //
        when (factsToMerge.size) {
            1 -> factsToMerge.single()
            2 -> {
                val factEntry = factsToMerge.sortedBy { it.branchingStack.size() }.first()
                val factLoop = factsToMerge.sortedBy { it.branchingStack.size() }.last()

                if (factLoop.branchingStack.size() != factEntry.branchingStack.size() + 1)
                    throwUnmergable(factsToMerge)

                val coverageLoop = factLoop.branchingStack.peek().blockUsage

                // Idea: We can discard a loop body unless it contains a relevant statement.
                when {
                    // If source not yet found, loop-body irrelevant, we just need to get out of the loop at some point
                    !factLoop.foundSource -> factEntry

                    // FOREIGN means: We must not execute the loop-body.
                    // Thus, we only consider the path where the loop is skipped.
                    coverageLoop == BlockUsage.Foreign -> factEntry // must not execute loop-body since it is foreign

                    // NONE means: We can, but don't need to execute the loop-body, but we *must* get out of the loop
                    // at some point (unless the sink statement is in the loop-body). Since we can't express "loop
                    // condition can first be true but must later change to false" we conservatively discard the
                    // loop-body and only consider the path where the loop is never executed.
                    coverageLoop == BlockUsage.None -> factEntry

                    // OWNED means: (We assume that) we must execute the loop-body at least once, but we *also* need to
                    // get out of the loop at some point (unless sink is in the loop-body). Naturally, this can only
                    // lead to a "false" condition.
                    else -> {
                        Fact(
                            foundSource = true,
                            expectingLoopCondition = false,
                            condition = factLoop.condition.refined().simplified(), // == and(factLoop.condition, factEntry.condition).refined().simplified(),
                            branchStatements = factLoop.branchStatements,
                            branchingStack = popMax(factLoop.branchingStack) // superset of factEntry.branchingStack
                        )
                    }
                }
            }
            else -> throwUnmergable(factsToMerge)
        }
    } else {
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
            val oldSize = facts.size
            facts = facts
                .groupBy { fact -> fact.branchingStack.peek().surroundingIf }
                .flatMap { (_, factGroup) ->
                    when (factGroup.size) {
                        1 -> factGroup // do nothing just yet, we'll get a second fact for this group after some more merging
                        else -> {
                            // (since we don't support 'switch' currently, the group size is at most 2)
                            val merged = factGroup.drop(1).fold(factGroup[0], ::doMerge)
                            listOf(merged.copy(branchingStack = popMax(merged.branchingStack)))
                        }
                    }
                }

            if (facts.size == oldSize)
                throwUnmergable(facts)
        }

        facts.single()
    }
}

private class PathConditionsAnalysis(
    graph: UnitGraph,
    private val method: SootMethod,
    private val ownRelevantStatements: Set<Statement>,
    private val foreignRelevantStatements: Set<Statement>) :
    ForwardBranchedFlowAnalysis<FactBox>(graph) {

    private val visitedStmts = HashSet<Unit>()

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
                        val fact =
                            when (u) {
                                is IfStmt ->
                                    if (succ == u.target)
                                        getBranchFlowAfter(u).single()
                                    else
                                        getFallFlowAfter(u)
                                else ->
                                    getFallFlowAfter(u)
                            }.content.singleOrNull()

                        if (fact != null) {
                            if (!fact.foundSource)
                                fontColor("#a0a0a0")

                            val condition = fact.condition.toString(ContextFormat.ContextFree)
                            val stack = fact.branchingStack.asSequence().map { it.blockUsage }.toList()
                            label("$condition\n$stack")
                        }
                    }
                })
        }

    // Uses a simple heuristic to determine whether a statement marks the beginning of a loop:
    // If it has a control-flow predecessor that comes *after* itself in the unit chain, return true.
    fun isLoopEntry(stmt: Unit) =
        graph.getPredsOf(stmt).any { pred -> method.activeBody.units.indexOf(pred) > method.activeBody.units.indexOf(stmt) }

    override fun newInitialFlow() = FactBox(ImmutableList.of())

    override fun entryInitialFlow() = FactBox(ImmutableList.of(
        Fact(
            false,
            false,
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
        stmt: Unit,
        fallOuts: List<FactBox>,
        branchOuts: List<FactBox>
    ) {
        if (!visitedStmts.add(stmt)) {
            // Statement already visited; ignore!
            // return
        }

        val isLoopEntry = isLoopEntry(stmt)
        val fact = mergeFacts(input.content, stmt, isLoopEntry)

        when (stmt) {
            is IfStmt -> {
                val condition = parseJimpleExpression(stmt.condition, ProgramContext(stmt, method), ForceBool)
                val trueCondition = and(fact.condition, condition).refined().simplified()
                val falseCondition = and(fact.condition, not(condition)).refined().simplified()
                val newStack = fact.branchingStack.push(BranchingStackFrame(BlockUsage.None, stmt))
                val newBranchStatements = fact.branchStatements + Statement(stmt as Stmt, method)

                val isLoopCondition = isLoopEntry || fact.expectingLoopCondition

                val (trueFact, falseFact) = if (isLoopCondition) {
                    // In loops, only the false-branch increases nesting (the true-branch skips the loop body)
                    Fact(fact.foundSource, false, trueCondition, newBranchStatements, fact.branchingStack) to
                        Fact(fact.foundSource, false, falseCondition, newBranchStatements, newStack)
                } else {
                    Fact(fact.foundSource, false, trueCondition, newBranchStatements, newStack) to
                        Fact(fact.foundSource, false, falseCondition, newBranchStatements, newStack)
                }

                branchOuts[0].content = ImmutableList.of(trueFact)
                fallOuts[0].content = ImmutableList.of(falseFact)
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
                val newFacts = ImmutableList.of(Fact(
                    fact.foundSource || stmtUsage == BlockUsage.Owned,
                    isLoopEntry,
                    fact.condition,
                    fact.branchStatements,
                    newStack))

                if (stmt.branches()) {
                    if (branchOuts.any())
                        branchOuts[0].content = newFacts
                } else {
                    if (fallOuts.any())
                        fallOuts[0].content = newFacts
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

fun JExpression.simplified() = simplifyTerm(this)

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
            val flowAtSink = mergeFacts(result.getFlowBefore(sinkStatement).content, sinkStatement, false)
            PathConditionResult(method, flowAtSink.condition, flowAtSink.branchStatements) { result.resultsToDirectedGraph() }
        }
        .asSequence()