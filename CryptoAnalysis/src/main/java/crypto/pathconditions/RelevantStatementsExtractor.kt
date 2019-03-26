package crypto.pathconditions.boomerang

import crypto.pathconditions.*
import crypto.pathconditions.debug.prettyPrint
import crypto.pathconditions.graphviz.*
import boomerang.*
import boomerang.callgraph.ObservableICFG
import boomerang.callgraph.ObservableStaticICFG
import boomerang.jimple.*
import boomerang.results.BackwardBoomerangResults
import soot.Value
import soot.jimple.*
import soot.jimple.internal.JimpleLocal
import soot.jimple.toolkits.ide.icfg.JimpleBasedInterproceduralCFG
import sync.pds.solver.nodes.*
import sync.pds.solver.nodes.Node
import wpds.impl.*
import java.util.*

//
// Provides functionality to extract the statements along the data flow path of a certain object
// (between its allocation site and another statement) from the call automaton of a forward query Boomerang solver.
//

// Boomerang configuration for this analysis
val boomerangConfig = object : DefaultBoomerangOptions() {
    override fun onTheFlyCallGraph() = false // Must be turned off if no SeedFactory is specified.
    override fun trackStrings() = true
    override fun isAllocationVal(v: Value?): Boolean = when {
        v is StaticInvokeExpr && v.toString().contains("getProperty(java.lang.String)") -> true
        // Causes StackOverflowException:
        // v is SpecialInvokeExpr && v.toString().contains("Hashtable: java.lang.Object get(") -> true

        v is JimpleLocal -> false
        v is CmpgExpr -> true
        v is CmplExpr -> true
        v is InstanceOfExpr -> true

        // v is Constant -> true

        else -> super.isAllocationVal(v)
    }
}

fun valueUsedInStatement(u: Stmt, value: Val, isBackward: Boolean): Boolean {
    if (value.isStatic)
        return true
    if (isBackward && u is AssignStmt && u.leftOp == value.value())
        return true
    if (u.containsInvokeExpr()) {
        val invokeExpr = u.invokeExpr
        return (invokeExpr is InstanceInvokeExpr && invokeExpr.base == value.value()) ||
            invokeExpr.args.contains(value.value())
    }
    return u.useBoxes.any { it.value == value.value() }
}

sealed class WalkTask {
    data class WalkForward(val node: INode<Val>, val variableOfInterest: Val) : WalkTask() {
        override fun toString() = "FORWARD: " + node.fact().prettyPrint()
    }

    data class WalkBackward(val transition: Transition<Statement, INode<Val>>, val variableOfInterest: Val) :
        WalkTask() {
        override fun toString() =
            "BACKWARD: " + transition.label.prettyPrint() + "\n" + transition.start.fact().prettyPrint() + " ==> " + transition.target.fact().prettyPrint() + "\n<<${variableOfInterest.prettyPrint()}>>"
    }
}

data class WalkForwardResult(val newTasks: List<WalkTask>)
data class WalkBackwardResult(val isRelevant: Boolean, val nextVariableOfInterest: Val)

private fun <W : Weight> walkAutomaton(
    automaton: WeightedPAutomaton<Statement, INode<Val>, W>,
    variableOfInterest: Val
): ArrayList<Statement> {
    val worklist = LinkedList<WalkTask>() as Queue<WalkTask>
    val done = HashSet<WalkTask>()
    val relevantStatements = ArrayList<Statement>()
    var graph = DirectedGraph.emptyUnlabeled<WalkTask>()

    // Step 1: Find the variable node for the variable we are interested in
    val initialState = automaton.states.first { it is SingleNode<Val> && it.fact() == variableOfInterest }
    val initialTask = WalkTask.WalkForward(initialState, variableOfInterest)
    worklist.add(initialTask)

    fun forwardPass(task: WalkTask.WalkForward): WalkForwardResult {
        val outgoing = automaton.transitions
            .filter { it.start == task.node }
            .distinctBy { it.target }
            .map { WalkTask.WalkForward(it.target, it.target.fact()) }
            .minus(done)
            .minus(worklist)

        val incoming = automaton.transitions
            .filter { it.target == task.node }
            .filter { it.start.fact().value() == it.target.fact().value() } // not sure why, but this helps greatly!
            .map { WalkTask.WalkBackward(it, task.variableOfInterest) }
            .minus(done)
            .minus(worklist)

        (outgoing + incoming).forEach { graph = graph.addEdge(task to it) }
        return WalkForwardResult((outgoing + incoming).toList())
    }

    fun backwardPass(task: WalkTask.WalkBackward): WalkBackwardResult {
        if (!task.transition.label.unit.isPresent ||
            !valueUsedInStatement(task.transition.label.unit.get(), task.variableOfInterest, isBackward = true)
        ) {
            return WalkBackwardResult(false, task.variableOfInterest)
        }

        val stmt = task.transition.label.unit.get()

        return when (stmt) {
            // Special case: Assignments!
            // If right op does not occur as a state in the (forward) automaton, the assignment is irrelevant
            is AssignStmt ->
                WalkBackwardResult(true, Val(stmt.leftOp, task.transition.label.method))
            is InvokeStmt -> WalkBackwardResult(true, task.variableOfInterest)
            is ReturnStmt -> WalkBackwardResult(true, task.variableOfInterest)
            else -> WalkBackwardResult(false, task.variableOfInterest)
        }
    }

    // Step 2: Walk through the automaton, extracting the relevant statements
    while (worklist.any()) {
        val task = worklist.remove()
        done += task
        when (task) {
            is WalkTask.WalkForward -> {
                val result = forwardPass(task)
                result.newTasks.forEach { worklist.add(it) }
                // We also need the statements stored in unbalanced nodes
                if (task.node.fact().isUnbalanced) {
                    val unbalancedStmt = Val.zero().javaClass.getDeclaredField("unbalancedStmt").let {
                        it.isAccessible = true
                        it.get(task.node.fact()) as Statement
                    }
                    relevantStatements.add(unbalancedStmt)
                }
            }
            is WalkTask.WalkBackward -> {
                val result = backwardPass(task)
                if (result.isRelevant) {
                    val newTask = WalkTask.WalkForward(task.transition.start, result.nextVariableOfInterest)
                    if (newTask !in done && newTask !in worklist) {
                        worklist.add(newTask)
                        graph = graph.addEdge(task to newTask)
                    }
                    relevantStatements.add(task.transition.label)
                    graph = graph.configureNode(task) { fillColor("whitesmoke") }
                } else {
                    graph = graph.removeNode(task)
                }
            }
        }
    }

    val graphDiagram = graph.eliminateMultiEdges().toDotString()

    return relevantStatements
}


/** Analysis Step 1: Perform Boomerang query */
private fun boomerangQuery(query: PathConditionsQuery): BackwardBoomerangResults<Weight.NoWeight> {
    // 1. Create a Boomerang solver.
    val icfg = ObservableStaticICFG(JimpleBasedInterproceduralCFG(true))

    val solver = object : Boomerang(boomerangConfig) {
        override fun icfg() = icfg
        override fun getSeedFactory() = null
    }

    // 2. Submit a query to the solver.
    val boomerangQuery = BackwardQuery(Statement(query.statement, query.method), Val(query.variable, query.method))
    val backwardQueryResults = solver.solve(boomerangQuery)
    solver.debugOutput()
    return backwardQueryResults
}

/** Analysis Step 2: Extract relevant statements from Boomerang results */
fun extractRelevantStatements(
    backwardQueryResults: BackwardBoomerangResults<Weight.NoWeight>,
    query: PathConditionsQuery
): ArrayList<Statement> {
    val callAutomaton = backwardQueryResults.queryToSolvers().asIterable()
        .firstOrNull { it.key is ForwardQuery && query.checkAllocationSite(it.key.stmt()) }
        ?.value?.callAutomaton

    if (callAutomaton == null)
        throw Exception("Could not find an allocation site of interest for variable '${query.variable}'")

    return walkAutomaton(callAutomaton, Val(query.variable, query.method))
}

fun extractRelevantStatements(query: PathConditionsQuery): ArrayList<Statement> {
    val boomerangResults = boomerangQuery(query)
    val relevantStatements = extractRelevantStatements(boomerangResults, query)
    return relevantStatements
}
