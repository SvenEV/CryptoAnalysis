package crypto.analysis

import boomerang.jimple.Statement
import boomerang.results.ForwardBoomerangResults
import soot.*
import soot.Unit
import soot.jimple.GotoStmt
import soot.jimple.IfStmt
import soot.jimple.toolkits.ide.icfg.BiDiInterproceduralCFG
import sync.pds.solver.nodes.Node
import typestate.TransitionFunction

object SvensMetricsCollector {

    fun Type.asString() = when (this) {
        is RefType -> this.sootClass.shortName
        else -> toQuotedString()
    }

    fun SootMethod.asString(): String {
        val params = parameterTypes.joinToString(", ") { it.asString() }
        return "${declaringClass.shortName}.$name($params): ${returnType.asString()}"
    }

    fun Statement.asString() =
            "${method.asString()} { ${this.unit} }"

    fun run(stmt: Statement, body: Body, results: ForwardBoomerangResults<TransitionFunction>, icfg: BiDiInterproceduralCFG<Unit, SootMethod>) {
        println("SVEN: ${stmt.asString()}")

        // Task 1: Check if seed is inside a conditional branch
        // Ingredients: ICFG to find previous statements
        val precedingIfs = iterateStatementsBackwards(stmt.unit.get(), icfg)
                .filterIsInstance<IfStmt>()
                .toList()

        val relevantIfs = precedingIfs
                .filter {
                    val endIf = findEndIf(it, body)
                    isStmtBetween(stmt.unit.get(), it, endIf, body)
                }
                .toList()

        if (relevantIfs.isNotEmpty()) {
            println("Seed is enclosed in ${relevantIfs.size} (out of ${precedingIfs.size}) if-statements")
            relevantIfs.forEach { println("    $it") }
        }

        results.asStatementValWeightTable().cellSet().forEach {
            val context = results.getContext(Node(it.rowKey, it.columnKey))
        }

    }

    fun isStmtBetween(stmt: Unit, start: Unit, end: Unit, body: Body): Boolean {
        val seq = listOf(start, stmt, end)
        return body.units.filter { it in seq } == seq
    }

    fun findEndIf(ifStmt: IfStmt, body: Body): Unit {
        // jump target is either the end-if, or it's the beginning of the else-branch which is
        // indicated by the preceding statement (end of then-branch) being a jump (to the end-if)
        val pred = body.units.getPredOf(ifStmt)
        return if (pred is GotoStmt) pred.target else ifStmt.target
    }

    fun iterateStatementsBackwards(stmt: Unit, icfg: BiDiInterproceduralCFG<Unit, SootMethod>): Sequence<Unit> = sequence {
        icfg.getPredsOf(stmt).forEach {
            yield(it)
            yieldAll(iterateStatementsBackwards(it, icfg))
        }
    }
}