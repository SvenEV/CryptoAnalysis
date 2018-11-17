package crypto.analysis

import boomerang.jimple.Statement
import soot.*
import soot.Unit
import soot.jimple.IfStmt
import soot.jimple.toolkits.ide.icfg.BiDiInterproceduralCFG

object SvensMetricsCollector {

    fun run(stmt: Statement, body: Body, icfg: BiDiInterproceduralCFG<Unit, SootMethod>) {
        println("SVEN: ${stmt}")

        val enclosingIfs = enclosingIfs(stmt.unit.get(), body, icfg).toList()

        if (enclosingIfs.isNotEmpty()) {
            println("Seed is enclosed in ${enclosingIfs.size} if-statements")
            enclosingIfs.forEach { println("    $it") }
            // TODO: Analyze the if-conditions
        }
    }

    /**
     * Returns the sequence of items between the first occurrence of [start] and the first occurrence
     * of [end], including [start] and [end]. If [start] is not found, returns an empty sequence. If
     * [end] is not found, returns all items from [start] to the end of the sequence.
     * Uses reference equality to check for occurrences of [start] and [end].
     */
    fun <T> Sequence<T>.between(start: T, end: T): Sequence<T> =
            dropWhile { it !== start }.takeWhile { it !== end } + end

    fun isStmtBetween(stmt: Unit, start: Unit, end: Unit, body: Body): Boolean {
        val seq = listOf(start, stmt, end)
        return body.units.filter { it in seq } == seq
    }

    fun <T> Sequence<T>.comesBefore(a: T, b: T): Boolean {
        for (o in this)
            if (o === a)
                return true
            else if (o === b)
                return false
        return false
    }

    // Determines all control flow paths from a 'start' to an 'end' statement, where each path is a list of statements.
    fun allPaths(start: Unit, end: Unit, body: Body, icfg: BiDiInterproceduralCFG<Unit, SootMethod>): Sequence<Sequence<Unit>> =
            if (start == end)
                sequenceOf(sequenceOf(end))
            else
                actualPreds(end, body, icfg)
                        .asSequence()
                        .flatMap { allPaths(start, it, body, icfg) }
                        .map { it + end }

    // Determines a precise list of predecessor statements by combining info from the ICFG and traps.
    fun actualPreds(stmt: Unit, body: Body, icfg: BiDiInterproceduralCFG<Unit, SootMethod>): List<Unit> {
        // ICFG does not contain predecessors of the first statements in catch-blocks, so we also analyze
        // the method's traps to find potential exception-throwing statements leading to the catch-block.
        val predsIcfg = icfg.getPredsOf(stmt)
                .filter { body.units.asSequence().comesBefore(it, stmt) } // HACK to avoid infinite recursion caused by loops
        val predsTraps = body.traps.asSequence()
                .filter { trap -> trap.handlerUnit === stmt }
                .flatMap { trap -> body.units.asSequence().between(trap.beginUnit, trap.endUnit) }
        return (predsIcfg + predsTraps).distinct()
    }

    // For a list of control-flow paths (i.e. Unit-sequences), returns only the statements visited by all paths
    fun List<Sequence<Unit>>.commonStatements() =
            asSequence()
                    .flatten()
                    .groupBy { it } // use 'groupBy' to count the number of paths the statement occurs in
                    .filter { it.value.size == size }
                    .map { it.key }
                    .distinct()
                    .asSequence()

    // From a sequence of statements, filters out if-statements of which the branch(es) is/are not part of the sequence
    fun Sequence<Unit>.filterIrrelevantIfs(body: Body, icfg: BiDiInterproceduralCFG<Unit, SootMethod>) =
            zipWithNext { a, b ->
                if (a.branches() && actualPreds(b, body, icfg).size > 1)
                    // if-statement followed by a "merge point" => remove if statement
                    emptyList()
                else
                    // otherwise => keep statement
                    listOf(a)
            }.flatten()

    fun enclosingIfs(stmt: Unit, body: Body, icfg: BiDiInterproceduralCFG<Unit, SootMethod>) =
        allPaths(body.units.first, stmt, body, icfg).toList()
                .commonStatements()
                .filterIrrelevantIfs(body, icfg)
                .filterIsInstance<IfStmt>()
}

