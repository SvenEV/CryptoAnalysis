package crypto.analysis

import boomerang.jimple.Statement
import soot.*
import soot.Unit
import soot.jimple.*
import soot.jimple.toolkits.ide.icfg.BiDiInterproceduralCFG
import java.io.PrintWriter
import java.io.StringWriter

object SvensMetricsCollector {

    fun run(seedStmt: Statement, callStmts: Iterable<Statement>, body: Body, icfg: BiDiInterproceduralCFG<Unit, SootMethod>) {
        Markdown.olItem("**`${seedStmt}`**")

        if (seedStmt.toString() == "<com.springcryptoutils.core.cipher.asymmetric.Base64EncodedCiphererImpl: java.lang.String encrypt(java.lang.String)> getInstance(\$r5)")
            println()

        val enclosingIfs = enclosingIfs(body.units.first, seedStmt.unit.get(), body, icfg).toList()

        val conditionsPerCallStmt = (callStmts.toList() - seedStmt)
                .associateWith { enclosingIfs(seedStmt.unit.get(), it.unit.get(), body, icfg).toList() }

        // TODO: Analyze the if-conditions (in particular, find out whether the statement lies in the true or the false branch)
        Markdown.tab {
            if (enclosingIfs.isNotEmpty() || true) {
                val numIfs = seedStmt.method.activeBody.units.filterIsInstance<IfStmt>().count()
                Markdown.ulItem("${enclosingIfs.size} ifs enclosing seed `$seedStmt` ($numIfs ifs in method)")
                Markdown.tab.ul(enclosingIfs.map { "${it.condition} at `${it.unit}`" })
            }

            for (call in conditionsPerCallStmt) {
                val numIfs = call.key.method.activeBody.units.filterIsInstance<IfStmt>().count()
                Markdown.ulItem("${call.value.size} ifs enclosing call `${call.key}` ($numIfs ifs in method)")
                Markdown.tab.ul(call.value.map { "${it.condition} at `${it.unit}`" })
            }

            val sw = StringWriter()
            Printer.v().printTo(body, PrintWriter(sw))
//            Markdown.codeBlock(sw.buffer.toString())
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

    fun enclosingIfs(start: Unit, end: Unit, body: Body, icfg: BiDiInterproceduralCFG<Unit, SootMethod>) =
            allPaths(start, end, body, icfg).toList()
                    .commonStatements()
                    .filterIrrelevantIfs(body, icfg)
                    .filterIsInstance<IfStmt>()
                    .map { createIfStmtInfo(it, body, icfg) }

    fun createIfStmtInfo(stmt: IfStmt, body: Body, icfg: BiDiInterproceduralCFG<Unit, SootMethod>): IfStmtInfo {
        val usedValues = stmt.condition.useBoxes.map { it.value }
        return when (stmt.condition) {
            is EqExpr, is NeExpr -> {
                val local = usedValues.filterIsInstance<Local>().firstOrNull()
                val nullConstant = usedValues.filterIsInstance<NullConstant>().firstOrNull()

                if (local != null) {
                    val allocationSites = allocationSites(local, stmt, body).toList()
                }

                val conditionInfo =
                        if (local != null && nullConstant != null)
                            NullCheck(local.type)
                        else
                            EqualityCheck(usedValues.first().type, usedValues.filterIsInstance<Constant>().first())

                IfStmtInfo(stmt, conditionInfo)
            }
            is GtExpr, is GeExpr, is LtExpr, is LeExpr -> {
                val type = usedValues.first().type
                val constant = usedValues.filterIsInstance<Constant>().firstOrNull()
                return if (constant == null)
                    IfStmtInfo(stmt, OtherCondition)
                else
                    IfStmtInfo(stmt, Comparison(type, constant))
            }
            else -> IfStmtInfo(stmt, OtherCondition)
        }
    }

    // a very basic, intra-procedural, imprecise, but alias-aware way to find allocation sites of a local
    // (in the future we'd like to use Boomerang instead)
    fun allocationSites(local: Local, stmt: Unit, body: Body): Sequence<AssignStmt> =
            body.units.asSequence().between(body.units.first, stmt)
                    .filterIsInstance<AssignStmt>()
                    .filter { it.leftOp === local }
                    .flatMap {
                        when (it.rightOp) {
                            is Local -> allocationSites(it.rightOp as Local, it, body)
                            is CastExpr -> when (val op = (it.rightOp as CastExpr).op) {
                                is Local -> allocationSites(op, it, body)
                                else -> sequenceOf(it)
                            }
                            else -> sequenceOf(it)
                        }
                    }

    data class IfStmtInfo(val unit: IfStmt, val condition: IfCondition)
}

sealed class IfCondition
data class NullCheck(val type: Type) : IfCondition() {
    override fun toString() = "Null-check on '$type'"
}

data class EqualityCheck(val type: Type, val constant: Value) : IfCondition() {
    override fun toString() = "Equality-check of type '$type' with '$constant'"
}

data class Comparison(val type: Type, val constant: Value) : IfCondition() {
    override fun toString() = "Comparison of type '$type' with '$constant'"
}

object OtherCondition : IfCondition()
