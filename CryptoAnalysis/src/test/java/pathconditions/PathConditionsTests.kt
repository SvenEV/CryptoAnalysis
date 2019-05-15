package pathconditions

import boomerang.jimple.Statement
import crypto.pathconditions.computeRefinedSimplifiedPathConditions
import crypto.pathconditions.expressions.ContextFormat
import crypto.pathconditions.expressions.toString
import org.junit.Test
import soot.jimple.Stmt
import javax.crypto.Cipher
import kotlin.reflect.KFunction
import kotlin.test.assertEquals

/**
 * @param relevantLines The line numbers (with 0 referring to the first statement in the test method) of relevant statements. The last line number is used to determine the sink statement.
 * @param expectedCondition Expected condition as String
 */
data class DataFlow(val relevantLines: List<Int>, val expectedCondition: String)

@Suppress("CanBeVal", "LiftReturnOrAssignment", "ConstantConditionIf", "ASSIGNED_BUT_NEVER_ACCESSED_VARIABLE", "UNUSED_VALUE", "VARIABLE_WITH_REDUNDANT_INITIALIZER", "MemberVisibilityCanBePrivate")
class PathConditionsTests : SootBasedTest() {

    val c1 = false
    val c2 = false
    val i = 0
    val j = 0

    /**
     * Given a set of relevant statements, tests whether the correct path conditions are computed.
     * @param testMethod The method to be analyzed
     */
    fun test(testMethod: KFunction<Unit>, vararg dataFlows: DataFlow) {
        val method = thisClass.methods.single { it.name == testMethod.name }
        val units = method.retrieveActiveBody().units

        val firstLine = units
            .map { it.lineNumber() }
            .first { it >= 0 }

        dataFlows.forEach { flow ->
            val sinkStatement = units
                .singleOrNull { it.lineNumber() - firstLine == flow.relevantLines.last() }
                ?: throw Exception("No (unique) sink statement found at line '${flow.relevantLines.last()}'")

            val relevantStatements = units
                .filter { it.lineNumber() - firstLine in flow.relevantLines }
                .map { Statement(it as Stmt, method) }
                .toSet()

            val foreignRelevantStmts = units
                .filter {
                    it.lineNumber() - firstLine in dataFlows
                        .asSequence()
                        .minus(flow)
                        .flatMap { f -> f.relevantLines.asSequence() }
                }
                .map { Statement(it as Stmt, method) }
                .toSet()

            val conditions = computeRefinedSimplifiedPathConditions(sinkStatement, relevantStatements, foreignRelevantStmts)

            val conditionsAsString = conditions
                .map { it.condition.toString(ContextFormat.ContextFree) }
                .singleOrNull() ?: "true"

            val dot = conditions.first().asDirectedGraph().toDotString()

            assertEquals(flow.expectedCondition, conditionsAsString,
                "Actual path conditions do not match expected ones")
        }
    }


    private fun simpleBranching() {
        if (i > 0) {
            if (i < 5) {
                nop()
            } else {
                nop()
            }
        } else {
            nop()
        }
        nop() // sink
    }

    @Test
    fun simpleBranchingTest1() = test(
        ::simpleBranching,
        DataFlow(listOf(2, 9), "this.i > 0L && 5L > this.i")
    )

    @Test
    fun simpleBranchingTest2() = test(
        ::simpleBranching,
        DataFlow(listOf(4, 9), "this.i >= 5L") // implies "$param0 > 0"
    )

    @Test
    fun simpleBranchingTest3() = test(
        ::simpleBranching,
        DataFlow(listOf(7, 9), "this.i <= 0L")
    )

    private fun singleFlow1() {
        val x = "A"
        var y = "B"
        if (Math.random() < .5)
            y = x
        Cipher.getInstance(x)
    }

    @Test
    fun singleFlow1Test() = test(
        ::singleFlow1,
        DataFlow(listOf(0, 4), "true")
    )

    private fun singleFlow2() {
        var x = "A"
        x = "B"
        Cipher.getInstance(x)
    }

    @Test
    fun singleFlow2Test() = test(
        ::singleFlow2,
        DataFlow(listOf(1, 2), "true")
    )

    private fun singleFlowTwoWays() {
        val x = "A"
        var z: String? = null
        if (i > 0) {
            if (j < 5) {
                nop()
            } else {
                z = x
            }
        } else {
            z = x
        }
        Cipher.getInstance(z) // sink
    }

    @Test
    fun singleFlowTwoWaysTest() = test(
        ::singleFlowTwoWays,
        DataFlow(listOf(0, 6, 9, 11), "this.j >= 5L || this.i <= 0L")
    )

    private fun multiFlow1() {
        var x = "asdf"
        if (Math.random() < .5)
            x = "no"
        Cipher.getInstance(x)
    }

    @Test
    fun multiFlow1Test() = test(
        ::multiFlow1,
        DataFlow(listOf(2, 3), "Math.random() < 0.5"),
        DataFlow(listOf(0, 3), "0.5 <= Math.random()")
    )

    private fun multiFlow2() {
        val x = "A"
        var y = "B"
        if (Math.random() < .5)
            y = x
        Cipher.getInstance(y)
    }

    @Test
    fun multiFlow2Test() = test(
        ::multiFlow2,
        DataFlow(listOf(0, 3, 4), "Math.random() < 0.5"),
        DataFlow(listOf(1, 4), "0.5 <= Math.random()")
    )

    private fun multiFlow3() {
        val x = "A"
        var y = x
        if (Math.random() < .5)
            y = "AES"
        Cipher.getInstance(y)
    }

    @Test
    fun multiFlow3Test() = test(
        ::multiFlow3,
        DataFlow(listOf(0, 1, 4), "0.5 <= Math.random()"),
        DataFlow(listOf(1, 3, 4), "Math.random() < 0.5")
    )

    private fun merge1() {
        val x = "A" // 1
        var y: String? = null
        var z: String? = null
        if (c1) {
            if (c2)
                y = x // 1
            else
                z = x
            z = y // 1
        }
        Cipher.getInstance(z) // 1
    }

    @Test
    fun merge1Test() = test(
        ::merge1,
        DataFlow(listOf(0, 5, 8, 10), "this.c1 && this.c2")
    )


    private fun merge2() {
        val x = "A" // 1
        var y: String? = null
        var z: String? = null
        if (c1) {
            if (c2) {
                y = x // 1
                z = y // 1
            } else {
                z = x // 1
            }
        }
        Cipher.getInstance(z) // 1
    }

    @Test
    fun merge2Test() = test(
        ::merge2,
        DataFlow(listOf(0, 5, 6, 8, 11), "this.c1")
    )

    private fun equalAllocSites() {
        var x: String? = null // null assignment required to prevent optimization
        if (c1)
            x = "A"
        else
            x = "A"
        Cipher.getInstance(x)
    }

    @Test
    fun equalAllocSitesTest() = test(
        ::equalAllocSites,
        DataFlow(listOf(2, 5), "this.c1"),
        DataFlow(listOf(4, 5), "!this.c1")
    )

    private fun superfluousAssignment() {
        val x = "A"
        var y = x
        if (c1)
            y = x
        if (c2)
            y = x
        Cipher.getInstance(y)
    }

    @Test
    fun superfluousAssignmentTest() = test(
        ::superfluousAssignment,
        // Optimally, we would know that the two 'y = x' assignments are useless, but since
        // we don't track variable values we have to be conservative and assume that the
        // statements are required. This results in a condition that only covers a subset of
        // the possible scenarios that lead to this data flow.
        DataFlow(listOf(0, 1, 3, 5, 6), "this.c1 && this.c2")
    )

    // Consider the "D"-flow. If we'd propagate "false"...
    // (1) after visiting a foreign statement, or
    // (2) after merging two FOREIGN-branches
    // ...we'd never get the correct condition "c2", but just "false".
    private fun mustNotPropagateFalseAfterForeignStatement() {
        var x = "A"

        if (c1)
            x = "B"
        else
            x = "C"

        if (c2)
            x = "D"

        Cipher.getInstance(x)
    }

    @Test
    fun mustNotPropagateFalseAfterForeignStatementTest() = test(
        ::mustNotPropagateFalseAfterForeignStatement,
        DataFlow(listOf(3, 10), "this.c1 && !this.c2"),
        DataFlow(listOf(5, 10), "!this.c1 && !this.c2"),
        DataFlow(listOf(8, 10), "this.c2")
    )

    // Consider the "B"-flow. Even though the "c1"-branch contains a foreign statement,
    // we shouldn't discard it because at that point we haven't even visited the source
    // of the "B"-flow yet and what happens before the source doesn't matter.
    private fun lateSource() {
        var x = "A"
        if (c1)
            nop()
        if (c2)
            x = "B"
        Cipher.getInstance(x)
    }

    @Test
    fun lateSourceTest() = test(
        ::lateSource,
        DataFlow(listOf(0, 2, 5), "this.c1 && !this.c2"),
        DataFlow(listOf(4, 5), "this.c2")
    )

    private fun covaIndirectConcrete1(d: Int) {
        var a = 0
        if (d == 2) {
            a = 1
        }
        if (d == 3) {
            a = 2
        }
        var e = 0
        if (a >= 0) {
            e = 1
        } else {
            e = 2
        }
        if (a < 2) {
            e = 3
        }
        nop()
    }

    @Test
    fun covaIndirectConcrete1Test() = test(
        ::covaIndirectConcrete1,
        DataFlow(listOf(9, 16), "a >= 0L && a >= 2L"),
        DataFlow(listOf(11, 16), "0L > a && a >= 2L"),
        DataFlow(listOf(14, 16), "2L > a")
    )

    private fun covaInfeasible1(b: Boolean) {
        if (b) {
            println()
            val a = !b
            if (a) {
                nop()
            }
        }
    }

    @Test
    fun covaInfeasible1Test() = test(
        ::covaInfeasible1,
        DataFlow(listOf(4), "false")
    )


    private fun loop() {
        var x = "A"
        for (i in 0..10) {
            while (c1) {
                x = "B"
            }
            nop()
        }
        Cipher.getInstance(x)
    }

    @Test
    fun loopTest() = test(
        ::loop,
        DataFlow(listOf(0, 7), "i > 10L"), // For "A", just skipping the outer loop is one of the valid paths
        DataFlow(listOf(3, 7), "false") // For "B" both must hold, 'c1' (to execute 'x = "B"') and '!c1' (to reach sink)
    )

    private fun loopWithSinkInsideLoop() {
        var x = "A"
        for (i in 0..10) {
            while (c1) {
                x = "B"
            }
            Cipher.getInstance(x)
        }
    }

    @Test
    fun loopWithSinkInsideLoopTest() = test(
        ::loopWithSinkInsideLoop,
        DataFlow(listOf(0, 5), "i <= 10L && !this.c1"),
        DataFlow(listOf(3, 5), "false")
    )

    private fun nestedForeign() {
        var x = "A"
        if (c1) {
            if (c2)
                x = "B"
        }
        Cipher.getInstance(x)
    }

    @Test
    fun nestedForeignTest() = test(
        ::nestedForeign,
        DataFlow(listOf(0, 5), "!this.c1 || !this.c2"),
        DataFlow(listOf(3, 5), "this.c1 && this.c2")
    )
}
