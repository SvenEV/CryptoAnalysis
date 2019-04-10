package pathconditions

import boomerang.jimple.Statement
import crypto.pathconditions.computeRefinedSimplifiedPathConditions
import crypto.pathconditions.expressions.WithContextFormat
import crypto.pathconditions.expressions.toString
import org.junit.Test
import soot.jimple.Stmt
import javax.crypto.Cipher
import kotlin.reflect.KFunction
import kotlin.test.assertEquals

data class DataFlow(val relevantLines: Set<Int>, val expectedCondition: String)

class PathConditionsTests : SootBasedTest() {
    /**
     * Given a set of relevant statements, tests whether the correct path conditions are computed.
     * @param relevantLines The line numbers (with 0 referring to the first statement in [testMethod]) of relevant statements
     * @param expectedConditions Expected conditions as Strings
     * @param testMethod The method to be analyzed
     */
    fun test(testMethod: KFunction<Unit>, vararg dataFlows: DataFlow) {
        val method = thisClass.methods.single { it.name == testMethod.name }
        val units = method.retrieveActiveBody().units

        val firstLine = units
            .map { it.lineNumber() }
            .first { it >= 0 }

        dataFlows.forEach { flow ->
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

            val conditions = computeRefinedSimplifiedPathConditions(relevantStatements, foreignRelevantStmts)

            val conditionsAsString = conditions
                .map { it.condition.toString(WithContextFormat.ContextFree) }
                .singleOrNull() ?: "true"

            assertEquals(flow.expectedCondition, conditionsAsString,
                "Actual path conditions do not match expected ones")
        }
    }


    private fun simpleBranching(i: Int) {
        if (i > 0) {
            if (i < 5) {
                nop()
            } else {
                nop()
            }
        } else {
            nop()
        }
    }

    @Test
    fun simpleBranchingTest1() = test(
        ::simpleBranching,
        DataFlow(setOf(2), "\$param0 > 0L && 5L > \$param0")
    )

    @Test
    fun simpleBranchingTest2() = test(
        ::simpleBranching,
        DataFlow(setOf(4), "\$param0 >= 5L") // implies "$param0 > 0"
    )

    @Test
    fun simpleBranchingTest3() = test(
        ::simpleBranching,
        DataFlow(setOf(7), "\$param0 <= 0L")
    )

    @Test
    fun simpleBranchingTest4() = test(
        ::simpleBranching,
        DataFlow(setOf(4, 7), "false")
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
        DataFlow(setOf(0, 4), "true")
    )

    private fun singleFlow2() {
        var x = "A"
        x = "B"
        Cipher.getInstance(x)
    }

    @Test
    fun singleFlow2Test() = test(
        ::singleFlow2,
        DataFlow(setOf(1, 2), "true")
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
        DataFlow(setOf(2, 3), "Math.random() < 0.5"),
        DataFlow(setOf(0, 3), "0.5 <= Math.random()")
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
        DataFlow(setOf(0, 3, 4), "Math.random() < 0.5"),
        DataFlow(setOf(1, 4), "0.5 <= Math.random()")
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
        DataFlow(setOf(0, 1, 4), "0.5 <= Math.random()"),
        DataFlow(setOf(1, 3, 4), "Math.random() < 0.5")
    )
}
