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
    fun test(dataFlows: Set<DataFlow>, testMethod: KFunction<kotlin.Unit>) {
        val method = klass.methods.single { it.name == testMethod.name }
        val units = method.retrieveActiveBody().units

        val firstLine = units
            .map { it.lineNumber() }
            .first { it >= 0 }

        dataFlows.forEach { flow ->

            val relevantStatements = units
                .filter { it.lineNumber() - firstLine in flow.relevantLines }
                .map { Statement(it as Stmt, method) }

            val foreignRelevantStmts = units
                .filter { it.lineNumber() - firstLine in dataFlows.minus(flow).flatMap { f -> f.relevantLines } }
                .map { Statement(it as Stmt, method) }

            val conditions = computeRefinedSimplifiedPathConditions(relevantStatements, foreignRelevantStmts)

            val conditionsAsString = conditions
                .map { it.condition.toString(WithContextFormat.ContextFree) }
                .single()

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
        setOf(
            DataFlow(setOf(2), "\$param0 > 0L && 5L > \$param0")
        ),
        ::simpleBranching
    )

    @Test
    fun simpleBranchingTest2() = test(
        setOf(
            DataFlow(setOf(4), "\$param0 >= 5L") // implies "$param0 > 0"
        ),
        ::simpleBranching
    )

    @Test
    fun simpleBranchingTest3() = test(
        setOf(
            DataFlow(setOf(7), "\$param0 <= 0L")
        ),
        ::simpleBranching
    )

    @Test
    fun simpleBranchingTest4() = test(
        setOf(
            DataFlow(setOf(4, 7), "false")
        ),
        ::simpleBranching
    )


    private fun multiAssignment() {
        var x = "asdf"

        if (Math.random() < .5)
            x = "no"

        val c = Cipher.getInstance(x)
    }

    @Test
    fun multiAssignmentTest() = test(
        setOf(
            DataFlow(setOf(3, 5), "Math.random() < 0.5"),
            DataFlow(setOf(0, 5), "0.5 <= Math.random()")
        ),
        ::multiAssignment
    )
}