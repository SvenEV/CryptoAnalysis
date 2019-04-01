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

class PathConditionsTests : SootBasedTest() {
    /**
     * Given a set of relevant statements, tests whether the correct path conditions are computed.
     * @param relevantLines The line numbers (with 0 referring to the first statement in [testMethod]) of relevant statements
     * @param expectedConditions Expected conditions as Strings
     * @param testMethod The method to be analyzed
     */
    fun test(relevantLines: Set<Int>, expectedConditions: Set<String>, testMethod: KFunction<kotlin.Unit>) {
        val method = klass.methods.single { it.name == testMethod.name }
        val units = method.retrieveActiveBody().units

        val firstLine = units
            .map { it.lineNumber() }
            .first { it >= 0 }

        val relevantStatements = units
            .filter { it.lineNumber() - firstLine in relevantLines }
            .map { Statement(it as Stmt, method) }

        val conditions = computeRefinedSimplifiedPathConditions(relevantStatements)

        val conditionsAsString = conditions
            .map { it.condition.toString(WithContextFormat.ContextFree) }
            .toSet()

        assertEquals(expectedConditions.toSet(), conditionsAsString,
            "Actual path conditions do not match expected ones")
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
        setOf(2),
        setOf("\$param0 > 0L && 5L > \$param0"),
        ::simpleBranching
    )

    @Test
    fun simpleBranchingTest2() = test(
        setOf(4),
        setOf("\$param0 >= 5L"), // implies "$param0 > 0"
        ::simpleBranching
    )

    @Test
    fun simpleBranchingTest3() = test(
        setOf(7),
        setOf("\$param0 <= 0L"),
        ::simpleBranching
    )

    @Test
    fun simpleBranchingTest4() = test(
        setOf(4, 7),
        setOf("false"),
        ::simpleBranching
    )


    private fun multiAssignment() {
        var x = "asdf"

        if (Math.random() < .5)
            x = "no"

        val c = Cipher.getInstance(x)
    }

    @Test
    fun multiAssignmentTest1() = test(
        setOf(3, 5),
        setOf("Math.random() < 0.5"),
        ::multiAssignment
    )

    @Test
    fun multiAssignmentTest2() = test(
        setOf(0, 5),
        setOf("Math.random() >= 0.5"),
        ::multiAssignment
    )
}