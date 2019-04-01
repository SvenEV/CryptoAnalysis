package pathconditions

import crypto.pathconditions.expressions.*
import crypto.pathconditions.ofType
import crypto.pathconditions.refinement.refine
import crypto.pathconditions.simplifyTerm
import org.junit.Test
import soot.Scene
import soot.jimple.ReturnStmt
import kotlin.reflect.KFunction
import kotlin.test.assertEquals

class RefinementAndSimplificationTests : SootBasedTest() {
    /**
     * Refines and simplifies the return-expression of a method and checks whether the result is as expected.
     * @testMethod Method with a single return statement returning Boolean
     * @expectedResult Expected expression after refinement and simplification
     */
    fun test(testMethod: KFunction<Boolean>, expectedResult: String) {
        // Find the query variable and statement
        val method = klass.methods.single { it.name == testMethod.name }
        Scene.v().entryPoints.add(method)

        println()
        println("Method '${method.name}':")
        val returnStmt = method.retrieveActiveBody().units.ofType<ReturnStmt>().last()
        val expression = parseJimpleExpression(ValueWithContext(returnStmt.op, returnStmt, method), NoTypeHint)
        println("    Original:    ${expression.toString(WithContextFormat.ContextFree)}")
        val refined = refine(expression)
        println("    Refined:     ${refined.toString(WithContextFormat.ContextFree)}")
        val simplified = simplifyTerm(refined)
        println("    Simplified:  ${simplified.toString(WithContextFormat.ContextFree)}")

        println("    Expected:    $expectedResult")
        assertEquals(expectedResult, simplified.toString(WithContextFormat.ContextFree))
    }

    private fun a(): Boolean {
        val foo = 12
        val bar = foo + 3
        val r = bar == 15
        return r
    }

    @Test
    fun aTest() = test(::a, "true")

    private fun b(): Boolean {
        val foo = 12
        val bar = foo + 3
        return bar > 15
    }

    @Test
    fun bTest() = test(::b, "false")

    private fun c(): Boolean {
        val foo = Math.random()
        val bar = 3
        return bar + 7 <= foo + 2
    }

    @Test
    fun cTest() = test(::c, "10.0 <= Math.random() + 2.0")

    private fun conditionalInt(): Boolean {
        val foo = System.out
        val x = if (foo == null) 4 else -4
        return x > 2
    }

    @Test
    fun conditionalIntTest() = test(::conditionalInt, "(System.out == null ? 4 : -4) > 2")

    private fun conditionalBool(): Boolean {
        val x = if (Math.random() < .5) false else true
        return x;
    }

    @Test
    fun conditionalBoolTest() = test(::conditionalBool, "Math.random() >= 0.5")

    fun stringOps(): Boolean {
        val y = "a" + "b"
        return y == "ab"
    }

    @Test
    fun stringOpsTest() = test(::stringOps, "true")
}