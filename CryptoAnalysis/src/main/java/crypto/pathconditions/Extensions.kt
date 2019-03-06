package crypto.pathconditions

import boomerang.Query
import boomerang.jimple.Statement
import boomerang.results.BackwardBoomerangResults
import boomerang.solver.AbstractBoomerangSolver
import soot.SootMethod
import soot.Value
import soot.jimple.Stmt
import wpds.impl.Weight

inline fun <reified U> Sequence<*>.ofType() =
    filter { it is U }.map { it as U }

inline fun <reified U> Iterable<*>.ofType() =
    filter { it is U }.map { it as U }

// Helper function to obtain private field 'queryToSolvers' of Boomerang results
@Suppress("UNCHECKED_CAST")
fun <W : Weight> BackwardBoomerangResults<W>.queryToSolvers(): Map<Query, AbstractBoomerangSolver<W>> {
    val field = this.javaClass.superclass.getDeclaredField("queryToSolvers")
    field.isAccessible = true
    return field.get(this) as Map<Query, AbstractBoomerangSolver<W>>
}

data class PathConditionsQuery(
    val variable: Value,
    val statement: Stmt,
    val method: SootMethod,
    val checkAllocationSite: (Statement) -> Boolean
)