package crypto.pathconditions

import boomerang.jimple.Statement
import boomerang.preanalysis.BoomerangPretransformer
import crypto.pathconditions.boomerang.extractRelevantStatements
import crypto.pathconditions.debug.prettyPrint
import crypto.pathconditions.refinement.refined
import soot.PackManager
import soot.SceneTransformer
import soot.Transform
import soot.Unit

/**
 * A (temporary) entry point to perform all steps of the analysis
 * (determine relevant statements and compute, refine and simplify conditions)
 */

fun solve(query: PathConditionsQuery): Set<PathConditionResult> {
    val relevantStatements = extractRelevantStatements(query)
    return computeRefinedSimplifiedPathConditions(query.statement, relevantStatements, emptySet() /* TODO: foreignRelevantStatements */)
}

fun computeRefinedSimplifiedPathConditions(
    sinkStatement: Unit,
    relevantStatements: Set<Statement>,
    foreignRelevantStatements: Set<Statement>) =

    computePathConditions(sinkStatement, relevantStatements, foreignRelevantStatements)
        .map {
            try {
                it.copy(condition = it.condition.refined().simplified())
            } catch (ex: Exception) {
                throw Exception("Failed to refine or simplify '${it.condition}' from method '${it.method.name}'.${System.lineSeparator()}${it.method.prettyPrint()}", ex)
            }
        }
        .toSet()

fun pathConditionsAnalysisTransformer(createQuery: () -> PathConditionsQuery) = object : SceneTransformer() {
    override fun internalTransform(phaseName: String?, options: MutableMap<String, String>?) {
        val query = createQuery()
        val simplifiedConditions = solve(query)
        val jimple = simplifiedConditions.map { it.method.prettyPrint() }

        //val conditionTree = simplifiedCondition.toDotGraph().toDotString()
    }
}

fun analyze(transformer: SceneTransformer) =
    PackManager.v().apply {
        getPack("wjtp").add(Transform("wjtp.ifds", transformer))
        getPack("cg").apply()
        BoomerangPretransformer.v().apply()
        getPack("wjtp").apply()
    }!!