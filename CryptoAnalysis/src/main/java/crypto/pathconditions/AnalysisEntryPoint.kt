package crypto.pathconditions

import boomerang.jimple.Statement
import boomerang.preanalysis.BoomerangPretransformer
import crypto.pathconditions.boomerang.extractRelevantStatements
import crypto.pathconditions.debug.prettyPrint
import crypto.pathconditions.expressions.JTrue
import crypto.pathconditions.refinement.refine
import soot.PackManager
import soot.SceneTransformer
import soot.Transform

/**
 * A (temporary) entry point to perform all steps of the analysis
 * (determine relevant statements and compute, refine and simplify conditions)
 */

fun solve(query: PathConditionsQuery): Set<PathConditionResult> {
    val relevantStatements = extractRelevantStatements(query)
    return computeRefinedSimplifiedPathConditions(relevantStatements)
}

fun computeRefinedSimplifiedPathConditions(relevantStatements: Iterable<Statement>) =
    computePathConditions(relevantStatements)
        .map { PathConditionResult(it.method, simplifyTerm(refine(it.condition))) }
        .filter { it.condition !is JTrue } // ignore TRUE conditions
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