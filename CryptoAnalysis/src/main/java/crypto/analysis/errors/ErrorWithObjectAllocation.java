package crypto.analysis.errors;

import boomerang.jimple.Statement;
import boomerang.jimple.Val;
import crypto.analysis.IAnalysisSeed;
import crypto.pathconditions.PathConditionResult;
import crypto.rules.CryptSLRule;
import kotlin.Lazy;
import kotlin.LazyKt;
import sync.pds.solver.nodes.Node;

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import static crypto.pathconditions.AnalysisEntryPointKt.computeRefinedSimplifiedPathConditions;

public abstract class ErrorWithObjectAllocation extends AbstractError {
	private final IAnalysisSeed objectAllocationLocation;

	public ErrorWithObjectAllocation(Statement errorLocation, CryptSLRule rule, IAnalysisSeed objectAllocationLocation) {
		super(errorLocation, rule);
		this.objectAllocationLocation = objectAllocationLocation;
	}

	public IAnalysisSeed getObjectLocation() {
		return objectAllocationLocation;
	}

	protected String getObjectType() {
		if (this.objectAllocationLocation.asNode().fact() != null && this.objectAllocationLocation.asNode().fact().value() != null)
			return " on object of type " + this.objectAllocationLocation.asNode().fact().value().getType();
		return "";
	}

	public Set<Node<Statement, Val>> getDataFlowPath() {
		return objectAllocationLocation.getDataFlowPath();
	}

	/**
	 * @param relatedErrors Errors that relate to the same statement as this error
	 */
	public Set<PathConditionResult> getPathConditions(List<ErrorWithObjectAllocation> relatedErrors) {
		Set<Statement> relevantStatements = getDataFlowPath().stream().map(Node::stmt).collect(Collectors.toSet());
		Set<Statement> foreignRelevantStmts = relatedErrors.stream()
				.flatMap(error -> error.getDataFlowPath().stream().map(Node::stmt))
				.collect(Collectors.toSet());
		return computeRefinedSimplifiedPathConditions(relevantStatements, foreignRelevantStmts);
	}
}
