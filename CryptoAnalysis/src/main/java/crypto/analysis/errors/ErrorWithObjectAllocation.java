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
import java.util.Set;

import static crypto.pathconditions.AnalysisEntryPointKt.computeRefinedSimplifiedPathConditions;

public abstract class ErrorWithObjectAllocation extends AbstractError {
	private final IAnalysisSeed objectAllocationLocation;
	private final Lazy<Set<PathConditionResult>> pathConditions;

	public ErrorWithObjectAllocation(Statement errorLocation, CryptSLRule rule, IAnalysisSeed objectAllocationLocation) {
		super(errorLocation, rule);
		this.objectAllocationLocation = objectAllocationLocation;
		this.pathConditions = LazyKt.lazy(() -> {
			Iterable<Statement> relevantStatements = getDataFlowPath().stream().map(Node::stmt)::iterator;
			return computeRefinedSimplifiedPathConditions(relevantStatements, new HashSet<>() /* TODO: foreignRelevantStatements */);
		});
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

	public Set<PathConditionResult> getPathConditions() {
		return pathConditions.getValue();
	}
}
