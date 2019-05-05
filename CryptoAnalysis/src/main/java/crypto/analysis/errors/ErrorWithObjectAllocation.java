package crypto.analysis.errors;

import boomerang.jimple.Statement;
import boomerang.jimple.Val;
import crypto.analysis.IAnalysisSeed;
import crypto.pathconditions.PathConditionResult;
import crypto.rules.CryptSLRule;
import sync.pds.solver.nodes.Node;

import java.util.Collection;
import java.util.Collections;
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

	public Collection<Node<Statement, Val>> getDataFlowPath() {
		return objectAllocationLocation.getDataFlowPath();
	}

	public Set<PathConditionResult> computePathConditions() {
		Set<Statement> relevantStatements = getDataFlowPath().stream().map(Node::stmt).collect(Collectors.toSet());

		return computeRefinedSimplifiedPathConditions(
				objectAllocationLocation.stmt().getUnit().get(),
				relevantStatements,
				Collections.emptySet());
	}
}
