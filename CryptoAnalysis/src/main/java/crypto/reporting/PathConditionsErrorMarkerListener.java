package crypto.reporting;

import com.google.common.collect.Table;
import com.google.common.collect.Tables;
import crypto.analysis.errors.AbstractError;
import crypto.analysis.errors.ErrorWithObjectAllocation;
import crypto.pathconditions.expressions.JFalse;
import soot.SootClass;
import soot.SootMethod;

import java.util.Set;

public class PathConditionsErrorMarkerListener extends ErrorMarkerListener {

	public Table<SootClass, SootMethod, Set<AbstractError>> getErrorMarkers() {
		return Tables.unmodifiableTable(errorMarkers);
	}

	@Override
	public boolean filterError(AbstractError error) {
		if (error instanceof ErrorWithObjectAllocation) {
			// If one of the path conditions is 'false', we have a false positive and the error can be ignored
			// TODO: Does this really prove false-positiveness in every case?
			ErrorWithObjectAllocation errorWithObjectAllocation = (ErrorWithObjectAllocation) error;
			// boolean hasFalseCondition = errorWithObjectAllocation.getPathConditions().stream()
			// 		.anyMatch(o -> o.getCondition().equals(JFalse.INSTANCE));
			// return !hasFalseCondition;

			// TODO: Re-implement false-positive filtering somewhere else
			return true;
		}
		return true;
	}
}
