package crypto.reporting;

import com.google.common.collect.Table;
import com.google.common.collect.Tables;
import crypto.analysis.errors.AbstractError;
import soot.SootClass;
import soot.SootMethod;

import java.util.Set;

public class PathConditionsErrorMarkerListener extends ErrorMarkerListener {
	public Table<SootClass, SootMethod, Set<AbstractError>> getErrorMarkers() {
		return Tables.unmodifiableTable(errorMarkers);
	}
}
