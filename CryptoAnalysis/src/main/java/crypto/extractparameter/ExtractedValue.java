package crypto.extractparameter;

import boomerang.jimple.Statement;
import soot.Value;

import java.util.List;

public class ExtractedValue {
	private final Statement stmt;
	private final Value val;
	private final List<Statement> dataFlowStatements;

	public ExtractedValue(Statement stmt, Value val, List<Statement> dataFlowStatements) {
		this.stmt = stmt;
		this.val = val;
		this.dataFlowStatements = dataFlowStatements;
	}

	public Statement stmt() {
		return stmt;
	}
	
	public Value getValue() {
		return val;
	}

	public List<Statement> getDataFlowStatements() {
		return dataFlowStatements;
	}

	@Override
	public String toString() {
		return "Extracted Value: " + val + " at " +stmt;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((stmt == null) ? 0 : stmt.hashCode());
		result = prime * result + ((val == null) ? 0 : val.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		ExtractedValue other = (ExtractedValue) obj;
		if (stmt == null) {
			if (other.stmt != null)
				return false;
		} else if (!stmt.equals(other.stmt))
			return false;
		if (val == null) {
			if (other.val != null)
				return false;
		} else if (!val.equals(other.val))
			return false;
		return true;
	}
	
}
