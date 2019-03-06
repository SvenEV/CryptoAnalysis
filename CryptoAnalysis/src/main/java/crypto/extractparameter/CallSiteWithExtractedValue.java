package crypto.extractparameter;

import boomerang.jimple.Statement;
import soot.Value;
import soot.jimple.Constant;

import java.util.List;

public class CallSiteWithExtractedValue {
	private final CallSiteWithParamIndex cs;
	private final ExtractedValue val;
	private final List<Statement> dataFlowStatements;

	public CallSiteWithExtractedValue(CallSiteWithParamIndex cs, ExtractedValue val, List<Statement> dataFlowStatements){
		this.cs = cs;
		this.val = val;
		this.dataFlowStatements = dataFlowStatements;
	}

	public CallSiteWithParamIndex getCallSite() {
		return cs;
	}

	public ExtractedValue getVal() {
		return val;
	}

	public List<Statement> getDataFlowStatements() {
		return dataFlowStatements;
	}

	@Override
	public String toString() {
		String res = "";
		switch(cs.getIndex()) {
			case 0: 
				res = "First ";
				break;
			case 1: 
				res = "Second ";
				break;
			case 2: 
				res = "Third ";
				break;
			case 3: 
				res = "Fourth ";
				break;
			case 4: 
				res = "Fiveth ";
				break;
			case 5: 
				res = "Sixth ";
				break;
		}
		res += "parameter";
		if(val != null && val.getValue() != null){
			Value allocVal = val.getValue();
			if(allocVal instanceof Constant){
				res += " (with value " + allocVal +")";
			}
		}
		return res;
	}
}
