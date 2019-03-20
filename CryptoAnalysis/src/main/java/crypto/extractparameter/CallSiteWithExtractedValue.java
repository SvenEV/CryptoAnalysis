package crypto.extractparameter;

import boomerang.jimple.Statement;
import soot.Value;
import soot.jimple.Constant;

import java.util.List;

public class CallSiteWithExtractedValue {
	private final CallSiteWithParamIndex cs;
	private final ExtractedValue val;

	public CallSiteWithExtractedValue(CallSiteWithParamIndex cs, ExtractedValue val){
		this.cs = cs;
		this.val = val;
	}

	public CallSiteWithParamIndex getCallSite() {
		return cs;
	}

	public ExtractedValue getVal() {
		return val;
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
