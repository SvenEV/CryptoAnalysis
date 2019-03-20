package crypto.extractparameter;

import boomerang.BackwardQuery;
import boomerang.Boomerang;
import boomerang.ForwardQuery;
import boomerang.jimple.AllocVal;
import boomerang.jimple.Statement;
import boomerang.jimple.Val;
import boomerang.results.BackwardBoomerangResults;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.Lists;
import com.google.common.collect.Multimap;
import com.google.common.collect.Sets;
import crypto.analysis.CryptoScanner;
import crypto.boomerang.CogniCryptIntAndStringBoomerangOptions;
import crypto.pathconditions.PathConditionsQuery;
import crypto.pathconditions.boomerang.RelevantStatementsExtractorKt;
import crypto.rules.CryptSLMethod;
import crypto.typestate.CryptSLMethodToSootMethod;
import crypto.typestate.LabeledMatcherTransition;
import crypto.typestate.SootBasedStateMachineGraph;
import heros.utilities.DefaultValueMap;
import soot.*;
import soot.jimple.Stmt;
import soot.jimple.toolkits.ide.icfg.BiDiInterproceduralCFG;
import typestate.finiteautomata.MatcherTransition;
import wpds.impl.Weight.NoWeight;

import java.util.*;
import java.util.Map.Entry;

public class ExtractParameterAnalysis {

	private Map<Statement, SootMethod> allCallsOnObject;
	private Collection<LabeledMatcherTransition> events = Sets.newHashSet();
	private CryptoScanner cryptoScanner;
	private Multimap<CallSiteWithParamIndex, ExtractedValue> collectedValues = HashMultimap.create();
	private Multimap<CallSiteWithParamIndex, Type> propagatedTypes = HashMultimap.create();
	private DefaultValueMap<AdditionalBoomerangQuery, AdditionalBoomerangQuery> additionalBoomerangQuery = new DefaultValueMap<AdditionalBoomerangQuery, AdditionalBoomerangQuery>() {
		@Override
		protected AdditionalBoomerangQuery createItem(AdditionalBoomerangQuery key) {
			return key;
		}
	};
	private Collection<CallSiteWithParamIndex> querySites = Sets.newHashSet();

	public ExtractParameterAnalysis(CryptoScanner cryptoScanner, Map<Statement, SootMethod> allCallsOnObject, SootBasedStateMachineGraph fsm) {
		this.cryptoScanner = cryptoScanner;
		this.allCallsOnObject = allCallsOnObject;
		for (MatcherTransition m : fsm.getAllTransitions()) {
			if (m instanceof LabeledMatcherTransition) {
				this.events.add((LabeledMatcherTransition) m);
			}
		}
	}

	public Set<AdditionalBoomerangQuery> run() {
		for (Entry<Statement, SootMethod> callSiteWithCallee : allCallsOnObject.entrySet()) {
			Statement callSite = callSiteWithCallee.getKey();
			SootMethod declaredCallee = callSiteWithCallee.getValue();
			if (callSite.isCallsite()) {
				for (LabeledMatcherTransition e : events) {
					if (e.matches(declaredCallee)) {
						injectQueryAtCallSite(e.label(), callSite);
					}
				}
			}
		}
		for (AdditionalBoomerangQuery q : additionalBoomerangQuery.keySet()) {
//			if (reports != null) {
//				reports.boomerangQueryStarted(query, q);
//			}
			q.solve();
//			if (reports != null) {
//				reports.boomerangQueryFinished(query, q);
//			}
		}

		return additionalBoomerangQuery.keySet();
	}

	public Multimap<CallSiteWithParamIndex, ExtractedValue> getCollectedValues() {
		return collectedValues;
	}

	public Multimap<CallSiteWithParamIndex, Type> getPropagatedTypes() {
		return propagatedTypes;
	}

	public Collection<CallSiteWithParamIndex> getAllQuerySites() {
		return querySites;
	}

	private void injectQueryAtCallSite(List<CryptSLMethod> list, Statement callSite) {
		if (!callSite.isCallsite())
			return;
		for (CryptSLMethod matchingDescriptor : list) {
			for (SootMethod m : CryptSLMethodToSootMethod.v().convert(matchingDescriptor)) {
				SootMethod method = callSite.getUnit().get().getInvokeExpr().getMethod();
				if (!m.equals(method))
					continue;
				{
					int index = 0;
					for (Entry<String, String> param : matchingDescriptor.getParameters()) {
						if (!param.getKey().equals("_")) {
							soot.Type parameterType = method.getParameterType(index);
							if (parameterType.toString().equals(param.getValue())) {
								addQueryAtCallsite(param.getKey(), callSite, index);
							}
						}
						index++;
					}
				}
			}
		}
	}

	public void addQueryAtCallsite(final String varNameInSpecification, final Statement stmt, final int index) {
		if (!stmt.isCallsite())
			return;
		Value parameter = stmt.getUnit().get().getInvokeExpr().getArg(index);
		if (!(parameter instanceof Local)) {
			CallSiteWithParamIndex cs = new CallSiteWithParamIndex(stmt, new Val(parameter, stmt.getMethod()), index, varNameInSpecification);
			List<Statement> dataFlowStatements = Collections.emptyList(); // TODO: What should dataFlowStatements be in this context?
			collectedValues.put(cs, new ExtractedValue(stmt, parameter, dataFlowStatements));
			querySites.add(cs);
			return;
		}
		Val queryVal = new Val((Local) parameter, stmt.getMethod());

		for (Unit pred : cryptoScanner.icfg().getPredsOf(stmt.getUnit().get())) {
			AdditionalBoomerangQuery query = additionalBoomerangQuery
					.getOrCreate(new AdditionalBoomerangQuery(new Statement((Stmt) pred, stmt.getMethod()), queryVal));
			CallSiteWithParamIndex callSiteWithParamIndex = new CallSiteWithParamIndex(stmt, queryVal, index, varNameInSpecification);
			querySites.add(callSiteWithParamIndex);
			query.addListener((q, result) -> {
				propagatedTypes.putAll(callSiteWithParamIndex, result.getPropagationType());
				for (ForwardQuery v : result.getAllocationSites().keySet()) {
					// Obtain statements along data flow path ("relevant statements")
					// TODO: Is there any difference between q.var() and v.var() or q.stmt() and v.stmt()?
					// TODO: Do we really get different data flow statements for different forward queries
					PathConditionsQuery pcQuery = new PathConditionsQuery(v.var().value(), v.stmt().getUnit().get(), v.stmt().getMethod(), site -> true);
					ArrayList<Statement> dataFlowStatements = RelevantStatementsExtractorKt.extractRelevantStatements(result, pcQuery);

					ExtractedValue extractedValue;
					if (v.var() instanceof AllocVal) {
						AllocVal allocVal = (AllocVal) v.var();
						extractedValue = new ExtractedValue(allocVal.allocationStatement(), allocVal.allocationValue(), dataFlowStatements);
					} else {
						extractedValue = new ExtractedValue(v.stmt(), v.var().value(), dataFlowStatements);
					}
					collectedValues.put(callSiteWithParamIndex, extractedValue);
				}
			});
		}
	}

	public void addAdditionalBoomerangQuery(AdditionalBoomerangQuery q, QueryListener listener) {
		AdditionalBoomerangQuery query = additionalBoomerangQuery.getOrCreate(q);
		query.addListener(listener);
	}

	public class AdditionalBoomerangQuery extends BackwardQuery {
		public AdditionalBoomerangQuery(Statement stmt, Val variable) {
			super(stmt, variable);
		}

		protected boolean solved;
		private List<QueryListener> listeners = Lists.newLinkedList();
		private BackwardBoomerangResults<NoWeight> res;

		public BackwardBoomerangResults<NoWeight> getResult() {
			return res;
		}

		public void solve() {
			Boomerang boomerang = new Boomerang(new CogniCryptIntAndStringBoomerangOptions()) {
				@Override
				public BiDiInterproceduralCFG<Unit, SootMethod> icfg() {
					return ExtractParameterAnalysis.this.cryptoScanner.icfg();
				}
			};
			res = boomerang.solve(this);
			boomerang.debugOutput();
			// log("Solving query "+ accessGraph + " @ " + stmt);
			for (QueryListener l : Lists.newLinkedList(listeners)) {
				l.solved(this, res);
			}
			solved = true;
		}

		public void addListener(QueryListener q) {
			if (solved) {
				q.solved(this, res);
				return;
			}
			listeners.add(q);
		}

	}

	private static interface QueryListener {
		public void solved(AdditionalBoomerangQuery q, BackwardBoomerangResults<NoWeight> res);
	}


}
