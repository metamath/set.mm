// Define the stack (state)
package mm;

import java.util.*;

class State {
    short maxVar; /* Largest variable used */
    List<List<Short>> assertionVec;
    List<String> proofVec; // Proof for each assertion
    List<List<Short>> hypothesisVec;
    Set<DVPair> distinctVarSet; 

    SortedMap<String,Axiom> userThms; // copy of userTheorems; used for Undo
    int currentFam; // for Undo

    Data stateInf;

    State(Data master) { 
	maxVar = 0;
	assertionVec = new ArrayList<List<Short>>();
	proofVec = new ArrayList<String>();
	hypothesisVec = new ArrayList<List<Short>>();
	distinctVarSet = new HashSet<DVPair>();
	userThms = new TreeMap<String,Axiom>(master.getThms());
	currentFam = master.getFamily();
	stateInf = master;
    }
    State(State that) {
	maxVar = that.maxVar;
	assertionVec = new ArrayList<List<Short>>(that.assertionVec);
	proofVec = new ArrayList<String>(that.proofVec);
	hypothesisVec = new ArrayList<List<Short>>(that.hypothesisVec);
	distinctVarSet = new HashSet<DVPair>(that.distinctVarSet);
	stateInf = that.stateInf;
    }
    List<Short> getAssertion(int position) {return assertionVec.get(position);}
    List<Short> getStackTop() { return getAssertion(assertionVec.size()-1); }
    void pushAssertion(List<Short> assertion, String proof) {
	assertionVec.add(assertion);
	proofVec.add(proof);
    }
    void removeAssertionAt(int position) {assertionVec.remove(position);}
    void addHyp() {
	List<Short> t=new ArrayList<Short>(1);
	t.add(++maxVar);
	hypothesisVec.add(t);}
    void removeHypAt(int position) {hypothesisVec.remove(position);}

    private short scanVec(List<List<Short>> vec, short[] varMap, short maxVar) {
	for(int i=0; i< vec.size(); i++) {
	    List<Short> scanBuf=new ArrayList<Short>(vec.get(i));
	    for (int j = 0; j < scanBuf.size(); j++) {
		short c = scanBuf.get(j);
		if (c < 0) continue; // not a variable
		if (varMap[c] == 0) varMap[c] = ++maxVar; // Add new variable
		scanBuf.set(j, varMap[c]);
	    }
	    vec.set(i, scanBuf);
	}
	return maxVar;
    }
	    

    /** Renumber all variables; reduce maxVar if gaps were eliminated
     *  Also, trim off any distinct pairs that aren't in assertion or hyp
     * (important, otherwise distinct var list will have garbage entries)
     *  Note:  variables are numbered starting at 1, not 0. */
    void normalize() {
	short[] varMap = new short[maxVar + 1];
	Set<DVPair> newDVS=new HashSet<DVPair>();

	maxVar=scanVec(assertionVec, varMap, (short)0);
	maxVar=scanVec(hypothesisVec, varMap, maxVar);

	// Scan distinct variable pairs
	for (DVPair dVC : distinctVarSet) {
	    boolean didSub=false;
	    try {
		short a=varMap[dVC.first]==0 ? dVC.first : varMap[dVC.first];
		short b=varMap[dVC.second]==0 ? dVC.second : varMap[dVC.second];
		dVC=new DVPair(a,b);
		didSub=!(varMap[dVC.first]==0 && varMap[dVC.second]==0);
	    }
	    catch(DVViolation e) {
		e.printStackTrace();
		System.err.println("DVViolation: " + varMap[dVC.first] + " " + varMap[dVC.second] + " " + dVC);
	    }
	    if(didSub) newDVS.add(dVC);
	}
	distinctVarSet=newDVS;
	// Initialize variable name/type finder
	VariableName.init();
    }

    /** Build a special version of a State containing all steps of the proof
     *  instead of just the stack entries.  Also, each proofVec string in the
     *  special State has <step# label,step-ref,step-ref,...> instead of an
     *  axiom list.  Used to display detailed proof for the 'Proof Info'
     *  option. */
    final State buildProofInfoState() {
	// Add proof steps one by one with special unify() mode, keeping all steps
	// Get the axiom-list version of the proof of the top of the stack
	String proof = proofVec.get(proofVec.size()-1);
	State proofInfoState = new State(stateInf);
	// Copy any hypotheses
	for (int i = 0; i < hypothesisVec.size(); i++)  proofInfoState.addHyp();
	// Scan the axiom-list proof
	for (String label : proof.split("\\s+")) {
	    if (label.charAt(0) == '$') { // Hypothesis $hypnn - future: make sure that $ is not allowed if user name accepted for user proofs
		int hypNum = Integer.parseInt(label.substring(4)) - 1;
		proofInfoState.pushAssertion(proofInfoState.hypothesisVec.get(hypNum),
					     // Special label for hypothesis step
					     String.valueOf(proofInfoState.assertionVec.size() + 1) + " " + label);
	    } else proofInfoState = new Unification(stateInf).unify(label, proofInfoState, true);
	}

	// Sort the proof steps (they are not sorted in proofInfoState)
	int[] stepSortMap = new int[proofInfoState.assertionVec.size()];
	for (int i = 0; i < stepSortMap.length; i++) {
	    String labl = proofInfoState.proofVec.get(i);
	    stepSortMap[Integer.parseInt(labl.split("\\s+")[0])-1] = i;
	}
	List<List<Short>> sortedAssertionVec = new ArrayList<List<Short>>();
	List<String> sortedProofVec = new ArrayList<String>();
	for (int step : stepSortMap) {
	    sortedAssertionVec.add(proofInfoState.assertionVec.get(step));
	    sortedProofVec.add(proofInfoState.proofVec.get(step));
	}
	proofInfoState.assertionVec = sortedAssertionVec;
	proofInfoState.proofVec = sortedProofVec;
	// end sort

	proofInfoState.normalize(); // Trim distinct vars, init var names
	// Dummy run thru steps in reverse order for desired variable name
	// assignment
	for (int i = proofInfoState.assertionVec.size() - 1; i >=0; i--) PrimFormula.getDisplay(proofInfoState.assertionVec.get(i));
	return proofInfoState;
    } // buildProofInfoState

}
