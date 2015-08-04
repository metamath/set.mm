// Define an axiom
// (Future:  make Axiom same class as State for uniformity & to simplify pgm?)
package mm;

import java.util.*;

class Axiom {
    String label, proof, description, menuEntry; 
    List<Short> assertion;
    List<List<Short>> axiomHypothesisVec;
    Set<DVPair> axiomDistVarSet; 
    Data currentState;

    private void init(String label, List<Short> assertion, String description, List<List<Short>> axHypVec, Set<DVPair> axDVS, String proof) {
	this.label = label;
	this.assertion = assertion;
	this.axiomHypothesisVec = axHypVec;
	this.axiomDistVarSet = axDVS;
	this.description = description;
	this.proof = proof;
	VariableName.init();  
	menuEntry = (1 - axiomHypothesisVec.size()) + " " + label + " " + PrimFormula.getDisplay(assertion);
    }

    Axiom(Data curState, String label, String englRPN, String descr) { 
	currentState=curState;
	init(label,englToList(englRPN),descr,new ArrayList<List<Short>>(),new HashSet<DVPair>(),""); 
    }
    Axiom(Data curState, String label, String englRPN) { this(curState,label,englRPN,""); }
    
    Axiom(Data state, State st) {
	st = new State(st);

	// Remove all assertions except last
	List<List<Short>> trimmedAssertionVec = new ArrayList<List<Short>>();
	List<String> trimmedProofVec = new ArrayList<String>();
	trimmedAssertionVec.add(st.assertionVec.get(st.assertionVec.size()-1));
	trimmedProofVec.add(st.proofVec.get(st.proofVec.size()-1));
	st.assertionVec = trimmedAssertionVec;
	st.proofVec = trimmedProofVec;
	st.normalize(); 

	currentState=state;
	init("user-" + String.valueOf(state.numThms()+1),st.assertionVec.get(st.assertionVec.size()-1),"Theorem added by user",st.hypothesisVec,st.distinctVarSet,
	     st.proofVec.get(st.proofVec.size()-1));
    }

    void addHyp(String hyp) { axiomHypothesisVec.add(englToList(hyp)); }

    void addDistinct(String dvPair) throws DVViolation {
	String[] varS=dvPair.split("\\s+");
	List<Short> var=new ArrayList<Short>(varS.length);
	for(String s : varS) var.add(Short.parseShort(s.substring(1)));
	for(int i=0; i<var.size(); i++) for(int j=i+1; j<var.size(); j++) axiomDistVarSet.add(new DVPair(var.get(i),var.get(j)));
    }

    // Convert RPN character, space-separated strings to RPN list
    // Connectives are negative, variables are positive
    private final List<Short> englToList(String englRPN) {
	List<Short> buf = new ArrayList<Short>();

	for (String token : englRPN.split("\\s+")) {
	    if (token.charAt(0) == '$') buf.add(Short.parseShort(token.substring(1)));
	    else if(currentState.hasConnective(token)) buf.add((short)-(currentState.getConnecitve(token) + 1));
	}

	return buf;
    } // englToList

    public void setDescr(String d) { description=d; }

}
