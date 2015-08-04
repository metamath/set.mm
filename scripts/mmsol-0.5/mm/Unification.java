// Define unification methods
package mm;

import java.util.*;

public class Unification {

    private short newMaxVar; // New largest variable
    private List<Substitution> substVec; // Substitution list to make throughout State

    private List<List<Short>> axiomHypVec, stateHypVec;

    Data stateInf;

    Unification(Data state) { 
	axiomHypVec=new ArrayList<List<Short>>();
	stateHypVec=new ArrayList<List<Short>>();
	stateInf=state; 
    }

    /** Unification algorithm - returns a new State if unification
	possible, null otherwise */
    State unify(Axiom testAxiom, State currentState, boolean proofInfoFlag) {
	short cr, cs, substVar;
	State newState;
	List<Short> substForm, axiomHyp, stateHyp;

	substVec = new ArrayList<Substitution>();
	int currentStateStackSize = currentState.assertionVec.size();
	if (testAxiom == null) return null; // To allow for sloppy axiom array
	int axiomHypSize = testAxiom.axiomHypothesisVec.size();

	// See if stack has enough entries
	if (currentStateStackSize < axiomHypSize) return null;

	// Build state hypothesis ArrayList
	stateHypVec = new ArrayList<List<Short>>();
	for (int hyp = 0; hyp < axiomHypSize; hyp++) stateHypVec.add(currentState.assertionVec.get(currentStateStackSize - axiomHypSize + hyp));

	// Don't destroy caller's distinctVarSet
	Set<DVPair> newDistinctVarSet = new HashSet<DVPair>(currentState.distinctVarSet);

	newMaxVar = currentState.maxVar;

	// Build axiom hypothesis List with renumbered variables
	axiomHypVec = new ArrayList<List<Short>>();
	for (int hyp = 0; hyp < axiomHypSize; hyp++) axiomHypVec.add(renumberVars(currentState.maxVar,testAxiom.axiomHypothesisVec.get(hyp)));

	// Renumber distinct variables of axiom and add to dist var ArrayList
	for (DVPair dv : testAxiom.axiomDistVarSet) newDistinctVarSet.add(renumberVars(currentState.maxVar,dv));

	// Unify each hypothesis
	for (int hyp = 0; hyp < axiomHypSize; hyp++) {
	    for (int i = 0; i < axiomHypVec.get(hyp).size() && i < stateHypVec.get(hyp).size(); i++) {
		// Assign working hypotheses strings; also reassign them each
		// pass thru loop to reflect result of substitution at end of loop
		axiomHyp = axiomHypVec.get(hyp);
		stateHyp = stateHypVec.get(hyp);
		cr = axiomHyp.get(i);
		cs = stateHyp.get(i);
		if (cr == cs) continue;
		if (cr > 0) { // Variable in axiom
		    substForm = PrimFormula.pformula(stateHyp, i); // Get subformula
		    substVar = cr;
		} else if (cs > 0) { // Variable in state hyp
		    substForm = PrimFormula.pformula(axiomHyp, i); // Get subformula
		    substVar = cs;
		} else return null; // Unif not possible - connectives mismatch
		if (substForm.indexOf(substVar) >= 0) return null; // Unif not possible - substituted var in substitution
		Substitution subst = new Substitution(substVar, substForm);
		try { newDistinctVarSet=rebuildDistinct(subst, newDistinctVarSet); }
		catch(DVViolation e) { return null; }
		makeSub(subst); // Make subst to hyp's and substVec
		substVec.add(subst);
	    }
	    if (axiomHypVec.get(hyp).size() != stateHypVec.get(hyp).size()) return null; // Unif not possible
	}

	// Build new State to return to caller
	newState = new State(stateInf);
	// Build new assertion stack
	newState.assertionVec = new ArrayList<List<Short>>();

	if (proofInfoFlag) {
	    // Don't discard used-up assertions in this mode, but put them
	    // at the bottom of the stack so they'll be available for the detailed
	    // proof
	    for (int i = currentStateStackSize - axiomHypSize; i < currentStateStackSize; i++)
		newState.pushAssertion(Substitution.makeVecSubst(currentState.assertionVec.get(i), substVec), currentState.proofVec.get(i));
	}

	// Copy assertions and their proofs that were not popped by unification
	for (int i = 0; i < currentStateStackSize - axiomHypSize; i++)
	    newState.pushAssertion(Substitution.makeVecSubst(currentState.assertionVec.get(i), substVec), currentState.proofVec.get(i));
	// Build proof for new assertion
	String newProof = proofInfoFlag ? String.valueOf(currentStateStackSize+1) + " " + testAxiom.label : testAxiom.label;
	if (proofInfoFlag)
	    // Format is step#, axiom used, steps used by hypotheses of axiom
	    for (int i = currentStateStackSize - 1; i >= currentStateStackSize - axiomHypSize; i--)
		newProof += "," + currentState.proofVec.get(i).substring(0, currentState.proofVec.get(i).indexOf(' '));
	else 
	    // Format is axiom used, preceded by concatenated proofs of hypotheses
	    for (int i = currentStateStackSize - 1; i >= currentStateStackSize - axiomHypSize; i--) 
		newProof = currentState.proofVec.get(i) + " " + newProof;
	// Push new, substituted assertion and proof from result of axiom
	newState.pushAssertion(Substitution.makeVecSubst(renumberVars(currentState.maxVar,testAxiom.assertion), substVec), newProof);
	// Copy hypotheses with substitutions made to them
	for (List<Short> hp : currentState.hypothesisVec)
	    newState.hypothesisVec.add(Substitution.makeVecSubst(hp, substVec));
	// Assign distinct variable list
	newState.distinctVarSet = newDistinctVarSet;
	// Assign largest variable
	newState.maxVar = newMaxVar;
	newState.normalize();
	return newState;
    }


    State unify(String lbl, State curState, boolean pInf) { return unify(stateInf.getAx(lbl), curState, pInf); }
    
    /** Renumber variables in a formula from a axiom, by adding axiom's var #
	(which must be > 0) to oldMaxVar */
    List<Short> renumberVars(short oldMaxVar, List<Short> axiomFormula) {
	List<Short> formulaBuf = new ArrayList<Short>(axiomFormula);
	// Renumber variables
	for (int i = 0; i < formulaBuf.size(); i++) {
	    if (formulaBuf.get(i) > 0) {
		short newVar = (short)(oldMaxVar + formulaBuf.get(i));
		formulaBuf.set(i, newVar);
		if (newVar > newMaxVar) newMaxVar = newVar;
	    }
	}
	return formulaBuf;
    }

    DVPair renumberVars(short oldMaxVar, DVPair dVC) {
	if(dVC.first+oldMaxVar> newMaxVar) newMaxVar=(short)(dVC.first+oldMaxVar);
	try { return new DVPair((short)(dVC.first+oldMaxVar), (short)(dVC.second+oldMaxVar)); }
	catch(DVViolation e) { return null; }
    }


    /** Make substitution to hyp's and substVec (substVec is theoretically
	not necessary but done to speed things up) */
    void makeSub(Substitution subst) {
	for (int hyp = 0; hyp < stateHypVec.size(); hyp++) {
	    stateHypVec.set(hyp, subst.makeSubst(stateHypVec.get(hyp)));
	    axiomHypVec.set(hyp, subst.makeSubst(axiomHypVec.get(hyp)));
	}
	for (Substitution sub : substVec) sub.substVec = subst.makeSubst(sub.substVec);
    }
    
    /** Rebuild newDistinctVarSet after a substitution */
    Set<DVPair> rebuildDistinct(Substitution subst, Set<DVPair> newDistinctVarSet) throws DVViolation {
	Set<DVPair> newDVS=new HashSet<DVPair>();

	for (DVPair dVC : newDistinctVarSet)
	    if (dVC.hasVar(subst.substVar))
		for (int i=0; i<subst.substVec.size(); i++)
		    if (subst.substVec.get(i) >= 0) newDVS.add(dVC.subst(subst.substVar, subst.substVec.get(i)));
	    else newDVS.add(dVC);
	return newDVS;
    } // rebuildDistinct
}
