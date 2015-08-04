// Define a substitution
package mm;

import java.util.*;

class Substitution {
    short substVar;           // The variable being substituted
    List<Short> substVec;     // What it's substituted with
    Substitution(short substVar, List<Short> substVec) {
	this.substVar = substVar;
	this.substVec = substVec;
    }

    // Makes a substitution into a formula
    final List<Short> makeSubst(List<Short> formula) {
	List<Short> res=new ArrayList<Short>();
	for(short c : formula) {
	    if(c==substVar) res.addAll(substVec);
	    else res.add(c);
	}
	return res;
    }

    // Makes a set of substitutions into a formula
    final static List<Short> makeVecSubst(List<Short> formula, List<Substitution> substVec) {
	for (Substitution sub : substVec) formula = sub.makeSubst(formula);
	return formula;
    }
} 
