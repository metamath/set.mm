// Primitive formula handler
package mm;
import java.util.*;

final class PrimFormula {
    static Connective[] connectiveArr;

    // Get shortest primitive formula
    static final List<Short> pformula(List<Short> formula, int start) {
	int end=start;
	for(int lev=1; lev>0; end++, lev--) 
	    if(formula.get(end) < 0) lev+=connectiveArr[-(formula.get(end)+1)].numArgs;
	return new ArrayList<Short>(formula.subList(start,end));
    } // pformula

    // Return variable/connective types
    static final List<Short> getTypes(List<Short> formula, int start) {
	List<Short> typesList=new ArrayList<Short>();
	if (formula.get(start) > 0) typesList.add((short)0);
	else { // It's a connective
	    typesList.add(connectiveArr[-(formula.get(start)+1)].type);
	    for (short argtype : connectiveArr[-(formula.get(start)+1)].argtypes) {
		// Override the type of the first return char (could be
		// a variable with type not yet known)
		List<Short> tmp=getTypes(formula, start+typesList.size());
		tmp.set(0,argtype);
		typesList.addAll(tmp);
	    }
	}
	return typesList;
    } // getTypes

    // Return formula in display notation
    static final String getDisplay(List<Short> formula) { return getDisplay(formula, 0, getTypes(formula, (short)0)); }

    private static final String getDisplay(List<Short> formula, int start, List<Short> typesList) {
	if (formula.get(start) > 0) return VariableName.name(formula.get(start), typesList.get(start));
	else {
	    short connNum = (short)(-(formula.get(start)+1));
	    List<Short> subformula = new ArrayList<Short>(1);
	    subformula.add(formula.get(start));
	    String[] displayArgs = new String[connectiveArr[connNum].numArgs];
	    // Collect the arguments in display notation
	    for (int i = 0; i < connectiveArr[connNum].numArgs; i++) {
		int position = start + subformula.size();
		subformula.addAll(pformula(formula, position));
		displayArgs[i] = getDisplay(formula, position, typesList);
	    }
	    String displayFormula = "";
	    // Replace the arguments in the connectives display notation
	    for (String token : connectiveArr[connNum].notation.split("\\s+")) 
		displayFormula=(displayFormula.equals("") ? "" : displayFormula+" " )+(token.charAt(0)=='$' ? displayArgs[Integer.parseInt(token.substring(1))-1] : token);
	    return displayFormula;
	}
    } // getDisplay

} // class PrimFormula
