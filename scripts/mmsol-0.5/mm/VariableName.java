// Get name for display of variable
package mm;

import java.util.*;

final class VariableName {
    private static Map<Short,String> varNameMap = new HashMap<Short,String>();
    private static Map<String, Short> revVarNameMap = new HashMap<String,Short>();
    private static Map<Short,Short> varTypeMap = new HashMap<Short,Short>();
    static final String[][] VAR_NAMES = {{"P","Q","R","S","T","U","W","X","Y","Z"}, 
					 {"x","y","z","w","v","u","t","s","r","q","p","n","m","l","k","j","i","h","g","f","d","c","b","a"}, 
					 {"A","B","C","D","F","G","H","J","K","L","M","N"}, 
					 {"e"}};
    static int[] varSoFar = new int[4]; // Counter for how many so far for
    // each type

    // Initialize (e.g. after renormalizing variables)
    final static void init() {
	varNameMap = new HashMap<Short,String>();
	revVarNameMap = new HashMap<String,Short>();
	varTypeMap = new HashMap<Short,Short>();
	varSoFar = new int[4]; // Initialized to 0; there are 4 types
    }


    // Set name based on type and previous names
    private static void setName(short var, short type) {
	if(!varNameMap.containsKey(var)) {
	    int v = varSoFar[type]++;
	    int quotient = v / VAR_NAMES[type].length;
	    int remainder = v % VAR_NAMES[type].length;
	    String suffix = quotient==0 ? suffix = "" : String.valueOf(quotient-1);
	    varNameMap.put(var,VAR_NAMES[type][remainder]+suffix);
	    revVarNameMap.put(varNameMap.get(var), var);
	    varTypeMap.put(var,type);
	}
    }

    // Get name of variable - type must be 0 thru 3 (wff thru digit)
    final static String name(short var, short type) {
	setName(var,type); 
	return varNameMap.get(var);
    }

    // This is a handy way to find out variable's type, but should only
    // be used after getting the variable's name
    final static short type(short var) { return varTypeMap.get(var); }
    final static short type(String var) {
	if(revVarNameMap.containsKey(var)) { return type(revVarNameMap.get(var)); }
	return (short)(-1);
    }

} 
