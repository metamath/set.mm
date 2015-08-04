// Define a logical connective
package mm;

class Connective {
    String label, notation;
    short type;
    short[] argtypes;
    int numArgs;
    Data stateInf;

    Connective(Data stateInf, String label, String wtype, int numArgs, String notation) {
	this.stateInf = stateInf;
	this.label = label;
	this.type = stateInf.getExprType(wtype);
	this.argtypes = new short[numArgs];
	this.numArgs = numArgs;
	this.notation = notation;
    }
    void setArgtype(int arg, String sarg) { this.argtypes[arg] = stateInf.getExprType(sarg); }

} 
