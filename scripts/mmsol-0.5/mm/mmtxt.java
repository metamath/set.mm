package mm;
import java.util.*;
import java.io.IOException;

import gnu.getopt.Getopt;

public class mmtxt {

    public static void main(String[] args){
	Getopt g=new Getopt("mmtxt", args, "f:p");
	Data state = new Data();
	boolean proofInf=false;
	Unification unifier=new Unification(state);
	
	int c;
	while((c=g.getopt()) != -1) {
	    switch((char)c) {
	    case 'f': 
		state.setFamily(Integer.parseInt(g.getOptarg()));
		state.resetAxioms();
		break;
	    case 'p':
		proofInf=true;
		break;
	    }
	}


	State curState = new State(state);
	for(int i=g.getOptind(); i<args.length; i++) curState = unifier.unify(state.getAx(args[i]), curState, false);
	
	if(proofInf) curState=curState.buildProofInfoState();

	for(int i=0; i<curState.assertionVec.size(); i++) {
	    List<Short> a=curState.assertionVec.get(i);
	    if(proofInf) System.out.print(curState.proofVec.get(i) + " ");
	    System.out.println(PrimFormula.getDisplay(a));
	}
	for(DVPair d : curState.distinctVarSet)
	    System.out.println("$d " + VariableName.name(d.first, (short)0) + " " + VariableName.name(d.second, (short)0));
    }	
    
}
