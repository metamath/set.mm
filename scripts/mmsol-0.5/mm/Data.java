package mm;
import java.util.*;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStreamReader;


public class Data {
    private ClassLoader loader;

    // Connective storage
    private Map<String,Short> connectiveMap; // For speedup
    
    // Axiom storage
    static final int FAMILIES = 15;

    private String[] familyName;
    private Map<String,Integer> revFamilyName;

    private String[] axFiles = {"propcalc.txt", "propdefs.txt",	"predcalc.txt",	"preddefs.txt",	"settheory.txt", "setdefs.txt",	"impl.txt", "ipc.txt",
				"modal.txt", "godel.txt", "quantum.txt", "euclid.txt", "weakd.txt", "meredith.txt", "curmm.txt" };

    @SuppressWarnings("unchecked")
	private List<String>[] extraInfo = new List[FAMILIES];

    @SuppressWarnings("unchecked")
	private SortedMap<String,Axiom>[] axiomFamily = new SortedMap[FAMILIES]; 


    private Map<String,String> tokenMap;

    static final private String CONNECTIVES_FILE="connectives.txt";
    static final private String TOKENS_FILE="tokens.txt";

    private int currentFamily; // Current family
    private SortedMap<String,Axiom> axioms; // Current axiom set
    private SortedMap<String,Axiom> userTheorems; 

    // Type parameters
    static final int NUM_TYPES = 4;
    static final String[] TYPE_NAMES = new String[]{"wff", "var", "class", "digit"};

    private boolean[][] typesUsed = new boolean[FAMILIES][NUM_TYPES];

    private Connective[] connectiveArr;

    /* Do preprocessing on the input. Returns the first line that
     * is non-empty after removing comments and excess whitespace.
     * Returns null for EOF.
     */
    private String nextLine(BufferedReader in) throws IOException {
	String res="";
	while(res.equals("")) {
	    if((res=in.readLine())==null) return null;
	    res=res.replaceAll("#.*","").trim(); 
	}
	return res;
    }
  
    /* Read in connectives from connectives.txt. The format of the
     * file is as follows: each line contains
     * four whitespace-seperated elements, viz: the connective's
     * name, its type, the number of arguments it takes, and its printname.
     * The next line after that contains the types of each argument.
     */
    private void readConnectives() throws IOException {
	List<Connective> res=new ArrayList<Connective>();
	BufferedReader in=new BufferedReader(new InputStreamReader(loader.getResourceAsStream(CONNECTIVES_FILE)));
	short connCount=0;

	for(String curConn=nextLine(in); curConn!=null; curConn=nextLine(in), connCount++) {
	    String[] args=curConn.split("\\s+",4);
	    String name=args[0], type=args[1], pname=args[3];
	    int nargs=Integer.parseInt(args[2]);
	    Connective tmp=new Connective(this,name,type,nargs,pname);
	    if(nargs!=0) {
		String[] atyps=nextLine(in).split("\\s+");
		for(int i=0; i<atyps.length; i++) tmp.setArgtype(i,atyps[i]);
	    }
	    connectiveMap.put(name, connCount);
	    res.add(tmp);
	}
	  
	in.close();
	connectiveArr=PrimFormula.connectiveArr=res.toArray(new Connective[res.size()]);
    }
  
    // Read in axioms from the given file.
    private void readAxioms(int fam) throws IOException, DVViolation {
	axiomFamily[fam]=new TreeMap<String,Axiom>();
	extraInfo[fam]=new ArrayList<String>();
	typesUsed[fam]=new boolean[NUM_TYPES];
	BufferedReader in=new BufferedReader(new InputStreamReader(loader.getResourceAsStream(axFiles[fam])));
	  
	for(String line=nextLine(in); line!=null; line=nextLine(in)) {
	    String[] args=line.split("\\s+",2);

	    if(args[0].equals("info")) extraInfo[fam].add(args.length==1 ? "" : args[1]);
	    else if(args[0].equals("title")) {
		familyName[fam]=args[1]; 
		revFamilyName.put(args[1],fam);
	    }
	    else if(args[0].equals("usestype")) for(String typ : args[1].split("\\s+")) typesUsed[fam][getExprType(typ)] = true;
	    else if(args[0].equals("hyp")) {
		args=args[1].split("\\s+", 2);
		axiomFamily[fam].get(args[0]).addHyp(args[1]);
	    }
	    else if(args[0].equals("dv")) {
		args=args[1].split("\\s+", 2);
		axiomFamily[fam].get(args[0]).addDistinct(args[1]);
	    }
	    else {
		String name=args[0];
		String descr=nextLine(in);
		String assertion=args[1];
		Axiom tmp=new Axiom(this,name,assertion,descr);
		axiomFamily[fam].put(name,tmp);
	    }
	}	  
	in.close();
    }

    private void readTokens() throws IOException {
	BufferedReader in=new BufferedReader(new InputStreamReader(loader.getResourceAsStream(TOKENS_FILE)));

	for(String curLine=nextLine(in); curLine!=null; curLine=nextLine(in)) {
	    String[] args=curLine.split("\\s+",2);
	    tokenMap.put(args[0],args[1]);
	}
    }

    public Data() {
	loader = ClassLoader.getSystemClassLoader();
	userTheorems = new TreeMap<String,Axiom>();
	currentFamily = 0;
	connectiveMap = new HashMap<String,Short>();
	tokenMap = new HashMap<String,String>();
	familyName = new String[FAMILIES];
	revFamilyName = new HashMap<String,Integer>();

	try { 
	    readConnectives();
	    for(int i=0; i<FAMILIES; i++) readAxioms(i); 
	    readTokens();
	}
	catch(IOException e) { }
	catch(DVViolation e) { }

	resetAxioms();

    } 

    public String getCurFam() { return familyName[currentFamily]; }
    public Axiom getAx(String name) { return axioms.get(name); }
    public void setAxioms(SortedMap<String,Axiom> a) { axioms=a; }
    public SortedMap<String,Axiom> getAxioms() { return axioms; }

    public void addThm(Axiom th) { userTheorems.put(th.label, th); }
    public SortedMap<String,Axiom> getThms() { return userTheorems; }
    public int numThms() { return userTheorems.size(); }
    public void clearThms() { setThms(new TreeMap<String,Axiom>()); }
    public void setThms(SortedMap<String,Axiom> t) { userTheorems=t; }

    public void setFamily(int fam) { currentFamily=fam; }
    public int getFamily() { return currentFamily; }

    public String getFamName(int i) { return familyName[i]; }
    public String[] getFamNames() { return familyName; }
    public int getFamNum(String name) { return revFamilyName.get(name); }

    public boolean hasConnective(String tok) { return connectiveMap.containsKey(tok); }
    public short getConnecitve(String tok) { return connectiveMap.get(tok); }

    public String getToken(String t) { return tokenMap.containsKey(t) ? tokenMap.get(t) : t; }
    
    /** Builds the axioms map based on the chosen logic familiy
	and adds to it all user theorems that are valid in that
	logic family */
    public final void resetAxioms(int logicFamily) {
	axioms = new TreeMap<String,Axiom>(axiomFamily[logicFamily]);
	for (Axiom userTh : userTheorems.values()) {
	    boolean validProof = true;
	    for (String label : userTh.proof.split("\\s+")) {
		if (!axioms.containsKey(label) && label.charAt(1) != '$') {
		    validProof = false;
		    break;
		}
	    }
	    if (validProof) axioms.put(userTh.label, userTh);
	}
    }

    public final void resetAxioms() { resetAxioms(currentFamily); }

    public List<String> getInfo(int fam) { return extraInfo[fam]; }
    public List<String> getInfo() { return getInfo(currentFamily); }

    public boolean usesType(int fam, int typ) { return typesUsed[fam][typ]; }
    public boolean usesType(int typ) { return usesType(currentFamily,typ); }

    public Connective getConn(int i) { return connectiveArr[i]; }


    // Get expression type number for input string; return -1 if bad
    public short getExprType(String stype) {
	for (short i = 0; i < TYPE_NAMES.length; i++)
	    if (TYPE_NAMES[i].equals(stype)) return i;
	return (short)(-1);
    }
}
