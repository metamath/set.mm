// mm.java Copyright (c) 2003 Norman Megill nm at alum dot mit dot edu

// Copyright under terms of GNU General Public License

package mm;

import java.awt.*;
import java.util.*;
import java.util.List;

import java.awt.event.ActionListener;
import java.awt.event.ActionEvent;

import java.awt.event.ItemListener;
import java.awt.event.ItemEvent;

import javax.swing.*;

public class mm extends JPanel {

    private boolean proofInfoModeFlag = false, axiomInfoModeFlag = false;
    private String infoModeAxiomToShow;

    private TextArea proofText;

    private JMenuBar menubar;
    private JMenu optionsMenu, axiomMenu;
    private JMenuItem proofExitItem, infoExitItem, undoItem, rotateItem, swapItem, deleteItem, eraseItem, infoItem, proofItem, selectItem, hypItem, saveItem, exitItem;

    private State currentState; // Current state of stack
    private Stack<State> undoStack;

    static final Color BACKGROUND_COLOR = new Color(210, 255, 255);
    static final Color PROOF_BACKGROUND_COLOR = new Color(255, 255, 165);
    static final Color INFO_BACKGROUND_COLOR = new Color(255, 210, 255);

    // Font parameters
    static final int FONT_SIZE = 12;
    static final Font MATH_FONT = new Font("TimesNewRoman", Font.PLAIN, FONT_SIZE);
    static final int Y_INCREMENT = (FONT_SIZE * 3) / 2; // Line-to-line spacing
    static final int X_INIT = FONT_SIZE / 2; // Left margin
    static final int CHAR_SPACE = -1; // Space between chars of token
    static final int WHITE_SPACE = 2; // Space between tokens

    static final Color[] TYPE_COLORS = new Color[]{Color.blue, Color.red, Color.magenta, Color.green};

    static final String TITLE="Metamath Solitaire (C) 2003 (GPL) Norman Megill nm" + "@" + "alum.mit.edu";

    private int currentX, currentY;
    private Graphics g;
    private FontMetrics fm;

    private Data stateInf;
    private Unification unifier;

    public mm() {
	stateInf = new Data();
	undoStack = new Stack<State>();
	currentState = new State(stateInf);
	unifier = new Unification(stateInf);
	menubar = new JMenuBar();
	optionsMenu = new JMenu("Options");
	axiomMenu = new JMenu("Axioms");

	menubar.add(optionsMenu);
	menubar.add(axiomMenu);

	setBackground(BACKGROUND_COLOR);
    	setupItems();
	buildChoices();
    } 

    private void setupItems() {
	infoExitItem = new JMenuItem("Exit Axiom Information");
	infoExitItem.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent e) {
		    setBackground(BACKGROUND_COLOR);
		    axiomInfoModeFlag = false;
		    rebuildScreen();}});

	proofExitItem = new JMenuItem("Hide Proof Information");
	proofExitItem.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent e) {
		    mm.this.remove(proofText);
		    proofInfoModeFlag = false;
		    rebuildScreen();}});	

	undoItem = new JMenuItem("Undo");
	undoItem.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent a) {
		    currentState = undoStack.pop();
		    stateInf.setThms(currentState.userThms);
		    stateInf.setFamily(currentState.currentFam);
		    stateInf.resetAxioms();
		    rebuildScreen();}});

	rotateItem = new JMenuItem("Rotate Stack");
	rotateItem.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent a) {
		    pushUndo();
		    stackRot(0);
		    rebuildScreen();}});

	swapItem = new JMenuItem("Swap Stack Top");
	swapItem.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent a) {
		    pushUndo();
		    stackRot(currentState.assertionVec.size()-2);
		    rebuildScreen();}});

	deleteItem = new JMenuItem("Delete Stack Top");
	deleteItem.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent a) {
		    pushUndo();
		    currentState.assertionVec.remove(currentState.assertionVec.size() - 1);
		    currentState.proofVec.remove(currentState.proofVec.size() - 1);
		    currentState.normalize();
		    rebuildScreen();}});

	eraseItem = new JMenuItem("Erase Stack");
	eraseItem.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent a) {
		    pushUndo();
		    currentState = new State(stateInf);
		    rebuildScreen();}});

	proofItem = new JMenuItem("Proof Information");
	proofItem.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent a) {
		    proofInfoModeFlag = true;
		    rebuildScreen();}});

	infoItem = new JMenuItem("Axiom Information");
	infoItem.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent a) {
		    axiomInfoModeFlag = true;
		    infoModeAxiomToShow = ""; 
		    setBackground(INFO_BACKGROUND_COLOR);    
		    rebuildScreen();}});

	selectItem = new JMenuItem("Select Logic Family");
	selectItem.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent a) {
		    String s = (String)JOptionPane.showInputDialog(null,"Select a logic family:","Logic Selection",JOptionPane.PLAIN_MESSAGE,null,stateInf.getFamNames(), 
								   stateInf.getFamName(0));
		    if(s!=null && s.length()>0) {
			int i=stateInf.getFamNum(s);
			if (stateInf.getFamily() != i) {
			    pushUndo();
			    stateInf.setFamily(i);
			    stateInf.resetAxioms();
			    currentState = new State(stateInf);
			}
		    }
		    rebuildScreen();}});

	hypItem = new JMenuItem("Add Hypothesis");
	hypItem.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent a) {
		    pushUndo();
		    currentState.addHyp();
		    rebuildScreen();}});

	rotateItem = new JMenuItem("Rotate Stack");
	rotateItem.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent a) {
		    pushUndo();
		    stackRot(0);
		    rebuildScreen();}});

	saveItem = new JMenuItem("Save As Axiom");
	saveItem.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent a) {
		    stateInf.addThm(new Axiom(stateInf, currentState));
		    currentState.userThms = stateInf.getThms();
		    stateInf.resetAxioms();
		    rebuildScreen();}});

	exitItem = new JMenuItem("Exit");
	exitItem.addActionListener(new ActionListener() { public void actionPerformed(ActionEvent a) { System.exit(0); }});
    }
		
    
    private void stackRot(int iStart) {
	int iEnd = currentState.assertionVec.size() - 1;
	List<Short> tmpStr = currentState.assertionVec.get(iStart);
	String tmpPStr = currentState.proofVec.get(iStart);
	for (int i = iStart; i < iEnd; i++) {
	    currentState.assertionVec.set(i,currentState.assertionVec.get(i + 1));
	    currentState.proofVec.set(i,currentState.proofVec.get(i + 1));
	}
	currentState.assertionVec.set(iEnd, tmpStr);
	currentState.proofVec.set(iEnd, tmpPStr);
    }

    private void pushUndo() { undoStack.push(new State(currentState)); }

    private void buildChoices() {
	setupItems();
	buildOptionChoices();
	buildAxiomChoices();
    }
    
    
    // Build list of choices from axiom menu
    private void buildOptionChoices() {
	optionsMenu.removeAll();
	if (proofInfoModeFlag) optionsMenu.add(proofExitItem);
	else if (axiomInfoModeFlag) optionsMenu.add(infoExitItem);
	else {
	    if (!undoStack.empty()) optionsMenu.add(undoItem);
	    if (currentState.assertionVec.size() > 1) {
		optionsMenu.add(swapItem);
		optionsMenu.add(rotateItem);
	    }
	    if (!currentState.assertionVec.isEmpty()) optionsMenu.add(deleteItem);
	    if (!(currentState.assertionVec.isEmpty() && currentState.hypothesisVec.isEmpty())) optionsMenu.add(eraseItem);
	    if (!currentState.assertionVec.isEmpty()) optionsMenu.add(proofItem);
	    optionsMenu.add(infoItem);
	    optionsMenu.add(hypItem);
	    optionsMenu.add(selectItem);
	    if (!(currentState == null || currentState.assertionVec.isEmpty())) optionsMenu.add(saveItem);
	}

	optionsMenu.addSeparator();
	optionsMenu.add(exitItem);
    } 

    // Build list of choices from axiom menu
    void buildAxiomChoices() {
	axiomMenu.removeAll();
	if (proofInfoModeFlag) return; // Disable selection in proof display mode

	String menuString = "";
	    
	if (!currentState.hypothesisVec.isEmpty()) {
	    // If there are hypotheses, do a dummy run-thru of assertions and hypotheses to get desired variable names for axiom choice menu
	    VariableName.init();
	    for (int i = currentState.assertionVec.size() - 1; i >= 0; i--) PrimFormula.getDisplay(currentState.assertionVec.get(i));
	    for (int i = currentState.hypothesisVec.size() - 1; i >= 0; i--) PrimFormula.getDisplay(currentState.hypothesisVec.get(i));
	}

	// Put any user hypotheses first. Variable names have not been reinitialized here; we want to use the names in the currentState display for best user info
	if (!axiomInfoModeFlag)
	    for (int i = 0; i < currentState.hypothesisVec.size(); i++)
		axiomMenu.add("1 $hyp " + (i+1) + " " + PrimFormula.getDisplay(currentState.hypothesisVec.get(i))).addActionListener(new AxiomListener(i));

	// For each axiom, if it unifies with the state stack, add it in
	// Note: in info mode we show *all* axioms in their natural order, whether
	// or not they unify
	for (Axiom ax : stateInf.getAxioms().values()) {
	    int hyps = ax.axiomHypothesisVec.size();
	    if (hyps == 0) menuString = ax.menuEntry; // use pre-computed entry for speed
	    else {
		State dummyState = unifier.unify(ax, currentState, false);
		if (dummyState == null) continue; // Unification not possible
		VariableName.init(); // Initialize so types don't get mixed up
		// Show how much stack will grow, name of axiom, & the top of the
		// stack that would result
		menuString = String.valueOf(1 - hyps) + " " + ax.label + " " + PrimFormula.getDisplay(dummyState.getStackTop());
	    }
	    axiomMenu.add(menuString).addActionListener(new AxiomListener(ax.label));
	} 
    }

    private class AxiomListener implements ActionListener {
	String choice;
	int hypN;
	boolean isHyp;
	AxiomListener(String c) { choice=c; isHyp=false; }
	AxiomListener(int n) { hypN=n; isHyp=true; }
	public void actionPerformed(ActionEvent e) {
	    if (axiomInfoModeFlag) infoModeAxiomToShow = choice;
	    else {
		if (isHyp) {
		    pushUndo();
		    currentState.pushAssertion(currentState.hypothesisVec.get(hypN), choice);
		} else {
		    undoStack.push(currentState);
		    // It's a axiom - it will always unify since that was determined
		    // when choice list was built
		    currentState = unifier.unify(stateInf.getAx(choice), currentState, false);
		}
	    } 
	    rebuildScreen();
	}
    };

    private void drawToken(String token, short type) {
	g.setColor(type==-1 ? Color.black : TYPE_COLORS[type]);
	g.drawString(token, currentX, currentY);
	currentX += fm.stringWidth(token) + WHITE_SPACE;

    }

    private void drawFormula(List<Short> formula) {
	fm = g.getFontMetrics();
	currentX = X_INIT;
	currentY += Y_INCREMENT;

	for (String token : PrimFormula.getDisplay(formula).split("\\s+")) drawToken(stateInf.getToken(token), VariableName.type(token)); 
    }

    // Draw the distinct variable pair list
    private void drawDistinct(Set<DVPair> distinctVarSet) {
	int cnt = 0;

	fm = g.getFontMetrics();
	currentX = X_INIT;

	for (DVPair dVC : distinctVarSet) {
	    // We assume type is already assigned, so 0 is OK */
	    drawToken(VariableName.name(dVC.first, (short)0), VariableName.type(dVC.first));
	    currentX += 4;
	    drawToken(VariableName.name(dVC.second, (short)0), VariableName.type(dVC.second));
	    currentX += 24;
	    // New line every 10 pairs
	    if (++cnt == 10) {
		currentX = X_INIT;
		currentY += Y_INCREMENT;
		cnt=0;
	    }
	}
    }

    public void paint(Graphics g) {
	String token;
	this.g=g;

	// validate makes an added Component show up in the display (not documented in Java spec?)
	validate();

	VariableName.init(); // Initialize so types don't get mixed up

	// Clear screen
	Rectangle r = getBounds();
	g.setColor(getBackground());
	g.fillRect(r.x, r.y, r.width, r.height);

	currentX = X_INIT;
	currentY = menubar.getHeight() + Y_INCREMENT/2;

	// Display type colors
	g.setFont(new Font("Dialog", Font.PLAIN, FONT_SIZE));
	g.setColor(Color.black);

	g.setFont(new Font("Dialog", Font.BOLD, FONT_SIZE));
	token = stateInf.getCurFam();
	g.drawString(token, X_INIT, currentY);
	fm = g.getFontMetrics();
	currentX += fm.stringWidth(token) + 2 * FONT_SIZE;
	g.setFont(new Font("Dialog", Font.PLAIN, FONT_SIZE));

	if (axiomInfoModeFlag && infoModeAxiomToShow.equals("")) {
	    currentY += 2 * Y_INCREMENT;
	    // User has not selected an axiom yet
	    token = "To see information about an axiom, choose it from the Axioms menu.";
	    g.drawString(token, X_INIT, currentY);
	    return;
	}
	if (!axiomInfoModeFlag && currentState.assertionVec.isEmpty() && currentState.hypothesisVec.isEmpty()) {
	    // There is nothing to display yet.  Just after startup or erase.
	    currentY += Y_INCREMENT;
	    g.drawString("The Axioms menu shows how much the stack will grow, the axiom name,", X_INIT, currentY+=Y_INCREMENT);
	    g.drawString("and as much of the axiom as can be displayed.", X_INIT, currentY+=Y_INCREMENT);  
	    g.drawString("Select repeatedly from the Axioms menu.  The stack will grow and shrink", X_INIT, currentY+=2*Y_INCREMENT);
	    g.drawString("with theorems.  The goal is to end up with a single stack entry containing", X_INIT, currentY+=Y_INCREMENT);
	    g.drawString("a nice theorem.  You can clip out its proof with 'Proof Information'.", X_INIT, currentY+=Y_INCREMENT); currentY += Y_INCREMENT;
	    for(String line : stateInf.getInfo()) g.drawString(line, X_INIT, currentY+=Y_INCREMENT);
	    currentY+=Y_INCREMENT;
	    return;
	}
	token = "Colors of variable types:";
	g.drawString(token, currentX, currentY);
	fm = g.getFontMetrics();
	currentX += fm.stringWidth(token) + 2 * FONT_SIZE;

	g.setFont(MATH_FONT);
	fm = g.getFontMetrics();

	for (int i = 0; i < Data.NUM_TYPES; i++)
	    if (stateInf.usesType(i)) {
		Color c = TYPE_COLORS[i];
		g.setColor(c); g.drawString(Data.TYPE_NAMES[i], currentX, currentY);
		currentX += fm.stringWidth(Data.TYPE_NAMES[i]) + 2 * FONT_SIZE;
	    }

	// Display stack (or requested axiom in info mode)
	String axOrTh = "axiom";
	if (!currentState.assertionVec.isEmpty() || axiomInfoModeFlag) {
	    currentY += Y_INCREMENT * 3 / 2;
	    g.setFont(new Font("Dialog", Font.PLAIN, FONT_SIZE));
	    g.setColor(Color.black);
	    if (axiomInfoModeFlag) {
		if (!stateInf.getAx(infoModeAxiomToShow).proof.equals("")) axOrTh = "theorem";
		g.setFont(new Font("Dialog", Font.BOLD, FONT_SIZE));
		token = "Information for " + axOrTh + " " + stateInf.getAx(infoModeAxiomToShow).label;
		g.drawString(token, X_INIT, currentY); currentY += Y_INCREMENT;
		g.setFont(new Font("Dialog", Font.PLAIN, FONT_SIZE));
		token = "Description:  " + stateInf.getAx(infoModeAxiomToShow).description;
		g.drawString(token, X_INIT, currentY);
		if (!stateInf.getAx(infoModeAxiomToShow).proof.equals("")) {
		    currentY += Y_INCREMENT;
		    g.drawString("Proof:  " + stateInf.getAx(infoModeAxiomToShow).proof, X_INIT, currentY);
		}
		currentY += Y_INCREMENT * 3 / 2;
		token = "Assertion made by this " + axOrTh + ":";
	    } else
		token = "Assertion stack (each line is " + (currentState.hypothesisVec.isEmpty() ?
							    "a theorem scheme of this logic family):" : "an inference from the hypotheses):");
	    g.drawString(token, X_INIT, currentY);
	    g.setFont(MATH_FONT);
	    VariableName.init(); // Initialize name map so var's will be renumbered
	    if (axiomInfoModeFlag) drawFormula(stateInf.getAx(infoModeAxiomToShow).assertion);
	    else for (int i = currentState.assertionVec.size() - 1; i >= 0; i--) drawFormula(currentState.assertionVec.get(i));
	}

	// Display hypotheses
	if ((!(axiomInfoModeFlag || currentState.hypothesisVec.isEmpty())) || (axiomInfoModeFlag && !stateInf.getAx(infoModeAxiomToShow).axiomHypothesisVec.isEmpty())) {
	    currentY += Y_INCREMENT * 3 / 2;
	    g.setFont(new Font("Dialog", Font.PLAIN, FONT_SIZE));
	    g.setColor(Color.black);
	    g.drawString("Hypotheses for " + (axiomInfoModeFlag ? "this " + axOrTh + ":" : "the assertions in the stack:"), X_INIT, currentY);
	    g.setFont(MATH_FONT);
	    if (axiomInfoModeFlag)
		for (int i = stateInf.getAx(infoModeAxiomToShow).axiomHypothesisVec.size() - 1; i >= 0; i--)
		    drawFormula(stateInf.getAx(infoModeAxiomToShow).axiomHypothesisVec.get(i));
	    else
		for (int i = currentState.hypothesisVec.size() - 1; i >= 0; i--) drawFormula(currentState.hypothesisVec.get(i));
	}

	// Display distinct variable pairs
	if (!(axiomInfoModeFlag || currentState.distinctVarSet.isEmpty()) ||
	    (axiomInfoModeFlag && !(stateInf.getAx(infoModeAxiomToShow).axiomDistVarSet.isEmpty()))) {
	    currentY += Y_INCREMENT + Y_INCREMENT / 2;
	    g.setFont(new Font("Dialog", Font.PLAIN, FONT_SIZE));
	    g.setColor(Color.black);
	    g.drawString("Substitutions for these variable pairs may not have variables in",
			 X_INIT, currentY);
	    currentY += Y_INCREMENT;
	    if (axiomInfoModeFlag) token = "common for an instance of the " + axOrTh + " to remain valid:";
	    else token = "common for the assertions to remain valid:";
	    g.drawString(token, X_INIT, currentY);
	    g.setFont(MATH_FONT);
	    currentY += Y_INCREMENT;

	    Set<DVPair> dVarSet=axiomInfoModeFlag ? stateInf.getAx(infoModeAxiomToShow).axiomDistVarSet : currentState.distinctVarSet;
	    drawDistinct(dVarSet);
	}
    } // paint

    public void rebuildScreen() {
	buildChoices();
	    
	// If in display proof mode, put proof after choice
	if (proofInfoModeFlag) {
	    proofText = new TextArea("The top stack entry is:\n\n    " + PrimFormula.getDisplay(currentState.assertionVec.get(currentState.assertionVec.size()-1)) +
				     "\n\nTo reconstruct the top stack entry, enter axioms in this order:\n\n    " + 
				     currentState.proofVec.get(currentState.proofVec.size()-1), 20, 65, TextArea.SCROLLBARS_VERTICAL_ONLY);
	    proofText.setBackground(PROOF_BACKGROUND_COLOR);
	    proofText.setEditable(false);
		
	    // Display fleshed-out proof detail
	    proofText.append("\n\nDetailed proof:\n\n");
	    State proofInfoState = currentState.buildProofInfoState();
	    for (int i = 0; i < proofInfoState.assertionVec.size(); i++)
		proofText.append(" " + proofInfoState.proofVec.get(i) + "    " + PrimFormula.getDisplay(proofInfoState.assertionVec.get(i)) + "\n");
	    if (!proofInfoState.distinctVarSet.isEmpty()) {
		proofText.append("\nDistinct variable pairs for this proof:\n\n");
		for (DVPair dVP : proofInfoState.distinctVarSet) proofText.append("   "+VariableName.name(dVP.first,(short)0)+" "+VariableName.name(dVP.second,(short)0)+" ");
	    }
		
	    add(proofText);
	}
	paint(getGraphics());
    }

    public void createGUI() {
	final JFrame frame=new JFrame(TITLE);
	frame.setDefaultCloseOperation(JFrame.DISPOSE_ON_CLOSE);
	frame.setSize(600, 400);
	frame.setJMenuBar(menubar);
	frame.add(this);
	frame.setJMenuBar(menubar);
	frame.validate();
	frame.setVisible(true);
    }

    public static void main(String[] args) {
	SwingUtilities.invokeLater(new Runnable() { public void run() { new mm().createGUI(); } });
    }	

} // class mm
