package il.ac.bgu.cs.fvm.impl;

import static il.ac.bgu.cs.fvm.util.CollectionHelper.set;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.examples.PetersonProgramGraphBuilder;
import il.ac.bgu.cs.fvm.programgraph.ActionDef;
import il.ac.bgu.cs.fvm.programgraph.ConditionDef;
import il.ac.bgu.cs.fvm.programgraph.ParserBasedActDef;
import il.ac.bgu.cs.fvm.programgraph.ParserBasedCondDef;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;
import il.ac.bgu.cs.fvm.util.Util;
import il.ac.bgu.cs.fvm.verification.VerificationResult;
import il.ac.bgu.cs.fvm.verification.VerificationSucceeded;


import java.util.*;

public class MutualExclusionDemo {

    private static final Set<String> labels = set("crit1", "crit2", "wait1", "wait2");
    private static int stageNum = 0;
    private static int subStageNum = 0;


    public static void main(String[] args) {
        FvmFacadeImpl fvm = new FvmFacadeImpl();


        printStage("Create the program graphs for peterson's algorithm");

        ProgramGraph<String, String> pg1 = PetersonProgramGraphBuilder.build(1);
        ProgramGraph<String, String> pg2 = PetersonProgramGraphBuilder.build(2);

        printStage("Interleave both program graphs into one.");
        ProgramGraph<Pair<String, String>, String> pg = fvm.interleave(pg1, pg2);

        Set<ActionDef> ad = set(new ParserBasedActDef());
        Set<ConditionDef> cd = set(new ParserBasedCondDef());

        printStage("Create a transition system from the program graph.");
        TransitionSystem<Pair<Pair<String, String>, Map<String, Object>>, String, String> ts = fvm.transitionSystemFromProgramGraph(pg, ad, cd);


        printStage("Remove all unnecessary atomic propositions from the transition system, in order to be able to check the properties."
                + "\nThe remaining labels should be: " + String.join(", ",labels) + ".\n");
        for (Pair<Pair<String, String>, Map<String, Object>> state: ts.getStates()) {
            for (String ap : ts.getAtomicPropositions()) ts.removeLabel(state, ap);
        }
        Set<String> aps = new HashSet<>(ts.getAtomicPropositions());
        for(String ap : aps) ts.removeAtomicProposition(ap);
        for(String l: set("wait1", "wait2", "crit1", "crit2", "crit1_enabled")) ts.addAtomicPropositions(l);

        for (Pair<Pair<String, String>, Map<String, Object>> state: ts.getStates()) {
            //for(String ap: ts.getAtomicPropositions()) ts.removeLabel(state, ap);
            if (labels.contains(state.getFirst().getFirst()))
                ts.addToLabel(state, state.getFirst().getFirst());
            for(Pair<Pair<String, String>, Map<String, Object>> next: fvm.post(ts, state)){
                if(next.getFirst().getFirst().equals("crit1")){
                    ts.addToLabel(state, "crit1_enabled");
                    break;
                }
            }
        }

        printStage("Create an automaton for each property.One for mutual exclusion and one for starvation.\n"+
                "Each automaton gets to an accepting state and loops infinitely on it only if the property that is checked is not upholded.");

        printStage("Create the automaton that doesn't uphold mutex");
        Automaton<String, String> mutexAut = createNonMutualExclusionAut(ts);

        printStage("Create the automaton that doesn't uphold starvation freedom");
        Automaton<String, String> starAut = createNonStarvationFreedomAut(ts);

        printStage("For each of the properties, product the automaton for that property with the transition system, \n"
                + "Then check if there is a run that concludes in an infinite loop on the accepting state of the automaton.");


        VerificationResult<Pair<Pair<String, String>, Map<String, Object>>> verMutex = fvm.verifyAnOmegaRegularProperty(ts, mutexAut);
        VerificationResult<Pair<Pair<String, String>, Map<String, Object>>> verStarvation = fvm.verifyAnOmegaRegularProperty(ts, starAut);

        printStage("Check the mutual exclusion property:");
        printResult(verMutex);

        printStage("Check the starvation freedom property:");
        printResult(verStarvation);
    }


    private static Automaton<String, String> createNonMutualExclusionAut(
            TransitionSystem<Pair<Pair<String, String>, Map<String, Object>>, String, String> ts) {
        Automaton<String, String> aut = new Automaton<>();
        printSubStage("Create a power set of the atomic propositions of the transition system.\n" +
                "\t\tThese will be the labels for the transitions of the automaton.");
        Set<Set<String>> props = Util.powerSet(ts.getAtomicPropositions());

        printSubStage("Add two states to the automaton:\n" +
                "\t\tq0 - initial state,\n\t\tq1 - accepting state");
        aut.addState("q0");
        aut.addState("q1");
        aut.setInitial("q0");
        aut.setAccepting("q1");

        printSubStage("Add a transition from q0 to itself for all labels that don't contain both crit1 and crit2,\n" +
                "\t\tas the automaton accepts only when both processes are in the critical section");
        printSubStage("Add a transition from q0 to q1 for all other subsets of the atomic propositions,\n" +
                "\t\tas those are all the states of the program where both processes are in the critical section.");
        printSubStage("Add a transition from q1 to itself for all the subsets of the atomic propositions,\n" +
                "\t\tsince after the automaton has transitioned to the accepting state it will remain there.");

        for(Set<String> label: props){
            if(label.contains("crit1") && label.contains("crit2"))
                aut.addTransition("q0",label,"q1");
            else
                aut.addTransition("q0",label,"q0");
            aut.addTransition("q1",label,"q1");
        }
        subStageNum = 0;
        return aut;
    }

    private static Automaton<String, String> createNonStarvationFreedomAut(
            TransitionSystem<Pair<Pair<String, String>, Map<String, Object>>, String, String> ts) {
        Automaton<String, String> aut = new Automaton<>();

        printSubStage("Create a power set of the atomic propositions of the transition system.\n" +
                "\t\tThese will be the symbols for the transitions of the automaton.");
        Set<Set<String>> props = Util.powerSet(ts.getAtomicPropositions());

        printSubStage("Add two states to the automaton:\n" +
                "\t\tq0 - initial state,\n\t\tq1 - accepting state");
        aut.addState("q0");
        aut.addState("q1");
        aut.setInitial("q0");
        aut.setAccepting("q1");

        printSubStage("Add a transition from q0 to itself for all labels");
        printSubStage("Add a transition from q0 to q1 for all labels that contain wait1,\n" +
                "\t\tsince the automaton will accept only when process 1 is stuck and can't enter the critical section.");
        printSubStage("Add a transition from q1 to itself for all the labels where process 1 isn't in the criticl section, to create starvation.");
        for(Set<String> label: props){
            aut.addTransition("q0",label,"q0");
            if(label.contains("wait1"))
                aut.addTransition("q0",label,"q1");
            if(!label.contains("crit1"))
                aut.addTransition("q1",label,"q1");
        }

        subStageNum = 0;
        return aut;
    }

    private static void printStage(String stage){
        stageNum++;
        System.out.println(stageNum + ". " + stage);
    }

    private static void printSubStage(String stage){
        subStageNum++;
        System.out.println("\t" + stageNum + "." + subStageNum + ". " + stage);
    }

    private static void printResult(VerificationResult res){
        if (res instanceof VerificationSucceeded) {
            System.out.println("\tSUCCESS.\n");
        } else {
            System.out.println("\tFAIL.\n");
        }
    }

}
