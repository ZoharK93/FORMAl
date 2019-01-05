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
import java.util.function.Predicate;

public class MutualExclusionDemo {

    private static final Set<String> labels = set("crit1", "crit2", "wait1", "wait2");
    private static int stageNum = 0;
    private static int subStageNum = 0;

    static final String petreson_proccess1 = "cs_1 := 0; do::true->skip; "
            + "atomic{ b1 := 1; x := 2}; wait_1 := 1; if ::b2==0||x==1 -> skip fi; wait_1 := 0; "
            + "cs_1 := 1; cs_1 := 0; b1 := 0 od";

    static final String petreson_proccess2 = "cs_2 := 0; do::true->skip; "
            + "atomic{ b2 := 1; x := 1}; wait_2 := 1; if ::b1==0||x==2 -> skip fi; wait_2 := 0; "
            + "cs_2 := 1; cs_2 := 0; b2 := 0 od";


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
                "Each automaton gets to an accepting state only if the property that is checked is not upholded.");

        //System.out.println("First we will start with the mutual exclusion property.");
        printStage("Create the automaton that doesn't uphold mutex");
        Automaton<String, String> mutexAut = createNonMutualExclusionAut(ts);

        //System.out.println("Now we will create the second automaton for the starvation freedom property.");
        printStage("Create the automaton that doesn't uphold starvation freedom");
        Automaton<String, String> starAut = createNonStarvationFreedomAut(ts);

        /*Set<String> notUsedLabels = new HashSet<>(ts.getAtomicPropositions());
        notUsedLabels.removeAll(labels);

        ts.getStates().forEach(s -> notUsedLabels.forEach(l -> ts.removeLabel(s, l)));
        notUsedLabels.forEach(ts::removeAtomicProposition);*/

        //Predicate<Pair<Pair<String, String>, ?>> _crit1 = ss -> ss.getFirst().getFirst().equals("crit1");
        //ts.getStates().stream().filter(s -> fvm.post(ts, s).stream().anyMatch(_crit1)).forEach(s -> ts.addToLabel(s, "crit1_enabled"));

        printStage("For each of the properties, product the automaton for that property with the transition system, \n"
                + "Then check if there is a run that concludes in the accepting state of the automaton infinite times.");


        VerificationResult<Pair<Pair<String, String>, Map<String, Object>>> verMutex = fvm.verifyAnOmegaRegularProperty(ts, mutexAut);
        VerificationResult<Pair<Pair<String, String>, Map<String, Object>>> verStarvation = fvm.verifyAnOmegaRegularProperty(ts, starAut);

        printStage("Check the mutual exclusion property:");
        printResult(verMutex);

        printStage("Check the starvation freedom property:");
        printResult(verStarvation);
    }


    private static Automaton<String, String> createNonMutualExclusionAut(
            TransitionSystem<Pair<Pair<String, String>, Map<String, Object>>, String, String> ts) {
        Automaton<String, String> mutexAut = new Automaton<>();
        /*final String NONCRIT = "q0";
        final String CRIT = "q1";

        printSubStage("Create 2 states for the automaton: \n" +
                " q0 which represents the non-critical section and q1 which represents the critical section.\n" +
                " Set q0 to be the initial state, and q1 to be the accepting state");
        mutexAut.addState(NONCRIT);
        mutexAut.addState(CRIT);
        mutexAut.setInitial(NONCRIT);
        mutexAut.setAccepting(CRIT);

        printSubStage("For each atomic proposition, add a transition from each state to itself.");
        for (Set<String> ap : Util.powerSet(labels)) {
            mutexAut.addTransition(NONCRIT, ap, NONCRIT);
            mutexAut.addTransition(CRIT, ap, CRIT);
        }

        printSubStage("Now, if we have a label of {crit1, crit2} in the transition system, "
                        + "then the automaton need to be at " + CRIT + " state. \nSo we will add this transition.");
        mutexAut.addTransition(NONCRIT, set("crit1 = 1","crit2 = 1"), CRIT);

        System.out.println(
                "Our automaton should accept if the transition system get to a state which contains {crit1, crit2}");
        System.out.println("Which means that our accepting state should be " + CRIT + ".\n");
        mutexAut.setAccepting(CRIT);
        subStageNum = 1;*/
        printSubStage("Create a power set of the atomic propositions of the transition system.\n" +
                "\t\tThese will be the symbols for the transitions of the automaton.");
        Set<Set<String>> props = Util.powerSet(ts.getAtomicPropositions());
        /*for(Set<String> l: props){
            if(l.contains("crit1") && l.contains("crit2"))
                mutexAut.addTransition("q0",l,"q1");
            else
                mutexAut.addTransition("q0",l,"q1");
            mutexAut.addTransition("q1",l,"q1");
        }*/

        printSubStage("Add two states to the automaton:\n" +
                "\t\tq0 - initial state,\n\t\tq1 - accepting state");
        mutexAut.addState("q0");
        mutexAut.addState("q1");
        mutexAut.setInitial("q0");
        mutexAut.setAccepting("q1");

        Predicate<Set<String>> phi = a -> a.contains("crit1") && a.contains("crit2");
        printSubStage("Add a transition from q0 to itself for all subsets of the atomic propositions that don't contain both crit1 and crit2,\n" +
                "\t\tas the automaton accepts only when both processes are in the critical section");
        props.stream().filter(phi.negate()).forEach(l -> mutexAut.addTransition("q0", l, "q0"));
        printSubStage("Add a transition from q0 to q1 for all other subsets of the atomic propositions,\n" +
                "\t\tas those are all the states of the program where both processes are in the critical section.");
        props.stream().filter(phi).forEach(l -> mutexAut.addTransition("q0", l, "q1"));
        printSubStage("Add a transition from q1 to itself for all the subsets of the atomic propositions,\n" +
                "\t\tsince after the automaton has transitioned to the accepting state it will remain there.");
        props.forEach(l -> mutexAut.addTransition("q1", l, "q1"));
        subStageNum = 0;
        return mutexAut;
    }

    private static Automaton<String, String> createNonStarvationFreedomAut(
            TransitionSystem<Pair<Pair<String, String>, Map<String, Object>>, String, String> ts) {
        Automaton<String, String> starveAut = new Automaton<>();
        /*final String STARV_1 = "process 1 starv";
        final String STARV_2 = "process 2 starv";
        final String NO_STARV = "no starvation";

        System.out.println("The automaton will have three states:");
        System.out.println("The first state represents that process 1 will starv, \nmeans he is waiting to get "
                + "into the critical section, but will never enter it.");
        starveAut.addState(STARV_1);
        System.out.println("The second state represents that process 2 will starv, \nmeans he is waiting to get "
                + "into the critical section, but will never enter it.");
        starveAut.addState(STARV_2);
        System.out.println("The third state represents that there is no starvation.");
        starveAut.addState(NO_STARV);
        System.out.println("our initial state is the no starvation state.");
        starveAut.setInitial(NO_STARV);

        System.out.println(
                "For each possible permutation of the atomic propositions our initial state can stay in the same state.");
        System.out.println(
                "If we see wait1 our automaton can move in a non determistic way to " + STARV_1 + ".");
        System.out.println(
                "If we see wait2 our automaton can move in a non determistic way to " + STARV_2 + ".");
        System.out.println(
                "If we are at " + STARV_1 + " we will stay there as long as we will not get cs_1.");
        System.out.println(
                "If we are at " + STARV_2 + " we will stay there as long as we will not get cs_2.");

        for (Set<String> atomProp : Util.powerSet(labels)) {
            starveAut.addTransition(NO_STARV, atomProp, NO_STARV);
            if (atomProp.contains("wait1"))
                starveAut.addTransition(NO_STARV, atomProp, STARV_1);
            if (!atomProp.contains("crit1"))
                starveAut.addTransition(STARV_1, atomProp, STARV_1);


            if (atomProp.contains("wait2"))
                starveAut.addTransition(NO_STARV, atomProp, STARV_2);
            if (!atomProp.contains("crit2"))
                starveAut.addTransition(STARV_2, atomProp, STARV_2);

        }

        System.out.println("Our automaton will accept if there is a run that one of the \n"
                + "proccesses will do wait and then will never get into the critical section. \n"
                + "Means our accepting state are: " + STARV_1 + " and " + STARV_2 + ".\n");

        starveAut.setAccepting(STARV_1);
        starveAut.setAccepting(STARV_2);
        subStageNum = 1;*/

        printSubStage("Create a power set of the atomic propositions of the transition system.\n" +
                "\t\tThese will be the symbols for the transitions of the automaton.");
        Set<Set<String>> props = Util.powerSet(ts.getAtomicPropositions());

        printSubStage("Add two states to the automaton:\n" +
                "\t\tq0 - initial state,\n\t\tq1 - accepting state");
        starveAut.addState("q0");
        starveAut.addState("q1");
        starveAut.setInitial("q0");
        starveAut.setAccepting("q1");

        printSubStage("Add a transition from q0 to itself for all subsets of the atomic propositions");
        props.forEach(l -> starveAut.addTransition("q0", l, "q0"));
        printSubStage("Add a transition from q0 to q1 for all subsets of the atomic propositions that contain wait1,\n" +
                "\t\tsince the automaton will accept only when process 1 is stuck and can't enter the critical section.");
        props.stream().filter(a -> a.contains("wait1")).forEach(l -> starveAut.addTransition("q0", l, "q1"));
        printSubStage("Add a transition from q1 to itself for all the labels where process 1 isn't in the criticl section, to create starvation.");
        props.stream().filter(a -> !a.contains("crit1")).forEach(l -> starveAut.addTransition("q1", l, "q1"));

        subStageNum = 0;
        return starveAut;
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
