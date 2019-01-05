package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.automata.MultiColorAutomaton;
import il.ac.bgu.cs.fvm.channelsystem.ChannelSystem;
import il.ac.bgu.cs.fvm.channelsystem.InterleavingActDef;
import il.ac.bgu.cs.fvm.channelsystem.ParserBasedInterleavingActDef;
import il.ac.bgu.cs.fvm.circuits.Circuit;
import il.ac.bgu.cs.fvm.exceptions.ActionNotFoundException;
import il.ac.bgu.cs.fvm.exceptions.StateNotFoundException;
import il.ac.bgu.cs.fvm.ltl.LTL;
import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaFileReader;
import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaParser.DostmtContext;
import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaParser.IfstmtContext;
import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaParser.OptionContext;
import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaParser.StmtContext;
import il.ac.bgu.cs.fvm.programgraph.ActionDef;
import il.ac.bgu.cs.fvm.programgraph.ConditionDef;
import il.ac.bgu.cs.fvm.programgraph.PGTransition;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;
import il.ac.bgu.cs.fvm.transitionsystem.AlternatingSequence;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;
import il.ac.bgu.cs.fvm.verification.VerificationFailed;
import il.ac.bgu.cs.fvm.verification.VerificationResult;
import il.ac.bgu.cs.fvm.programgraph.ParserBasedActDef;
import il.ac.bgu.cs.fvm.programgraph.ParserBasedCondDef;
import il.ac.bgu.cs.fvm.verification.VerificationSucceeded;

import java.io.InputStream;
import java.util.*;

import static il.ac.bgu.cs.fvm.nanopromela.NanoPromelaFileReader.pareseNanoPromelaFile;
import static il.ac.bgu.cs.fvm.nanopromela.NanoPromelaFileReader.pareseNanoPromelaString;
import static il.ac.bgu.cs.fvm.nanopromela.NanoPromelaFileReader.parseNanoPromelaStream;

/**
 * Implement the methods in this class. You may add additional classes as you
 * want, as long as they live in the {@code impl} package, or one of its 
 * sub-packages.
 */
public class FvmFacadeImpl implements FvmFacade {

    @Override
    public <S, A, P> TransitionSystem<S, A, P> createTransitionSystem() {
        return new TransitionSystemImpl<>();
    }

    @Override
    public <S, A, P> boolean isActionDeterministic(TransitionSystem<S, A, P> ts) {
        if(ts.getInitialStates().size() > 1) return false;
        Set<Transition<S,A>> transitions = ts.getTransitions();
        for(S state: ts.getStates()){
            Set<A> actions = new HashSet<>();
            for(Transition<S,A> tr: transitions){
                if(!tr.getFrom().equals(state)) continue;
                if(actions.contains(tr.getAction()))
                    return false;
                actions.add(tr.getAction());
            }
        }
        return true;
    }

    @Override
    public <S, A, P> boolean isAPDeterministic(TransitionSystem<S, A, P> ts) {
        if(ts.getInitialStates().size() > 1) return false;
        Map<S, Set<P>> labels = ts.getLabelingFunction();
        for(S state: labels.keySet()){
            Set<S> postStates = post(ts, state);
            Set<Set<P>> labelSets = new HashSet<>();
            for(S post:postStates){
                if(!labelSets.add(labels.get(post))) return false;
            }
        }
        return true;
    }

    @Override
    public <S, A, P> boolean isExecution(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        return isInitialExecutionFragment(ts, e) && isMaximalExecutionFragment(ts, e);
    }

    @Override
    public <S, A, P> boolean isExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        if(e.isEmpty()) return true;
        S state = e.head();
        AlternatingSequence<A, S> seq = e.tail();
        if(!ts.getStates().contains(state))
            throw new StateNotFoundException(state);
        if(seq.isEmpty()) return true;
        A action = seq.head();
        if(!ts.getActions().contains(action))
            throw new ActionNotFoundException(action);
        S next = seq.tail().head();
        for(Transition<S,A> tr: ts.getTransitions()) {
            if (!tr.getFrom().equals(state) || !tr.getAction().equals(action)) continue;
            if(tr.getTo().equals(next))
                return isExecutionFragment(ts, seq.tail());
        }
        return false;
    }

    @Override
    public <S, A, P> boolean isInitialExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        return ts.getInitialStates().contains(e.head()) && isExecutionFragment(ts, e);
    }

    @Override
    public <S, A, P> boolean isMaximalExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        return isExecutionFragment(ts, e) && isStateTerminal(ts, e.last());
    }

    @Override
    public <S, A> boolean isStateTerminal(TransitionSystem<S, A, ?> ts, S s) {
        Set<S> postStates = post(ts, s);
        return postStates.isEmpty() || (postStates.size() == 1 && postStates.contains(s));
    }

    @Override
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, S s) {
        if(!ts.getStates().contains(s))
            throw new StateNotFoundException(s);
        Set<S> post = new HashSet<>();
        for(Transition<S,?> tr: ts.getTransitions()){
            if(tr.getFrom().equals(s))
                post.add(tr.getTo());
        }
        return post;
    }

    @Override
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, Set<S> c) {
        Set<S> postStates = new HashSet<>();
        for(S state: c){
            postStates.addAll(post(ts,state));
        }
        return postStates;
    }

    @Override
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, S s, A a) {
        if(!ts.getStates().contains(s))
            throw new StateNotFoundException(s);
        Set<S> post = new HashSet<>();
        for(Transition<S,?> tr: ts.getTransitions()){
            if(tr.getFrom().equals(s) && tr.getAction().equals(a))
                post.add(tr.getTo());
        }
        return post;
    }

    @Override
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
        Set<S> postStates = new HashSet<>();
        for(S state: c){
            postStates.addAll(post(ts,state,a));
        }
        return postStates;
    }

    @Override
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, S s) {
        if(!ts.getStates().contains(s))
            throw new StateNotFoundException(s);
        Set<S> pre = new HashSet<>();
        for(Transition<S,?> tr: ts.getTransitions()){
            if(tr.getTo().equals(s))
                pre.add(tr.getFrom());
        }
        return pre;
    }

    @Override
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, Set<S> c) {
        Set<S> preStates = new HashSet<>();
        for(S state: c){
            preStates.addAll(pre(ts,state));
        }
        return preStates;
    }

    @Override
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, S s, A a) {
        if(!ts.getStates().contains(s))
            throw new StateNotFoundException(s);
        Set<S> pre = new HashSet<>();
        for(Transition<S,?> tr: ts.getTransitions()){
            if(tr.getTo().equals(s) && tr.getAction().equals(a))
                pre.add(tr.getFrom());
        }
        return pre;
    }

    @Override
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
        Set<S> preStates = new HashSet<>();
        for(S state: c){
            preStates.addAll(pre(ts,state,a));
        }
        return preStates;
    }

    @Override
    public <S, A> Set<S> reach(TransitionSystem<S, A, ?> ts) {
        Set<S> states = new HashSet<>();
        Set<S> init = ts.getInitialStates();
        boolean allTerminal = false;
        while(!allTerminal){
            allTerminal = true;
            for(S state: init){
                if(states.contains(state)) continue;
                if(!isStateTerminal(ts, state))
                    allTerminal=false;
            }
            states.addAll(init);
            init = post(ts,init);
        }
        return states;
    }

    @Override
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2) {
        return interleave(ts1,ts2,new HashSet<>());
    }

    @Override
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2, Set<A> handShakingActions) {
        TransitionSystem<Pair<S1, S2>, A, P> newTS = new TransitionSystemImpl<>();
        Set<Pair<S1,S2>> states = new HashSet<>();
        Set<Pair<S1,S2>> initials = new HashSet<>();
        Set<A> actions = new HashSet<>();
        Set<P> labels = new HashSet<>();
        for(S1 s1: ts1.getStates()){
            for(S2 s2: ts2.getStates()) {
                states.add(new Pair<>(s1, s2));

            }
        }

        actions.addAll(ts1.getActions());
        actions.addAll(ts2.getActions());
        labels.addAll(ts1.getAtomicPropositions());
        labels.addAll(ts2.getAtomicPropositions());
        newTS.addAllStates(states);
        newTS.addAllActions(actions);
        newTS.addAllAtomicPropositions(labels);

        for(S1 s1: ts1.getInitialStates()){
            for(S2 s2: ts2.getInitialStates()) {
                newTS.setInitial(new Pair<>(s1, s2),true);
            }
        }

        for(Transition<S1,A> t1: ts1.getTransitions()){
            if(handShakingActions.contains(t1.getAction())) continue;
            for(S2 s: ts2.getStates()){
                Transition<Pair<S1,S2>,A> trans =
                        new Transition<>(new Pair<>(t1.getFrom(),s),t1.getAction(),new Pair<>(t1.getTo(),s));
                newTS.addTransition(trans);
            }
        }

        for(Transition<S2,A> t2: ts2.getTransitions()){
            if(handShakingActions.contains(t2.getAction())) continue;
            for(S1 s: ts1.getStates()){
                Transition<Pair<S1,S2>,A> trans =
                        new Transition<>(new Pair<>(s,t2.getFrom()),t2.getAction(),new Pair<>(s,t2.getTo()));
                newTS.addTransition(trans);
            }
        }

        for(A action: handShakingActions){
            Set<S1> fromS1 = new HashSet<>();
            Set<S1> toS1 = new HashSet<>();
            Set<S2> fromS2 = new HashSet<>();
            Set<S2> toS2 = new HashSet<>();
            for(Transition<S1,A> t1: ts1.getTransitions()) {
                if (t1.getAction().equals(action)) {
                    fromS1.add(t1.getFrom());
                    toS1.add(t1.getTo());
                }
            }

            for(Transition<S2,A> t2: ts2.getTransitions()) {
                if (t2.getAction().equals(action)) {
                    fromS2.add(t2.getFrom());
                    toS2.add(t2.getTo());
                }
            }
            for(S1 s1: fromS1){
                for(S2 s2: fromS2){
                    Pair<S1,S2> from = new Pair<>(s1,s2);
                    for(S1 s1t: toS1){
                        for(S2 s2t: toS2){
                            Pair<S1,S2> to = new Pair<>(s1t,s2t);
                            if(ts1.getTransitions().contains(new Transition<>(s1,action,s1t)) &&
                                    ts2.getTransitions().contains(new Transition<>(s2,action,s2t)))
                                newTS.addTransition(new Transition<>(from, action, to));
                        }
                    }
                }
            }
        }

        for(Pair<S1,S2> state:states){
            for(P prop:ts1.getLabel(state.getFirst()))
                newTS.addToLabel(state,prop);
            for(P prop:ts2.getLabel(state.getSecond()))
                newTS.addToLabel(state,prop);
        }

        removeUnreachableStates(newTS,states);

        return newTS;
    }

    @Override
    public <L, A> ProgramGraph<L, A> createProgramGraph() {
        return new ProgramGraphImpl<>();
    }

    @Override
    public <L1, L2, A> ProgramGraph<Pair<L1, L2>, A> interleave(ProgramGraph<L1, A> pg1, ProgramGraph<L2, A> pg2) {
        ProgramGraph<Pair<L1, L2>, A> newPG = new ProgramGraphImpl<>();
        //Set<Pair<L1,L2>> locations = new HashSet<>();

        for(L1 l1: pg1.getLocations()){
            for(L2 l2: pg2.getLocations()) {
                newPG.addLocation(new Pair<>(l1, l2));
            }
        }


        for(L1 l1: pg1.getInitialLocations()){
            for(L2 l2: pg2.getInitialLocations()) {
                newPG.setInitial(new Pair<>(l1, l2),true);
            }
        }

        for(List<String> i1: pg1.getInitalizations()){
            for(List<String> i2: pg2.getInitalizations()) {
                List<String> newInit = new ArrayList<>();
                newInit.addAll(i1); newInit.addAll(i2);
                newPG.addInitalization(newInit);
            }
        }

        for(PGTransition<L1,A> tr1: pg1.getTransitions()){
            for(L2 l: pg2.getLocations()){
                PGTransition<Pair<L1,L2>,A> trans =
                        new PGTransition<>(new Pair<>(tr1.getFrom(),l),tr1.getCondition(),tr1.getAction(),
                                new Pair<>(tr1.getTo(),l));
                newPG.addTransition(trans);
            }
        }

        for(PGTransition<L2,A> tr2: pg2.getTransitions()){
            for(L1 l: pg1.getLocations()){
                PGTransition<Pair<L1,L2>,A> trans =
                        new PGTransition<>(new Pair<>(l,tr2.getFrom()),tr2.getCondition(),tr2.getAction(),
                                new Pair<>(l,tr2.getTo()));
                newPG.addTransition(trans);
            }
        }

        return newPG;
    }

    @Override
    public TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> transitionSystemFromCircuit(Circuit c) {
        TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> newTS = new TransitionSystemImpl<>();

        Set<String> inputs = c.getInputPortNames();
        Set<String> registers = c.getRegisterNames();
        Set<String> outputs = c.getOutputPortNames();

        String[] inputArr = inputs.toArray(new String[inputs.size()]);
        String[] regArr = registers.toArray(new String[registers.size()]);
        String[] outputArr = outputs.toArray(new String[outputs.size()]);

        Set<Pair<Map<String, Boolean>, Map<String, Boolean>>> states = new HashSet<>();

        newTS.addAllAtomicPropositions(inputArr);
        newTS.addAllAtomicPropositions(regArr);
        newTS.addAllAtomicPropositions(outputArr);

        int varsNum = inputArr.length+regArr.length;
        boolean[] bits = new boolean[varsNum];

        for(int i=0;i<Math.pow(2,varsNum);i++){
            Map<String,Boolean> inState = new HashMap<>();
            Map<String,Boolean> regState = new HashMap<>();
            List<String> labels = new ArrayList<>();

            for (int b = varsNum - 1; b >= 0; b--)
                bits[b] = (i & (1 << b)) != 0;

            for(int j=0;j<inputArr.length;j++) {
                inState.put(inputArr[j], bits[j]);
                if (bits[j]) labels.add(inputArr[j]);
            }

            boolean isInitial = true;
            for(int j=0;j<regArr.length;j++) {
                regState.put(regArr[j], bits[inputArr.length + j]);
                if(bits[inputArr.length + j]) {
                    isInitial=false;
                    labels.add(regArr[j]);
                }
            }

            Pair<Map<String, Boolean>, Map<String, Boolean>> state = new Pair<>(inState,regState);
            newTS.addState(state);
            states.add(state);
            newTS.addAction(inState);
            newTS.setInitial(state,isInitial);
            for(String l:labels)
                newTS.addToLabel(state,l);
            Map<String,Boolean> out = c.computeOutputs(inState,regState);
            for(String l:out.keySet())
                if(out.get(l))
                    newTS.addToLabel(state,l);
        }

        for(Pair<Map<String, Boolean>, Map<String, Boolean>> state: newTS.getStates()){
            Map<String, Boolean> ins = state.first;
            Map<String, Boolean> regs = state.second;
            for(Pair<Map<String, Boolean>, Map<String, Boolean>> nextState: newTS.getStates()){
                Map<String, Boolean> nextInput = nextState.first;
                Map<String, Boolean> nextRegs = c.updateRegisters(ins,regs);
                newTS.addTransition(new Transition<>(state,nextInput,new Pair<>(nextInput,nextRegs)));
            }
        }

        removeUnreachableStates(newTS,states);

        return newTS;
    }

    @Override
    public <L, A> TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystemFromProgramGraph(ProgramGraph<L, A> pg, Set<ActionDef> actionDefs, Set<ConditionDef> conditionDefs) {
        TransitionSystem<Pair<L, Map<String, Object>>, A, String> newTS = new TransitionSystemImpl<>();
        Set<Pair<L, Map<String, Object>>> allStates = new HashSet<>();
        Set<Transition<Pair<L, Map<String, Object>>,A>> allTransitions = new HashSet<>();

        for(L loc:pg.getInitialLocations()){
            if(pg.getInitalizations().isEmpty()){
                Pair<L, Map<String, Object>> state = new Pair<>(loc,new HashMap<>());
                newTS.addState(state);
                allStates.add(state);
                newTS.setInitial(state, true);
            }
            for(List<String> init: pg.getInitalizations()){
                Set<Map<String, Object>> evals = new HashSet<>();
                Map<String, Object> eval = new HashMap<>();
                for(String action: init){
                    eval = ActionDef.effect(actionDefs, eval, action);
                }
                Pair<L, Map<String, Object>> state = new Pair<>(loc,eval);
                newTS.addState(state);
                allStates.add(state);
                newTS.setInitial(state, true);
            }
        }

        boolean addedNewTr = true;
        while(addedNewTr){
            addedNewTr = false;
            for(PGTransition<L, A> tr: pg.getTransitions()) {
                newTS.addAction(tr.getAction());
                Set<Pair<L, Map<String, Object>>> states = new HashSet<>();
                Set<Transition<Pair<L, Map<String, Object>>,A>> transitions = new HashSet<>();
                for(Pair<L, Map<String, Object>> state:newTS.getStates()){
                    if(!tr.getFrom().equals(state.getFirst())) continue;
                    if(!ConditionDef.evaluate(conditionDefs, state.getSecond(),tr.getCondition())) continue;
                    Map<String, Object> eval = ActionDef.effect(actionDefs,state.getSecond(),tr.getAction());
                    Pair<L, Map<String, Object>> newState = new Pair<>(tr.getTo(),eval);
                    states.add(newState);
                    allStates.add(newState);
                    transitions.add(new Transition(state, tr.getAction(), newState));
                    addedNewTr = (addedNewTr || allTransitions.add(new Transition(state, tr.getAction(), newState)));
                }
                newTS.addAllStates(states);
                for(Transition<Pair<L, Map<String, Object>>,A> trans: transitions)
                    newTS.addTransition(trans);
            }
        }

        for(Pair<L,Map<String, Object>> state:newTS.getStates()){
            newTS.addAtomicProposition(state.getFirst().toString());
            for(String name:state.getSecond().keySet()) {
                String condStr = name + " = " + state.getSecond().get(name);
                newTS.addAtomicProposition(condStr);
                newTS.addToLabel(state,condStr);
            }
            newTS.addToLabel(state,state.getFirst().toString());
        }

        return newTS;
    }

    @Override
    public <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem(ChannelSystem<L, A> cs) {
        TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> newTS = createTransitionSystem();
        Set<ActionDef> effect = new HashSet<>();
        effect.add(new ParserBasedActDef());
        Set<ConditionDef> cond = new HashSet<>();
        cond.add(new ParserBasedCondDef());
        List<L> initLocs = new ArrayList<>();
        List<List<String>> allInits = new ArrayList<>();

        for(int i=0;i<cs.getProgramGraphs().size();i++)
            for(List<String> init : cs.getProgramGraphs().get(i).getInitalizations())
                allInits.add(init);

        Set<Map<String, Object>> allEvals = new HashSet<>();

        for(List<String> var : allInits)
        {
            Map<String, Object> varInit = new HashMap<>();
            for(String action : var)
                varInit = ActionDef.effect(effect, varInit, action);
            allEvals.add(varInit);
        }

        addInitialStatesTSFromCS(newTS, cs, initLocs, allEvals);

        transitionSystemFromCSFromInitialStates(newTS, cs, effect, cond);

        for(Pair<List<L>, Map<String, Object>> state : newTS.getStates())
        {
            for(L l: state.getFirst())
            {
                newTS.addAtomicProposition(l.toString());
                newTS.addToLabel(state, l.toString());
            }

            for(String var : state.second.keySet())
            {
                String newAtomicPreposition = var + " = " + state.second.get(var).toString();
                newTS.addAtomicProposition(newAtomicPreposition);
                newTS.addToLabel(state,newAtomicPreposition);
            }
        }

        return newTS;
    }

    private <L,A> void addInitialStatesTSFromCS(TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> ts,
                                                    ChannelSystem<L, A> cs, List<L> newInitLocs, Set<Map<String, Object>> allEvals)
    {
        int size = newInitLocs.size();
        if(size == cs.getProgramGraphs().size())
        {
            if(allEvals.isEmpty())
            {
                Pair<List<L>, Map<String, Object>> newState = new Pair<>
                        (new ArrayList<>(newInitLocs), new HashMap<>());
                ts.addState(newState);
                ts.setInitial(newState, true);
            }

            for(Map<String, Object> eval : allEvals)
            {
                Pair<List<L>, Map<String, Object>> newState = new Pair<>
                        (new ArrayList<>(newInitLocs), new HashMap<>(eval));
                ts.addState(newState);
                ts.setInitial(newState, true);
            }
        }
        else
        {
            for(L loc : cs.getProgramGraphs().get(size).getInitialLocations())
            {
                newInitLocs.add(loc);
                addInitialStatesTSFromCS(ts, cs, newInitLocs, allEvals);
                newInitLocs.remove(loc);
            }
        }
    }

    private <L, A>void transitionSystemFromCSFromInitialStates(TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> ts,
                                                               ChannelSystem<L, A> cs, Set<ActionDef> effect, Set<ConditionDef> cond)
    {
        InterleavingActDef channelActionDef = new ParserBasedInterleavingActDef();
        Deque<Pair<List<L>, Map<String, Object>>> queue = new LinkedList<>(ts.getInitialStates());
        Set<Pair<List<L>, Map<String, Object>>> allreadyChecked = new HashSet<>(ts.getInitialStates());
        while(!queue.isEmpty())
        {
            Pair<List<L>, Map<String, Object>> fromState = queue.removeFirst();
            Map<Integer, Set<PGTransition<L, A>>> allPGTransMap = getAllPGTransMapFromState(cs.getProgramGraphs(), fromState);
            Map<Integer, Set<PGTransition<L, A>>> allOneSidedTransMapRead = getAllOneSidedActionTransFromAllTrans(allPGTransMap, "?");
            Map<Integer, Set<PGTransition<L, A>>> allOneSidedTransMapWrite = getAllOneSidedActionTransFromAllTrans(allPGTransMap, "!");
            for(int i = 0; i < allPGTransMap.size(); i++)
                for(PGTransition<L, A> pgTrans : allPGTransMap.get(i))
                {
                    String currAction = pgTrans.getAction().toString();
                    if(ConditionDef.evaluate(cond, fromState.second, pgTrans.getCondition()))
                    {
                        if(!channelActionDef.isOneSidedAction(currAction) && ActionDef.effect(effect, fromState.second, pgTrans.getAction()) != null)
                        {
                            ts.addAction(pgTrans.getAction());
                            List<L> locsForNewState = new ArrayList<>(fromState.getFirst());
                            locsForNewState.set(i, pgTrans.getTo());
                            Pair<List<L>, Map<String, Object>> toState = new Pair<>(locsForNewState, ActionDef.effect(effect, fromState.second, pgTrans.getAction()));
                            Transition< Pair<List<L>, Map<String, Object>>, A> newTrans = new Transition<>(fromState, pgTrans.getAction(), toState);
                            if(!allreadyChecked.contains(toState))
                            {
                                ts.addState(toState);
                                allreadyChecked.add(toState);
                                queue.addLast(toState);
                            }
                            ts.addTransition(newTrans);
                        }
                        else
                        {
                            Map<Integer, Set<PGTransition<L, A>>> allOneSidedTransToIterate;
                            String firstQueueName = getQueueNameFromOneSidedAction(currAction);
                            if(currAction.contains("?"))
                                allOneSidedTransToIterate = allOneSidedTransMapWrite;
                            else
                                allOneSidedTransToIterate = allOneSidedTransMapRead;

                            for(int pgNum = i+1; pgNum < cs.getProgramGraphs().size(); pgNum++)
                            {
                                for(PGTransition<L, A> otherPGTrans : allOneSidedTransToIterate.get(pgNum))
                                {
                                    if(ConditionDef.evaluate(cond, fromState.second, otherPGTrans.getCondition()) &&
                                            firstQueueName.equals(getQueueNameFromOneSidedAction(otherPGTrans.getAction().toString())))
                                    {
                                        String newAction = currAction + "|" + otherPGTrans.getAction().toString();
                                        ts.addAction((A)newAction);
                                        List<L> locsForNewState = new ArrayList<>(fromState.getFirst());
                                        locsForNewState.set(i, pgTrans.getTo());
                                        locsForNewState.set(pgNum, otherPGTrans.getTo());
                                        Pair<List<L>, Map<String, Object>> toState = new Pair<>(locsForNewState, channelActionDef.effect(fromState.second, newAction));
                                        Transition<Pair<List<L>, Map<String, Object>>, A> newTrans = new Transition<>(fromState, (A)newAction, toState);
                                        if(!allreadyChecked.contains(toState))
                                        {
                                            ts.addState(toState);
                                            allreadyChecked.add(toState);
                                            queue.addLast(toState);
                                        }

                                        ts.addTransition(newTrans);
                                    }}}}}}}
    }

    private <L,A> Map<Integer, Set<PGTransition<L, A>>> getAllOneSidedActionTransFromAllTrans(Map<Integer, Set<PGTransition<L, A>>> allPGTransMap, String readOrWrite)
    {
        InterleavingActDef channelActionDef = new ParserBasedInterleavingActDef();
        Map<Integer, Set<PGTransition<L, A>>> res = new HashMap<>();
        for(int i = 0; i < allPGTransMap.size(); i++)
        {
            Set<PGTransition<L, A>> pgOneSidedTrans = new HashSet<>();
            for(PGTransition<L, A> pgTrans : allPGTransMap.get(i))
            {
                if(channelActionDef.isOneSidedAction(pgTrans.getAction().toString()) &&
                        pgTrans.getAction().toString().contains(readOrWrite))
                    pgOneSidedTrans.add(pgTrans);
            }
            res.put(i, pgOneSidedTrans);
        }
        return res;
    }

    private <L, A> Map<Integer, Set<PGTransition<L, A>>> getAllPGTransMapFromState(List<ProgramGraph<L, A>> pgs, Pair<List<L>, Map<String, Object>> fromState)
    {
        Map<Integer, Set<PGTransition<L, A>>> allPGTransMap = new HashMap<>();
        for(int i = 0; i < pgs.size(); i++)
        {
            ProgramGraph<L, A> currPG = pgs.get(i);
            L locOfCurrPG = fromState.getFirst().get(i);
            Set<PGTransition<L, A>> currPGTransitions = new HashSet<>();
            for(PGTransition<L, A> pgTrans : currPG.getTransitions())
                if(pgTrans.getFrom().equals(locOfCurrPG))
                    currPGTransitions.add(pgTrans);

            allPGTransMap.put(i, currPGTransitions);
        }
        return allPGTransMap;
    }

    private String getQueueNameFromOneSidedAction(String oneSidedAction)
    {
        int breakIndex = 0;
        for(int i = 0; i < oneSidedAction.length(); i++)
        {
            if(oneSidedAction.charAt(i) == '!' || oneSidedAction.charAt(i) == '?')
                breakIndex = i;
        }
        return oneSidedAction.substring(0, breakIndex);
    }

    @Override
    public <Sts, Saut, A, P> TransitionSystem<Pair<Sts, Saut>, A, Saut> product(TransitionSystem<Sts, A, P> ts, Automaton<Saut, P> aut) {
        TransitionSystem<Pair<Sts, Saut>, A, Saut> newTS = createTransitionSystem();

        Map<Sts, Set<P>> labels = ts.getLabelingFunction();
        for(Sts tsState : ts.getInitialStates()) {
            Set<P> label = labels.get(tsState) != null ? labels.get(tsState) : new HashSet();
            for(Saut autState: aut.getInitialStates())
                for(Saut toState : aut.nextStates(autState,label)) {
                    Pair<Sts, Saut> newSts = new Pair<>(tsState, toState);
                    newTS.addState(newSts);
                    newTS.setInitial(newSts,true);
                }
        }

        Deque<Pair<Sts, Saut>> states = new LinkedList<>(newTS.getInitialStates());
        while(!states.isEmpty())
        {
            Pair<Sts, Saut> state = states.removeFirst();
            for(Transition<Sts, A> tsTr : ts.getTransitions())
            {
                if(tsTr.getFrom().equals(state.getFirst()))
                {
                    A action = tsTr.getAction();
                    Sts tsToState = tsTr.getTo();
                    Set<P> labelTsToState =  labels.get(tsToState) != null ? labels.get(tsToState) : new HashSet();
                    Saut autFromState = state.getSecond();

                    Set<Saut> nextStates = aut.nextStates(autFromState,labelTsToState);
                    if(nextStates != null) {
                        for(Saut autToState : nextStates) {
                            Pair<Sts, Saut> newState = new Pair<>(tsToState, autToState);
                            if(!newTS.getStates().contains(newState))
                                states.addLast(newState);
                            newTS.addState(newState);
                            newTS.addAction(action);
                            newTS.addTransition(new Transition<>(state, action , newState));
                        }
                    }
                }
            }
        }

        for(Pair<Sts, Saut> state : newTS.getStates())
        {
            Saut label = state.getSecond();
            newTS.addAtomicProposition(label);
            newTS.addToLabel(state, label);
        }
        return newTS;
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromela(String filename) throws Exception {
        StmtContext stmt = pareseNanoPromelaFile(filename);
        return buildProgramGraph(stmt);
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromelaString(String nanopromela) throws Exception {
        StmtContext stmt = pareseNanoPromelaString(nanopromela);
        return buildProgramGraph(stmt);
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromela(InputStream inputStream) throws Exception {
        StmtContext stmt = parseNanoPromelaStream(inputStream);
        return buildProgramGraph(stmt);
    }

    //Implement up to here

    @Override
    public <S, A, P, Saut> VerificationResult<S> verifyAnOmegaRegularProperty(TransitionSystem<S, A, P> ts, Automaton<Saut, P> aut) {
        TransitionSystem<Pair<S, Saut>, A, Saut> productTS = product(ts, aut);
        for(Pair<S, Saut> prodState : productTS.getStates())
        {
            if(aut.getAcceptingStates().contains(prodState.getSecond()))
            {
                List<S> cycle = getPathBetweenStates(productTS, prodState, prodState, new HashSet<>(), new LinkedList<>());
                if(cycle == null) continue;
                for(Pair<S, Saut> initState : productTS.getInitialStates())
                {
                    List<S> prefix = getPathBetweenStates(productTS, initState, prodState, new HashSet<>(), new LinkedList<>());
                    if(prefix == null) continue;
                    VerificationFailed<S> ans = new VerificationFailed<>();
                    ans.setCycle(cycle);
                    ans.setPrefix(prefix);
                    return ans;
                }
            }
        }
        return new VerificationSucceeded<>();
    }

    private <S, A, Saut> List<S> getPathBetweenStates(TransitionSystem<Pair<S, Saut>, A, Saut> productTS, Pair<S, Saut> from,
                                                      Pair<S, Saut> to, Set<Pair<S, Saut>> checkedStates, List<S> path)
    {
        path.add(from.getFirst());
        for(Transition<Pair<S, Saut>, A> tr : productTS.getTransitions())
        {
            if(tr.getFrom().equals(from))
            {
                Pair<S, Saut> nextState = tr.getTo();
                if(nextState.equals(to))
                    return path;

                if(!checkedStates.contains(nextState))
                {
                    checkedStates.add(nextState);
                    List<S> tmpAns = getPathBetweenStates(productTS, nextState, to, checkedStates, path);
                    if(tmpAns != null)
                        return tmpAns;
                }
            }
        }
        path.remove(from.getFirst());
        return null;
    }

    @Override
    public <L> Automaton<?, L> LTL2NBA(LTL<L> ltl) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement LTL2NBA
    }

    @Override
    public <L> Automaton<?, L> GNBA2NBA(MultiColorAutomaton<?, L> mulAut) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement GNBA2NBA
    }


    //Helper functions

    private <S,A,P> void removeUnreachableStates(TransitionSystem<S,A,P> ts, Set<S> states){
        Set<S> reach = reach(ts);
        for(S state:states){
            if(!reach.contains(state)){
                Set<Transition<S,A>> transitions = ts.getTransitions();
                Set<Transition<S,A>> transitionsToRemove = new HashSet<>();
                for(Transition<S,A> tr: transitions){
                    if(tr.getFrom().equals(state) || tr.getTo().equals(state))
                        transitionsToRemove.add(tr);
                }
                for(Transition<S,A> tr: transitionsToRemove)
                    ts.removeTransition(tr);

                Set<P> labels = new HashSet<>(ts.getLabel(state));
                for(P label:labels){
                    ts.removeLabel(state, label);
                }
                ts.removeState(state);
            }
        }
    }

    private ProgramGraph<String, String> buildProgramGraph(StmtContext stmt)
    {
        ProgramGraph<String, String> newPG =  createProgramGraph();
        newPG.addLocation(stmt.getText());
        newPG.setInitial(stmt.getText(), true);
        newPG.addLocation("");

        buildPGFromRoot(newPG, stmt);
        return newPG;
    }

    private void buildPGFromRoot(ProgramGraph<String, String> pg, StmtContext stmt)
    {
        if(isSimpleStmt(stmt))
        {
            PGTransition<String, String> newTrans = new PGTransition<String, String>(stmt.getText(), "", stmt.getText(), "");
            pg.addTransition(newTrans);
        }
        else if((stmt.ifstmt() != null) || (stmt.dostmt() != null))
        {
            handleIfDoStmt(pg, stmt, stmt, "");
        }
        else if(stmt.stmt() != null)
        {
            handleSemicolon(pg, stmt, stmt, "");
        }
    }

    private void handleIfDoStmt(ProgramGraph<String, String> pg, StmtContext rootStmt, StmtContext childStmt, String cond)
    {
        if(isSimpleStmt(childStmt))
        {
            cond = closeParanthesis(cond);
            PGTransition<String, String> newTrans = new PGTransition<>(rootStmt.getText(), cond, childStmt.getText(), "");
            pg.addTransition(newTrans);
        }
        else if(childStmt.ifstmt() != null)
        {
            IfstmtContext ifStmt = childStmt.ifstmt();
            List<OptionContext> options = ifStmt.option();
            if(!cond.isEmpty())
                cond += " && (";
            for(OptionContext opt : options)
            {
                handleIfDoStmt(pg, rootStmt, opt.stmt(), cond + "(" + opt.boolexpr().getText() + ")");
            }
        }
        else if(childStmt.dostmt() != null)
        {
            DostmtContext doStmt = childStmt.dostmt();
            List<OptionContext> options = doStmt.option();

            Set<String> originalLocations = new HashSet<>(pg.getLocations());

            String newCond = new String(cond);
            if(!newCond.isEmpty())
                newCond += " && (";
            newCond += "!(";
            for(int i = 0; i < options.size(); i++)
            {
                newCond = newCond + "(" + options.get(i).boolexpr().getText() + ")";
                if(i < options.size() - 1)
                    newCond += "||";
            }
            newCond = closeParanthesis(newCond);
            PGTransition<String, String> newTrans = new PGTransition<>(rootStmt.getText(), newCond, "", "");
            pg.addTransition(newTrans);

            for(OptionContext opt : options)
            {
                ProgramGraph<String, String> optPG = buildProgramGraph(opt.stmt());
                newCond = new String(cond);
                if(!newCond.isEmpty() && !opt.boolexpr().getText().isEmpty())
                    newCond += " && (";
                newCond += "(" + opt.boolexpr().getText() + ")";
                newCond = closeParanthesis(newCond);
                getOriginalPG(pg, rootStmt, newCond, opt.stmt(), optPG, doStmt.getText());
            }
            runNewLocs(pg, originalLocations);
        }
        else if (childStmt.stmt() != null)
        {
            cond = closeParanthesis(cond);
            handleSemicolon(pg, rootStmt, childStmt, cond);
        }
    }

    private void handleSemicolon(ProgramGraph<String, String> pg, StmtContext rootStmt, StmtContext childStmt, String cond) {
        StmtContext firstStmt = childStmt;
        while(firstStmt.stmt() != null && !firstStmt.stmt().isEmpty())
            firstStmt = firstStmt.stmt().get(0);

        List<StmtContext> restStmts = new ArrayList<>();
        StmtContext iterator = childStmt;
        while(iterator.stmt() != null && !iterator.stmt().isEmpty())
        {
            restStmts.add(0, iterator.stmt().get(1));
            iterator = iterator.stmt().get(0);
        }

        ProgramGraph<String, String> firstStatementPG = buildProgramGraph(firstStmt);

        String lastStmt = restStmts.get(0).getText();
        for(int i = 1; i < restStmts.size(); i++)
        {
            lastStmt = lastStmt + ";" + restStmts.get(i).getText();
        }

        Set<String> originalLocations = new HashSet<>(pg.getLocations());
        getOriginalPG(pg, rootStmt, cond, firstStmt, firstStatementPG, lastStmt);
        runNewLocs(pg, originalLocations);
    }

    private void runNewLocs(ProgramGraph<String, String> pg, Set<String> originalLocations) {
        Set<String> updatedLocations = new HashSet<>(pg.getLocations());
        for(String loc : updatedLocations)
            if(!originalLocations.contains(loc)) {
                String res = "";
                for (int i = 0; i < loc.length(); i++) {
                    if (i + 1 < loc.length() && ((loc.charAt(i) == 'o' && loc.charAt(i + 1) == 'd') ||
                            (loc.charAt(i) == 'f' && loc.charAt(i + 1) == 'i'))) {
                        res += " " + loc.charAt(i) + loc.charAt(i + 1);
                        i++;
                    } else
                        res += loc.charAt(i);
                }
                buildPGFromRoot(pg, NanoPromelaFileReader.pareseNanoPromelaString(res));
            }
    }

    private void getOriginalPG(ProgramGraph<String, String> pg,
                               StmtContext rootStmt, String cond, StmtContext firstState,
                               ProgramGraph<String, String> firstStatementPG,
                               String lastsStatements) {
        for(PGTransition<String, String> firstPGTrans : firstStatementPG.getTransitions())
        {
            String fromState = rootStmt.getText();
            String newCond = firstPGTrans.getCondition();
            if(!firstPGTrans.getFrom().equals(firstState.getText()))
            {
                fromState = firstPGTrans.getFrom();
                if(!fromState.isEmpty())
                    fromState += ";";
                fromState += lastsStatements;
                pg.addLocation(fromState);
            }
            else
            {
                if(!cond.isEmpty())
                {
                    if(!newCond.isEmpty())
                        newCond = cond + " && (" + newCond;
                    else
                        newCond = cond;
                }
            }

            String toState = firstPGTrans.getTo();
            if(!toState.isEmpty())
                toState += ";";
            toState += lastsStatements;
            pg.addLocation(toState);

            newCond = closeParanthesis(newCond);
            PGTransition<String, String> newTrans = new PGTransition<>(fromState, newCond, firstPGTrans.getAction(), toState);
            pg.addTransition(newTrans);
        }
    }

    private boolean isSimpleStmt(StmtContext stmt)
    {
        return stmt.assstmt() != null || stmt.atomicstmt() != null || stmt.chanreadstmt() != null || stmt.chanwritestmt() != null || stmt.skipstmt() != null;
    }

    private String closeParanthesis(String s)
    {
        String res = s;
        int countOpen = 0;
        for(int i = 0; i < s.length(); i++)
        {
            if(s.charAt(i) == '(')
                countOpen++;
            else if(s.charAt(i) == ')')
                countOpen--;
        }

        for(int i = 0 ; i < countOpen; i++)
            res += ")";

        return res;
    }
}
