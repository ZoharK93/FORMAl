package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.exceptions.*;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public class TransitionSystemImpl<STATE,ACTION,ATOMIC_PROPOSITION> implements TransitionSystem<STATE,ACTION,ATOMIC_PROPOSITION> {

    String name;
    Set<ACTION> actions;
    Map<STATE, Boolean> states;
    Set<ATOMIC_PROPOSITION> atomic_propositions;
    Set<Transition<STATE,ACTION>> transitions;
    Map<STATE, Set<ATOMIC_PROPOSITION>> labeling_function;

    public TransitionSystemImpl(){
        actions = new HashSet<>();
        states = new HashMap<>();
        atomic_propositions = new HashSet<>();
        transitions = new HashSet<>();
        labeling_function = new HashMap<>();
    }

    @Override
    public String getName() {
        return name;
    }

    @Override
    public void setName(String name) {
        this.name = name;
    }

    @Override
    public void addAction(ACTION anAction) {
        actions.add(anAction);
    }

    @Override
    public void setInitial(STATE aState, boolean isInitial) throws StateNotFoundException {
        if(!states.containsKey(aState))
            throw new StateNotFoundException(aState);
        states.replace(aState, isInitial);
    }

    @Override
    public void addState(STATE state) {
        if(states.containsKey(state)) return;
        states.put(state, false);
        labeling_function.put(state, new HashSet<>());
    }

    @Override
    public void addTransition(Transition<STATE, ACTION> t) throws FVMException {
        if(!states.containsKey(t.getFrom()))
            throw new InvalidTransitionException(t);
        if(!states.containsKey(t.getTo()))
            throw new InvalidTransitionException(t);
        if(!actions.contains(t.getAction()))
            throw new InvalidTransitionException(t);

        transitions.add(t);
    }

    @Override
    public Set<ACTION> getActions() {
        return actions;
    }

    @Override
    public void addAtomicProposition(ATOMIC_PROPOSITION p) {
        atomic_propositions.add(p);
    }

    @Override
    public Set<ATOMIC_PROPOSITION> getAtomicPropositions() {
        return atomic_propositions;
    }

    @Override
    public void addToLabel(STATE s, ATOMIC_PROPOSITION l) throws FVMException {
        if(!atomic_propositions.contains(l))
            throw new InvalidLablingPairException(s,l);
        try {
            labeling_function.get(s).add(l);
        }
        catch (Exception e){ throw new StateNotFoundException(s);}
    }

    @Override
    public Set<ATOMIC_PROPOSITION> getLabel(STATE s) {
        if(!states.containsKey(s))
            throw new StateNotFoundException(s);
        return labeling_function.get(s);
    }

    @Override
    public Set<STATE> getInitialStates() {
        Set<STATE> initialStates = new HashSet<>();
        for (STATE state: states.keySet()) {
            if(states.get(state))
                initialStates.add(state);
        }
        return initialStates;
    }

    @Override
    public Map<STATE, Set<ATOMIC_PROPOSITION>> getLabelingFunction() {
        return labeling_function;
    }

    @Override
    public Set<STATE> getStates() {
        return states.keySet();
    }

    @Override
    public Set<Transition<STATE, ACTION>> getTransitions() {
        return transitions;
    }

    @Override
    public void removeAction(ACTION action) throws FVMException {
        for(Transition t: transitions){
            if(t.getAction().equals(action))
                throw new DeletionOfAttachedActionException(action, TransitionSystemPart.TRANSITIONS);
        }
        actions.remove(action);
    }

    @Override
    public void removeAtomicProposition(ATOMIC_PROPOSITION p) throws FVMException {
        for(Set labels: labeling_function.values()){
            if(labels.contains(p))
                throw new DeletionOfAttachedAtomicPropositionException(p,TransitionSystemPart.ATOMIC_PROPOSITIONS);
        }
    }

    @Override
    public void removeLabel(STATE s, ATOMIC_PROPOSITION l) {
        labeling_function.get(s).remove(l);
    }

    @Override
    public void removeState(STATE state) throws FVMException {
        for(Transition t: transitions){
            if(t.getFrom().equals(state) || t.getTo().equals(state))
                throw new DeletionOfAttachedStateException(state, TransitionSystemPart.TRANSITIONS);
        }
        if(!labeling_function.get(state).isEmpty())
            throw new DeletionOfAttachedStateException(state, TransitionSystemPart.LABELING_FUNCTION);
        if(states.get(state))
            throw new DeletionOfAttachedStateException(state, TransitionSystemPart.INITIAL_STATES);

        states.remove(state);
        labeling_function.remove(state);
    }

    @Override
    public void removeTransition(Transition<STATE, ACTION> t) {
        transitions.remove(t);
    }
}
