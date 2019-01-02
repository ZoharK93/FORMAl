package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.programgraph.PGTransition;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;

import java.util.*;

public class ProgramGraphImpl<L, A> implements ProgramGraph<L, A> {

    Map<L,Boolean> locations;
    Set<PGTransition<L,A>> transitions;
    Set<List<String>> initializations;
    String name;


    public ProgramGraphImpl(){
        locations=new HashMap<>();
        transitions = new HashSet<>();
        initializations = new HashSet<>();
    }


    @Override
    public void addInitalization(List<String> init) {
        initializations.add(init);
    }

    @Override
    public void setInitial(L location, boolean isInitial) {
        locations.replace(location, isInitial);
    }

    @Override
    public void addLocation(L l) {
        locations.put(l, false);
    }

    @Override
    public void addTransition(PGTransition<L, A> t) {
        transitions.add(t);
    }

    @Override
    public Set<List<String>> getInitalizations() {
        return initializations;
    }

    @Override
    public Set<L> getInitialLocations() {
        Set<L> initialLocs = new HashSet<>();
        for (L location: locations.keySet()) {
            if(locations.get(location))
                initialLocs.add(location);
        }
        return initialLocs;
    }

    @Override
    public Set<L> getLocations() {
        return locations.keySet();
    }

    @Override
    public String getName() {
        return name;
    }

    @Override
    public Set<PGTransition<L, A>> getTransitions() {
        return transitions;
    }

    @Override
    public void removeLocation(L l) {
        locations.remove(l);
    }

    @Override
    public void removeTransition(PGTransition<L, A> t) {
        transitions.remove(t);
    }

    @Override
    public void setName(String name) {
        this.name = name;
    }
}
