#lang forge/temporal

option max_tracelength 20
option min_tracelength 1

// MAGNETIC 
// Sigs for tracking which pole is faced up
abstract sig Polarity {}
one sig North, South extends Polarity{}

// Tower sig keeps track of the top ring in the stack and its own polarity
sig MTower {
    var Mtop: lone MRing,
    tpole: one Polarity
}

// Starting tower is where all rings start
// Ending tower is where all the rings should get to
one sig MStartingTower, MEndingTower extends MTower{}

// Ring keeps track of the ring immediately below it, the proper size order of rings 
// (which never changes), and its polarity (which changes on every move)
sig MRing {
    var Mbelow: lone MRing, // order on stack valid if top ring is bigger
    Morder: lone MRing,
    var pole: one Polarity
}

// Counter keeps track of how many moves are made
sig MCounter {
    var Mcounter: one Int
}

// Establishes the proper size order of rings and forces all rings in the starting
// tower to be in order, with polarity matching that of the starting tower.
pred MinitialOrder {
    MStartingTower.Mtop->(MRing - MStartingTower.Mtop) in ^Morder
    MStartingTower.Mtop->(MRing - MStartingTower.Mtop) in ^Mbelow
    // no cycles in order
    not {some iden & ^Morder}
    // all rings should have the same polarity as the starting tower
    all r:MRing | r.pole = MStartingTower.tpole
    // stack has to follow the proper order
    ^Mbelow in ^Morder
    MCounter.Mcounter = 0
}

// Sets the initial order of rings in the starting tower, and ensures no other
// tower has a top ring.
pred Minit {
    // linearity
    MinitialOrder
    some MStartingTower.Mtop
    all t: MTower | (t != MStartingTower) implies no t.Mtop
}

// Ensures rings are always in order, and that any ring has the same polarity as
// the ring below it, or has the same polarity as the tower it is in if there is 
// no ring below it.
pred Mwellformed {
    // below must always follow the same sequence set by order
    {^Mbelow in ^Morder}

    all r: MRing | {
        some r.Mbelow implies {
            r.pole = r.Mbelow.pole
        }
        no r.Mbelow implies {
            some t: MTower | {
                r = t.Mtop or (t.Mtop -> r in ^Mbelow)
                t.tpole = r.pole
            }
        }
    }
}

// Defines the constraints to make a move. Two towers will have their tops changed
// to reflect this movement. The ring moving has to flip its polarity, and has
// to have the polarity match whichever new tower it ends up in.
pred Mmove {
    some disj t1, t2:MTower, r1:MRing {
        t1.Mtop = r1
        t2.Mtop' = r1
        r1.Mbelow' = t2.Mtop
        t1.Mtop' = r1.Mbelow 
        some r1.Mbelow' implies {
            r1 -> r1.Mbelow' in ^Morder
            r1.pole' = r1.Mbelow'.pole
        }
        no r1.Mbelow' implies {
            r1.pole' = t2.tpole
        }
        all t:MTower | (t != t1 and t != t2) implies t.Mtop' = t.Mtop
        all r: MRing | r != r1 implies { 
            r.Mbelow' = r.Mbelow // all other rings stay the same
            r.pole' = r.pole
        }
        r1.pole' != r1.pole
    }
}

// Allows for a transition where nothing is changed. Need this to ensure counter
// is able to stop in lasso trace.
pred MdoNothing {
    MCounter.Mcounter' = MCounter.Mcounter
    all r: MRing | r.Mbelow' = r.Mbelow and r.pole' = r.pole
    all t: MTower | t.Mtop' = t.Mtop
}

// Makes a move, then ensures counter increments.
pred MtotalMoves {
    Mmove
    MCounter.Mcounter' = add[MCounter.Mcounter, 1]
}

// The end state, when the puzzle is satisfied. All rings should end up in the
// ending tower. All other towers should not have any top rings.
pred MendState {
    MEndingTower.Mtop->(MRing - MEndingTower.Mtop) in ^Mbelow
    some MEndingTower.Mtop
    all t: MTower | (t != MEndingTower) implies no t.Mtop
    all r: MRing | r.pole = MEndingTower.tpole
}

// A trace that solves the puzzle from init to endState
pred Mtrace {
    Minit and always Mwellformed and always {MtotalMoves or MdoNothing} and eventually MendState
}

// RUN STATEMENTS

// Minimum moves: 1 
// run {Mtrace} for exactly 1 MRing, 3 MTower
// Minimum moves: 4 
// run {Mtrace} for exactly 2 MRing, 3 MTower
// Minimum moves: 13
run {Mtrace} for exactly 3 MRing, 3 MTower, 5 Int
// Minimum moves: 7
// run {Mtrace} for exactly 3 MRing, 4 MTower