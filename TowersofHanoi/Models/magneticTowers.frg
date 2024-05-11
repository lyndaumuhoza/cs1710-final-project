#lang forge/temporal


option max_tracelength 16
option min_tracelength 6

// Sigs for tracking which pole is faced up
abstract sig Polarity {}
one sig North, South extends Polarity{}

// Tower sig keeps track of the top ring in the stack and its own polarity
abstract sig MTower {
    var Mtop: lone MRing,
    tpole: one Polarity
}

// Starting tower is where all rings start
// Ending tower is where all the rings should get to
one sig MStartingTower, MMidTower, MEndingTower extends MTower{}

// Ring keeps track of the ring immediately below it and its polarity 
// (which changes on every move)
abstract sig MRing {
    var Mbelow: lone MRing, // order on stack valid if top ring is bigger
    // specifying polarity
    var pole: one Polarity
}


// Expect three rings. Size order goes from 1 to 2 to 3.
one sig MRing1, MRing2, MRing3 extends MRing {}

// Sets the initial order of rings in the starting tower, and ensures no other
// tower has a top ring. Also constrains starting polarity of towers.
pred Minit {
    // enforcing linearity
    MRing1.Mbelow = MRing2
    MRing2.Mbelow = MRing3
    no MRing3.Mbelow 
    MStartingTower.Mtop = MRing1
    no MMidTower.Mtop
    no MEndingTower.Mtop 

    //Starting polarity of towers
    MStartingTower.tpole = North
    MMidTower.tpole = South 
    MEndingTower.tpole = South

    //Initial Ring Polarity
    MRing1.pole = North
    MRing2.pole = North
    MRing3.pole = North

    Mwellformed
}

// Ensures rings are always in order, and that any ring has the same polarity as
// the ring below it, or has the same polarity as the tower it is in if there is 
// no ring below it.
pred Mwellformed {
    all r: MRing | {
        r.Mbelow != r 
        some r.Mbelow implies {
            // (r.pole = North implies r.below.pole = North) and (r.pole = South implies r.below.pole = South)
            r.pole = r.Mbelow.pole
        }
        no r.Mbelow implies {
            some t: MTower | {
            r = t.Mtop or t.Mtop -> r in ^Mbelow 
            t.tpole = r.pole
        }
        }
    }

    MRing2.Mbelow != MRing1
    MRing3.Mbelow != MRing1 and MRing3.Mbelow != MRing2
}

// Defines the constraints to make a move. Two towers will have their tops changed
// to reflect this movement. The ring moving has to flip its polarity.
pred Mmove {
    //t1's top ring will be the next ring, t2's top ring will be t1's previous top ring
    some disj t1, t2, t3: MTower, r1: MRing {
        t1.Mtop = r1
        t2.Mtop' = r1
        r1.Mbelow' = t2.Mtop
        t1.Mtop' = r1.Mbelow 
        t3.Mtop' = t3.Mtop
        all r: MRing | {
            r != r1 implies {
                r.Mbelow' = r.Mbelow // all other rings stay the same
                r.pole' = r.pole
            }
        }

        r1.pole = North implies r1.pole' = South
        r1.pole = South implies r1.pole' = North
    }    
}

// The end state, when the puzzle is satisfied. All rings should end up in the
// ending tower. All other towers should not have any top rings.
pred MendState {
    MRing1.Mbelow = MRing2
    MRing2.Mbelow = MRing3
    no MRing3.Mbelow
    no MStartingTower.Mtop
    no MMidTower.Mtop
    MEndingTower.Mtop = MRing1
}

// A trace that solves the puzzle from init to endState and is always guaranteed
// to be wellformed.
pred Mtrace {
    Minit
    always Mwellformed
    always Mmove
    eventually MendState
}

// A trace that gets from init to endState but moves are not guaranteed to be
// wellformed. Used for testing correspondence.
pred MtraceNotWell {
    Minit
    always Mmove
    eventually MendState
}

test expect {
    initSat: {Minit} is sat
    wellformedSat: {Minit and always Mwellformed and always Mmove} is sat
    moveSat: {always Mmove} is sat 
    endSat: {always Mwellformed and always Mmove and eventually MendState} is sat
}

run {Mtrace} for exactly 3 MRing, 3 MTower, 2 Polarity
