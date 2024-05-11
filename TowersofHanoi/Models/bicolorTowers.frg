#lang forge/temporal


option max_tracelength 16
option min_tracelength 6

// Tower sig keeps track of the top ring in the stack
abstract sig BTower {
    var Btop: lone BRing
}

// Starting tower is where all rings start
// Ending tower is where all the rings should get to
one sig BStartingTower, BMidTower, BEndingTower extends BTower{}

// Ring keeps track of the ring immediately below it and its color 
// (which never changes)
abstract sig BRing {
    var Bbelow: lone BRing, // order on stack valid if Btop BRing is bigger
    // specifying start color
    col: one Color
}

// Sigs for assigning color to ring
abstract sig Color {}
one sig Black, White extends Color{}

// Expect three rings. Size order goes from 1 to 2 to 3.
one sig BRing1, BRing2, BRing3 extends BRing {}


// Sets the initial order of rings in the starting tower, and ensures no other
// tower has a top ring. Also constrains ring colors to be alternating.
pred Binit {
    // enforcing linearity
    BRing1.Bbelow = BRing2
    BRing2.Bbelow = BRing3
    no BRing3.Bbelow 
    BStartingTower.Btop = BRing1
    no BMidTower.Btop
    no BEndingTower.Btop 

    //Initial BRing color
    BRing1.col = Black
    BRing2.col = White
    BRing3.col = Black
}

// Ensures rings are always in order, and that any ring does not have the same color as
// the ring below it.
pred Bwellformed {
    all r: BRing | {
        r.Bbelow != r 
        some r.Bbelow implies {
            // (r.pole = North implies r.Bbelow.pole = North) and (r.pole = South implies r.Bbelow.pole = South)
            r.col != r.Bbelow.col
        }
    }

    BRing2.Bbelow != BRing1
    BRing3.Bbelow != BRing1 and BRing3.Bbelow != BRing2
}

// Defines the constraints to make a move. Two towers will have their tops changed
// to reflect this movement. 
pred Bmove {
    //t1's Btop BRing will be the next ring, t2's Btop BRing will be t1's previous Btop ring
    some disj t1, t2, t3: BTower, r1: BRing {
        t1.Btop = r1
        t2.Btop' = r1
        r1.Bbelow' = t2.Btop
        t1.Btop' = r1.Bbelow 
        t3.Btop' = t3.Btop
        all r: BRing | {
            r != r1 implies {
                r.Bbelow' = r.Bbelow // all other rings stay the same
            }
        }
    }    
}

// The end state, when the puzzle is satisfied. All rings should end up in the
// ending tower. All other towers should not have any top rings.
pred BendState {
    BRing1.Bbelow = BRing2
    BRing2.Bbelow = BRing3
    no BRing3.Bbelow
    no BStartingTower.Btop
    no BMidTower.Btop
    BEndingTower.Btop = BRing1
}

// A trace that solves the puzzle from init to endState and is always guaranteed
// to be wellformed.
pred Btrace {
    Binit
    always Bwellformed
    always Bmove
    eventually BendState
}

// A trace that gets from init to endState but moves are not guaranteed to be
// wellformed. Used for testing correspondence.
pred BtraceNotWell {
    Binit
    always Bmove
    eventually BendState
}

test expect {
    initSat: {Binit} is sat
    wellformedSat: {Binit and always Bwellformed and always Bmove} is sat
    moveSat: {always Bmove} is sat 
    endSat: {always Bwellformed and always Bmove and eventually BendState} is sat
}


run {Btrace} for exactly 3 BRing, 3 BTower, 2 Color
