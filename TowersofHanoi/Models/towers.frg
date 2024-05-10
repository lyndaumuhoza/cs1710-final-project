#lang forge/temporal

option max_tracelength 16
option min_tracelength 1

// Tower sig keeps track of the top ring in the stack 
abstract sig Tower {
    var top: lone Ring
}

// Starting tower is where all rings start
// Mid towers is intermediate, used as temporary place to put rings
// Ending tower is where all the rings should get to
one sig StartingTower, MidTower, EndingTower extends Tower{}

// Ring keeps track of the ring immediately below it.
abstract sig Ring {
    var below: lone Ring // order on stack valid if top ring is bigger
}

// Expect three rings. Size order goes from 1 to 2 to 3.
one sig Ring1, Ring2, Ring3 extends Ring {}

// Sets the initial order of rings in the starting tower, and ensures no other
// tower has a top ring.
pred init {
    // enforcing linearity
    Ring1.below = Ring2
    Ring2.below = Ring3
    no Ring3.below 
    StartingTower.top = Ring1
    no MidTower.top
    no EndingTower.top 
    wellformed
}

// Ensures rings are in order. Ensures no ring's below points to itself.
pred wellformed {
    all r: Ring | r.below != r 
    Ring2.below != Ring1
    Ring3.below != Ring1 and Ring3.below != Ring2
}

// Defines the constraints to make a move. Two towers will have their tops changed
// to reflect this movement. All rings and towers uninvolved will stay the same.
pred move {
    //t1's top ring will be the next ring, t2's top ring will be t1's previous top ring
    some disj t1, t2, t3: Tower, r1: Ring {
        t1.top = r1
        t2.top' = r1
        r1.below' = t2.top
        t1.top' = r1.below 
        t3.top' = t3.top
        all r: Ring | r != r1 implies r.below' = r.below // all other rings stay the same
    }    
}

// The end state, when the puzzle is satisfied. All rings should end up in the
// ending tower in the correct order. All other rings should not have any top rings.
pred endState {
    Ring1.below = Ring2
    Ring2.below = Ring3
    no Ring3.below
    no StartingTower.top
    EndingTower.top = Ring1
    no MidTower.top
}

// A trace that solves the puzzle from init to endState and guarantees moves
// are wellformed
pred trace {
    init
    always wellformed
    always move
    eventually endState
}

// A trace that solves the puzzle from init to endState but does not guarantee
// moves are wellformed. Used for testing correspondence.
pred traceNotWell {
    init
    always move
    eventually endState
}


test expect {
    initSat: {init} is sat
    wellformedSat: {always wellformed} is sat
    moveSat: {always move} is sat 
    endSat: {eventually endState} is sat
}

run {trace} for exactly 3 Ring, 3 Tower