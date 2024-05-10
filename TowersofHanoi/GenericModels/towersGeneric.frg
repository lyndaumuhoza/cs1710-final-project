#lang forge/temporal


option max_tracelength 20
option min_tracelength 1

// Tower sig keeps track of the top ring in the stack 
sig Tower {
    var top: lone Ring
}

// Starting tower is where all rings start
// Ending tower is where all the rings should get to
one sig StartingTower, EndingTower extends Tower{}

// Ring keeps track of the ring immediately below it and the proper size order of rings 
// (which never changes). Order points to the next biggest Ring.
sig Ring {
    var below: lone Ring, // order on stack valid if top ring is bigger
    order: lone Ring
}

// Counter keeps track of how many moves are made
one sig Counter {
  var counter: one Int // counter for the number of moves
}

// Establishes the proper size order of rings and forces all rings in the starting
// tower to be in order. No cycles allowed in the stack.
pred initialOrder {
    StartingTower.top->(Ring - StartingTower.top) in ^order
    StartingTower.top->(Ring - StartingTower.top) in ^below
    not {some iden & ^order}
    ^below in ^order
}

// Sets the initial order of rings in the starting tower, and ensures no other
// tower has a top ring.
pred init {
    // linearity
    initialOrder
    some StartingTower.top
    all t: Tower | (t != StartingTower) implies no t.top
    Counter.counter = 0
}

// Ensures rings are always in order
pred wellformed {
    // below must always follow the same sequence set by order
    {^below in ^order}
}

// Defines the constraints to make a move. Two towers will have their tops changed
// to reflect this movement. The ring cannot be stacked onto a ring out of order 
// (meaning a ring that is smaller than it).
pred move {
    some disj t1, t2: Tower, r1: Ring {
        t1.top = r1
        t2.top' = r1
        r1.below' = t2.top
        t1.top' = r1.below 
        some r1.below' implies r1 -> r1.below' in ^order
        all t: Tower | (t != t1 and t != t2) implies t.top' = t.top
        all r: Ring | r != r1 implies r.below' = r.below // all other rings stay the same
    }
}

// Allows for a transition where nothing is changed. Need this to ensure counter
// is able to stop in lasso trace.
pred doNothing {
    Counter.counter' = Counter.counter
    all r: Ring | r.below' = r.below
    all t: Tower | t.top' = t.top
}

// Makes a move, then ensures counter increments.
pred totalMoves {
    move
    Counter.counter' = add[Counter.counter, 1]
}

// The end state, when the puzzle is satisfied. All rings should end up in the
// ending tower. All other rings should not have any top rings.
pred endState {
    EndingTower.top->(Ring - EndingTower.top) in ^below
    some EndingTower.top
    all t: Tower | (t != EndingTower) implies no t.top
}

// A trace that solves the puzzle from init to endState
pred trace {
    init and always wellformed and always {totalMoves or doNothing} and eventually endState
}

// RUN STATEMENTS 

// Minimum moves: 1 
// run {trace} for exactly 1 Ring, 3 Tower
// Minimum moves: 3
// run {trace} for exactly 2 Ring, 3 Tower
// Minimum moves: 7
run {trace} for exactly 3 Ring, 3 Tower
// Minimum moves: 15 (this one will take 3-4 min)
// run {trace} for exactly 4 Ring, 3 Tower, 5 Int
// Minimum moves: 5
// run {trace} for exactly 3 Ring, 4 Tower
// Minimum moves: 9
// run {trace} for exactly 4 Ring, 4 Tower
