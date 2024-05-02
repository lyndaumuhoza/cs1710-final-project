#lang forge/temporal


option max_tracelength 13
option min_tracelength 6

abstract sig Tower {
    var top: lone Ring
}
one sig StartingTower, BasicTower, EndingTower extends Tower{}

abstract sig Ring {
    var below: lone Ring // order on stack valid if top ring is bigger
}

one sig Ring1, Ring2, Ring3 extends Ring {}

one sig Counter {
//   var counter: set Move // counter for the number of moves
    var counter: one Int
}

sig Move {}

pred init {
    // enforcing linearity
    Ring1.below = Ring2
    Ring2.below = Ring3
    no Ring3.below 
    StartingTower.top = Ring1
    no BasicTower.top
    no EndingTower.top 
    // #{Counter.counter} = 0
    // Counteer.counter = 0
}

pred wellformed {
    all r: Ring | r.below != r 
    Ring2.below != Ring1
    Ring3.below != Ring1 and Ring3.below != Ring2
}

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

pred totalMoves {
    // I put this in a separate predicate becuase it was harder to debug within move
    move
    // some m: Move | m not in Counter.counter and Counter.counter' = Counter.counter + m
    Counter.counter' = add[Counter.counter, 1]
}

pred endState {
    Ring1.below = Ring2
    Ring2.below = Ring3
    no Ring3.below
    no StartingTower.top
    EndingTower.top = Ring1
}

pred trace {
    init
    always wellformed
    always move
    eventually endState
}


test expect {
    initSat: {init} is sat
    wellformedSat: {always wellformed} is sat
    moveSat: {always move} is sat 
    endSat: {eventually endState} is sat
    // endSat2: {init and always wellformed and always totalMoves and eventually endState} is sat
}

// test expect {
//     // total number of moves sould be 7, 2^n-1, where n = 3, counter.counter/2
//     numberOfMoves: {init and always wellformed and always totalMoves and eventually {endState and Counter.counter = 14}} is sat
// }

run {init and always wellformed and always move and eventually endState} for exactly 3 Ring, 3 Tower