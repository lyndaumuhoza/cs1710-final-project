#lang forge/temporal


option max_tracelength 13
option min_tracelength 6

abstract sig Tower2 {
    var top2: lone RingD
}
one sig StartingTower2, BasicTower2, EndingTower2 extends Tower2{}

abstract sig RingD {
    var below2: lone RingD // order on stack valid if top2 ring is bigger
}

one sig RingA, RingB, RingC extends RingD {}

one sig counter22 {
  var counter2: one Int // counter2 for the number of moves
}

pred init2 {
    // enforcing linearity
    RingA.below2 = RingB
    RingB.below2 = RingC
    no RingC.below2 
    StartingTower2.top2 = RingA
    no BasicTower2.top2
    no EndingTower2.top2 
}

pred wellformed2 {
    all r: RingD | r.below2 != r 
    RingB.below2 != RingA
    RingC.below2 != RingA and RingC.below2 != RingB
}

pred move2 {
    //t1's top2 ring will be the next ring, t2's top2 ring will be t1's previous top2 ring
    some disj t1, t2, t3: Tower2, r1: RingD {
        t1.top2 = r1
        t2.top2' = r1
        r1.below2' = t2.top2
        t1.top2' = r1.below2 
        t3.top2' = t3.top2
        all r: RingD | r != r1 implies r.below2' = r.below2 // all other rings stay the same
    }    
}

pred totalMoves2 {
    // I put this in a separate predicate becuase it was harder to debug within move
    move
    counter22.counter2' = add[counter22.counter2, 1]
}

pred endState2 {
    RingA.below2 = RingB
    RingB.below2 = RingC
    no RingC.below2
    no StartingTower2.top2
    EndingTower2.top2 = RingA
}

pred trace2 {
    init2
    always wellformed2
    always move2
    eventually endState2
}

// test expect {
//     initSat: {init} is sat
//     wellformedSat: {always wellformed} is sat
//     moveSat: {always move} is sat 
//     endSat: {eventually endState} is sat
// }

// test expect {
//     // total number of moves sould be 7, 2^n-1, where n = 3 
//     numberOfMoves: {totalMoves and counter22.counter2 = 7} is sat
// }
// run {init and always wellformed and always move and eventually endState} for exactly 3 RingD, 3 Tower2