#lang forge/temporal


option max_tracelength 14
option min_tracelength 6

abstract sig BTower {
    var Btop: lone BRing
}
one sig BStartingTower, BMidTower, BEndingTower extends BTower{}

abstract sig BRing {
    var Bbelow: lone BRing, // order on stack valid if Btop BRing is bigger
    // specifying start color
    col: one Color
}

abstract sig Color {}
one sig Black, White extends Color{}

one sig BRing1, BRing2, BRing3 extends BRing {}

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

pred BendState {
    BRing1.Bbelow = BRing2
    BRing2.Bbelow = BRing3
    no BRing3.Bbelow
    no BStartingTower.Btop
    no BMidTower.Btop
    BEndingTower.Btop = BRing1
}

pred Btrace {
    Binit
    always Bwellformed
    always Bmove
    eventually BendState
}

pred BtraceNotWell {
    Binit
    always Bmove
    eventually BendState
}


// test expect {
//     initSat: {init} is sat
//     wellformedSat: {init and always wellformed and always move} is sat
//     moveSat: {always move} is sat 
//     endSat: {always wellformed and always move and eventually endState} is sat
// }

// test expect {
//     // total number of moves sould be 13
//     numberOfMoves: {totalMoves and Counter.counter = 13} for 5 Int is sat
// }

// run {init and always wellformed and always move and eventually endState} for exactly 3 Ring, 3 Tower, 2 Color
