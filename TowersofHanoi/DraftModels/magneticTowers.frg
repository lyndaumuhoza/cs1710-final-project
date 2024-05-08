#lang forge/temporal


option max_tracelength 14
option min_tracelength 6

abstract sig MTower {
    var Mtop: lone MRing,
    tpole: one Polarity
}
one sig MStartingTower, MMidTower, MEndingTower extends MTower{}

abstract sig MRing {
    var Mbelow: lone MRing, // order on stack valid if top ring is bigger
    // specifying polarity
    var pole: one Polarity
}

abstract sig Polarity {}
one sig North, South extends Polarity{}

one sig MRing1, MRing2, MRing3 extends MRing {}

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

pred MendState {
    MRing1.Mbelow = MRing2
    MRing2.Mbelow = MRing3
    no MRing3.Mbelow
    no MStartingTower.Mtop
    no MMidTower.Mtop
    MEndingTower.Mtop = MRing1
}

pred Mtrace {
    Minit
    always Mwellformed
    always Mmove
    eventually MendState
}

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

// test expect {
//     // total number of moves sould be 13
//     numberOfMoves: {totalMoves and Counter.counter = 13} for 5 Int is sat
// }

// run {init and always wellformed and always move and eventually endState} for exactly 3 Ring, 3 Tower, 2 Polarity
