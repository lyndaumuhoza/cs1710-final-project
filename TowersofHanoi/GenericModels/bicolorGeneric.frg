#lang forge/temporal

option max_tracelength 20
option min_tracelength 6

// BICOLOR 
abstract sig Color {}
one sig Black, White extends Color{}

sig BTower {
    var Btop: lone BRing
}

one sig BStartingTower, BEndingTower extends BTower{}


sig BRing {
    var Bbelow: lone BRing, // order on stack valid if top ring is bigger
    Border: lone BRing,
    col: one Color
}

pred BinitialOrder {
    BStartingTower.Btop->(BRing - BStartingTower.Btop) in ^Border
    BStartingTower.Btop->(BRing - BStartingTower.Btop) in ^Bbelow
    not {some iden & ^Border}
    all r: BRing | some r.Bbelow implies r.col != r.Bbelow.col
    // no cycles
    ^Bbelow in ^Border
}

pred Binit {
    // linearity
    BinitialOrder
    some BStartingTower.Btop
    all t: BTower | (t != BStartingTower) implies no t.Btop
}

pred Bwellformed {
    // below must always follow the same sequence set by order
    {^Bbelow in ^Border}

    all r: BRing | {
        some r.Bbelow implies {
            r.col != r.Bbelow.col
        }
        // no r.Bbelow implies {
        //     some t:BTower | {
        //         r = t.Btop or t.Btop -> r in ^Bbelow 
        //     }
        // }
    }
}

pred Bmove {
    some disj t1, t2:BTower, r1:BRing {
        t1.Btop = r1
        t2.Btop' = r1
        r1.Bbelow' = t2.Btop
        t1.Btop' = r1.Bbelow 
        some r1.Bbelow' implies {
            r1 -> r1.Bbelow' in ^Border
            r1.col != r1.Bbelow'.col
        }
        all t:BTower | (t != t1 and t != t2) implies t.Btop' = t.Btop
        all r: BRing | r != r1 implies { 
            r.Bbelow' = r.Bbelow // all other rings stay the same
        }
    }
}

pred BmoveNotWell {
    some disj t1, t2:BTower, r1:BRing {
        t1.Btop = r1
        t2.Btop' = r1
        r1.Bbelow' = t2.Btop
        t1.Btop' = r1.Bbelow 
        all t:BTower | (t != t1 and t != t2) implies t.Btop' = t.Btop
        all r: BRing | r != r1 implies { 
            r.Bbelow' = r.Bbelow // all other rings stay the same
        }
    }
}

pred BendState {
    BEndingTower.Btop->(BRing - BEndingTower.Btop) in ^Bbelow
    some BEndingTower.Btop
    all t: BTower | (t != BEndingTower) implies no t.Btop
}

pred Btrace {
    Binit and always Bwellformed and always Bmove and eventually BendState 
}

pred BtraceNotWell {
    Binit and always BmoveNotWell and eventually BendState 
}

run {Btrace} for exactly 3 BRing, 3 BTower