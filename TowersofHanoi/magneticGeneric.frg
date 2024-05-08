#lang forge/temporal

option max_tracelength 14
option min_tracelength 6

// MAGNETIC 
abstract sig Polarity {}
one sig North, South extends Polarity{}

sig MTower {
    var Mtop: lone MRing,
    tpole: one Polarity
}

one sig MStartingTower, MEndingTower, MMidTower extends MTower{}


sig MRing {
    var Mbelow: lone MRing, // order on stack valid if top ring is bigger
    Morder: lone MRing,
    var pole: one Polarity
}

pred MinitialOrder {
    MStartingTower.Mtop->(MRing - MStartingTower.Mtop) in ^Morder
    MStartingTower.Mtop->(MRing - MStartingTower.Mtop) in ^Mbelow
    not {some iden & ^Morder}
    all r:MRing | r.pole = MStartingTower.tpole
    // no cycles
    ^Mbelow in ^Morder
}

pred Minit {
    // linearity
    MinitialOrder
    some MStartingTower.Mtop
    all t: MTower | (t != MStartingTower) implies no t.Mtop
}

pred Mwellformed {
    // below must always follow the same sequence set by order
    {^Mbelow in ^Morder}

    all r: MRing | {
        some r.Mbelow implies {
            r.pole = r.Mbelow.pole
        }
        no r.Mbelow implies {
            some t:MTower | {
                r = t.Mtop or t.Mtop -> r in ^Mbelow 
                t.tpole = r.pole
            }
        }
    }
}

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
        all t:MTower | (t != t1 and t != t2) implies t.Mtop' = t.Mtop
        all r: MRing | r != r1 implies { 
            r.Mbelow' = r.Mbelow // all other rings stay the same
            r.pole' = r.pole
        }
        r1.pole' != r1.pole
    }
}

pred MmoveNotWell {
    some disj t1, t2:MTower, r1:MRing {
        t1.Mtop = r1
        t2.Mtop' = r1
        r1.Mbelow' = t2.Mtop
        t1.Mtop' = r1.Mbelow 
        all t:MTower | (t != t1 and t != t2) implies t.Mtop' = t.Mtop
        all r: MRing | r != r1 implies { 
            r.Mbelow' = r.Mbelow // all other rings stay the same
            r.pole' = r.pole
        }
        r1.pole' != r1.pole
    }
}

pred MendState {
    MEndingTower.Mtop->(MRing - MEndingTower.Mtop) in ^Mbelow
    some MEndingTower.Mtop
    all t: MTower | (t != MEndingTower) implies no t.Mtop
}

pred Mtrace {
    Minit and always Mwellformed and always Mmove and eventually MendState 
}

pred MtraceNotWell {
    Minit and always MmoveNotWell and eventually MendState 
}

run {Mtrace} for exactly 3 MRing, 3 MTower