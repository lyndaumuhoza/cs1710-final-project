#lang forge/temporal

open "bicolorGeneric.frg"

---------------------------------------------------

// PREDICATES FOR TESTING INIT

pred someRingsLinkToSelf {
    some iden & ^Border
}
pred someRingsLinkToSelfBelow {
    some iden & ^Bbelow
}
pred allRingInOrder {
    all r: BRing | some r.Bbelow implies r->r.Bbelow in ^Border
}
pred someStartingTop {
    some BStartingTower.Btop
}
pred allRingInStartTower {
    all r: BRing | r != BStartingTower.Btop implies BStartingTower.Btop -> r in ^Border
}
pred oneRingInStarting {
    #{BRing} = 1 and some BStartingTower.Btop
    all t: BTower | t.Btop != BStartingTower.Btop
}

pred allRingsMatchColor {
    all disj r1, r2: BRing | r1.col = r2.col
}

test suite for Binit {
    assert allRingInOrder is necessary for Binit
    assert someStartingTop is necessary for Binit
    assert allRingInStartTower is necessary for Binit
    assert oneRingInStarting is sufficient for Binit

    test expect {
        // basic sat test
        initSat: {Binit} is sat
        // all rings match color at first
        matchcolor: {Binit implies allRingsMatchColor} is theorem
        // no cycles in order
        someCyclesInitUnsat: {Binit and someRingsLinkToSelf} is unsat
        // no cycles in below
        someBelowCyclesInitUnsat: {Binit and someRingsLinkToSelfBelow} is unsat
        // no rings makes init unsat
        noRingsInitUnsat: {#{BRing}=0 and Binit} is unsat
    }

}


test suite for wellformed {

}

test suite for move {

}

test suite for endState {
    
}