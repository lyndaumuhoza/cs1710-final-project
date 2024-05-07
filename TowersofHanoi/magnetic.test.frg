#lang forge/temporal

open "magneticGeneric.frg"

---------------------------------------------------

// PREDICATES FOR TESTING INIT

pred someRingsLinkToSelf {
    some iden & ^Morder
}
pred someRingsLinkToSelfBelow {
    some iden & ^Mbelow
}
pred allRingInOrder {
    all r: MRing | some r.Mbelow implies r->r.Mbelow in ^Morder
}
pred someStartingTop {
    some MStartingTower.Mtop
}
pred allRingInStartTower {
    all r: MRing | r != MStartingTower.Mtop implies MStartingTower.Mtop -> r in ^Morder
}
pred oneRingInStarting {
    #{MRing} = 1 and some MStartingTower.Mtop
    all t: MTower | t.Mtop != MStartingTower.Mtop
}
pred allRingsMatchPolarity {
    all disj r1, r2: MRing | r1.pole = r2.pole
}

test suite for Minit {
    assert allRingInOrder is necessary for Minit
    assert someStartingTop is necessary for Minit
    assert allRingInStartTower is necessary for Minit
    assert oneRingInStarting is sufficient for Minit

    test expect {
        // basic sat test
        initSat: {Minit} is sat
        // all rings match polarity at first 
        matchPolarity: {Minit implies allRingsMatchPolarity} is theorem
        // no cycles in order
        someCyclesInitUnsat: {Minit and someRingsLinkToSelf} is unsat
        // no cycles in below
        someBelowCyclesInitUnsat: {Minit and someRingsLinkToSelfBelow} is unsat
        // no rings makes init unsat
        noRingsInitUnsat: {#{MRing}=0 and Minit} is unsat
    }
}

test suite for Mwellformed {

}

test suite for Mmove {

}

test suite for MendState {
    
}