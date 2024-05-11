#lang forge/temporal

open "magneticTowers.frg"

------------------------------------------------------------------------------
// TEST SUITE SIMILAR TO OTHER "magnetic.test.frg" FILE, BUT MADE TO WORK WITH
// HARD-CODED VERSION (TO VERIFY BOTH MODEL VERSIONS)
-------------------------------------------------------------------------------

// PREDICATES FOR TESTING INIT

// there is some ring whose below field links to itself
pred someRingsLinkToSelf {
    some r: MRing | r -> r in ^Mbelow
}
// all ring stacks (defined by below) follows the expected size constraint (defined by order)
pred allMRingInOrder {
    MRing1.Mbelow = MRing2
    MRing2.Mbelow = MRing3
    no MRing3.Mbelow
}
// the starting tower has some top ring
pred someStartingTop {
    some MStartingTower.Mtop
}
// all rings are in the starting tower
pred allRingInStartTower {
    MStartingTower.Mtop = MRing1
    MStartingTower.Mtop -> MRing2 in ^Mbelow
    MStartingTower.Mtop -> MRing3 in ^Mbelow
}
// there is one ring in the starting tower and no rings elsewhere
pred oneRingInStarting {
    some MStartingTower.Mtop
    all t: MTower | t.Mtop != MStartingTower.Mtop
    MRing1.pole = North
    MStartingTower.tpole = North
}
// all rings have the same polarity
pred allRingsMatchPolarity {
    all disj r1, r2: MRing | r1.pole = r2.pole
}

test suite for Minit {
    assert allMRingInOrder is necessary for Minit
    assert someStartingTop is necessary for Minit
    assert allRingInStartTower is necessary for Minit
    assert oneRingInStarting is sufficient for Minit

    test expect {
        // basic sat test
        initSat: {Minit} is sat
        // all rings match polarity at first 
        matchPolarity: {Minit implies allRingsMatchPolarity} is theorem
        // no cycles in below
        someCyclesInitUnsat: {Minit and someRingsLinkToSelf} is unsat
        // no rings makes init unsat
        noRingsInitUnsat: {#{MRing}=0 and Minit} is unsat

        // three rings where all are in starting tower, in order, with correct polarity
        initExThreeRing: {
            MStartingTower.Mtop = MRing1
            MRing1.Mbelow = MRing2
            MRing2.Mbelow = MRing3
            no MRing3.Mbelow
            MStartingTower.tpole = North
            MRing1.pole = North
            MRing2.pole = North
            MRing3.pole = North
            Minit
        } is sat

        // three rings where all are in starting tower, in order, but not with correct polarity
        initExThreeRingBadPole: {
            MStartingTower.Mtop = MRing1
            MRing1.Mbelow = MRing2
            MRing2.Mbelow = MRing3
            no MRing3.Mbelow
            MStartingTower.tpole = North
            MRing1.pole = South
            MRing2.pole = North
            MRing3.pole = South
            Minit
        } is unsat

        // two rings where all are in starting tower, with correct polarity, but not in order
        initExTwoRingUnordered: {
            MStartingTower.Mtop = MRing2
            MRing2.Mbelow = MRing1
            MRing1.Mbelow = MRing3
            no MRing3.Mbelow
            MStartingTower.tpole = North
            MRing1.pole = North
            MRing2.pole = North
            MRing3.pole = North
            Minit
        }  is unsat
    }
}

---------------------------------------------------

// PREDICATES FOR TESTING Mwellformed 

// no rings are stacked and all rings have the same polarity as the tower they are in
pred noMbelowsAndMatchTowers {
    no ^Mbelow
    all r: MRing | some t: MTower | {
        r = t.Mtop or t.Mtop -> r in ^Mbelow 
        t.tpole = r.pole
    }
}
// there are no rings in the model
pred noMRings {
    #{MRing} = 0
}
// there is a cycle between ring 1 and ring 2
pred someCycleInBelow {
    MRing1.Mbelow = MRing2
    MRing2.Mbelow = MRing1
}

test suite for Mwellformed {
    assert Mwellformed is necessary for Mtrace
    assert noMbelowsAndMatchTowers is sufficient for Mwellformed
    assert noMRings is sufficient for Mwellformed

    test expect {
        // basic sat test
        MwellformedSat: {Mwellformed} is sat
        // not possible to have cycles in below
        someCycleInBelowUnsat: {Mwellformed and someCycleInBelow} is unsat
        // Mwellformed example: MRings all in Morder but in diff towers
        MwellformedMRingDiffTower: {
            MStartingTower.Mtop = MRing1
            MMidTower.Mtop = MRing2
            MEndingTower.Mtop = MRing3
            no MRing1.Mbelow
            no MRing2.Mbelow
            no MRing3.Mbelow
            MStartingTower.tpole = North
            MRing1.pole = North
            MMidTower.tpole = South
            MRing2.pole = South
            MEndingTower.tpole = South
            MRing3.pole = South
            Mwellformed
        } is sat

        // Mwellformed example: MRings all in Morder and in same tower
        MwellformedFourMRingSameTower: {
            MMidTower.Mtop = MRing1
            MRing1.Mbelow = MRing2
            MRing2.Mbelow = MRing3
            no MRing3.Mbelow
            MMidTower.tpole = South
            MRing1.pole = South
            MRing2.pole = South
            MRing3.pole = South

            Mwellformed
        } is sat

        // not-Mwellformed example: MRings out of Morder
        notMwellformedOrder: {
            MStartingTower.Mtop = MRing1
            no MMidTower.Mtop 
            MEndingTower.Mtop = MRing3
            no MRing1.Mbelow
            no MRing2.Mbelow
            MRing3.Mbelow = MRing2
            MStartingTower.tpole = North
            MRing1.pole = North
            MMidTower.tpole = South
            MRing2.pole = South
            MEndingTower.tpole = South
            MRing3.pole = South
            Mwellformed
        } is unsat

        // not-Mwellformed example: MRings have incorrect polarity
        notMwellformedPolarity: {
            MStartingTower.Mtop = MRing1
            MMidTower.Mtop = MRing2
            MEndingTower.Mtop = MRing3
            no MRing1.Mbelow
            no MRing2.Mbelow
            no MRing3.Mbelow
            MStartingTower.tpole = North
            MRing1.pole = North
            MMidTower.tpole = South
            MRing2.pole = North
            MEndingTower.tpole = South
            MRing3.pole = South
            Mwellformed
        } is unsat
        
    }
}

// --------------------------------------------

// PREDICATES FOR TESTING Mmove

// some tower loses its top ring
pred oneMTowerDecMRing {
    some t: MTower | t.Mtop' = t.Mtop.Mbelow
}
// there are two towers for which the top of one became the top of the other
pred MRingMmoveDiffMTower {
    some disj t1, t2: MTower | t1.Mtop' = t2.Mtop
}
// assuming a move is made from initial stack, there is some ring who gets moved 
// onto another stack
pred onlyOneMRingMmove {
    Minit and Mmove implies {
        some r: MRing | {
            r.Mbelow' != r.Mbelow 
            all r1: MRing | r1 != r implies r1.Mbelow' = r1.Mbelow
        }
    }
}
// given a wellormed move, if there is no pre-defined order then there cannot be a stack
pred MorderPreserved {
    Mwellformed and Mmove implies {
        no MRing3.Mbelow 
        MRing2.Mbelow != MRing1
        all r: MRing | r -> r not in ^Mbelow
    }
}
// an example of moving ring from one tower to another
pred oneRingExMove {
    MStartingTower.tpole = North
    MMidTower.tpole = South
    MEndingTower.tpole = South

    no MRing1.Mbelow
    no MRing2.Mbelow
    no MRing3.Mbelow
    MStartingTower.Mtop = MRing1
    MMidTower.Mtop = MRing2
    MEndingTower.Mtop = MRing3
    MRing1.pole = North
    MRing2.pole = South
    MRing3.pole = South

    no MStartingTower.Mtop'
    MMidTower.Mtop' = MRing1
    MEndingTower.Mtop' = MRing3
    MRing1.Mbelow' = MRing2
    no MRing2.Mbelow'
    no MRing3.Mbelow'
    MRing1.pole' = South
    MRing2.pole' = South
    MRing3.pole' = South

}
// three towers' top ring changes at once
pred tooManyMTowersChange {
    some disj t1, t2, t3: MTower | {
        t1.Mtop' != t1.Mtop
        t2.Mtop' != t2.Mtop
        t3.Mtop' != t3.Mtop
    }
}
// a ring is flipped to change polarity 
pred oneRingFlipsOnMove {
    some r: MRing | {
        r.pole' != r.pole 
        all r1: MRing | r1 != r implies r1.pole' = r1.pole
    }
}

test suite for Mmove {
    assert oneMTowerDecMRing is necessary for Mmove
    assert MRingMmoveDiffMTower is necessary for Mmove
    assert onlyOneMRingMmove is necessary for Mmove
    assert MorderPreserved is necessary for Mmove
    assert oneRingFlipsOnMove is necessary for Mmove
    assert oneRingExMove is sufficient for Mmove

    test expect {
        // basic sat test
        MmoveSat: {Mmove} is sat
        // Mmove doesn't work with only one MTower
        MmoveOneMTower: {Mmove and #{MTower} = 1} is unsat
        // too many MTowers change Mtops
        threeMTowersChange: {Mmove and tooManyMTowersChange} is unsat

        // Mmove starting from Minitial stack
        MinitialMmoveEx: {
            MStartingTower.tpole = North
            MMidTower.tpole = South
            MEndingTower.tpole = South

            MStartingTower.Mtop = MRing1
            MRing1.Mbelow = MRing2
            MRing2.Mbelow = MRing3
            no MRing3.Mbelow
            MRing1.pole = North
            MRing2.pole = North
            MRing3.pole = North
            no MMidTower.Mtop
            no MEndingTower.Mtop

            MStartingTower.Mtop' = MRing2
            MMidTower.Mtop' = MRing1
            no MEndingTower.Mtop'
            no MRing1.Mbelow'
            MRing2.Mbelow' = MRing3
            no MRing3.Mbelow'
            MRing1.pole' = South
            MRing2.pole' = North
            MRing3.pole' = North

            Minit
            Mmove
        } is sat

        // basic Mmove moving smallest MRing onto largest MRing
        basicMmoveEx: {
            MStartingTower.tpole = North
            MMidTower.tpole = South
            MEndingTower.tpole = South

            MStartingTower.Mtop = MRing1
            MMidTower.Mtop = MRing2
            MEndingTower.Mtop = MRing3
            no MRing1.Mbelow
            no MRing2.Mbelow
            no MRing3.Mbelow
            MRing1.pole = North
            MRing2.pole = South
            MRing3.pole = South

            no MStartingTower.Mtop'
            MMidTower.Mtop' = MRing2
            MEndingTower.Mtop' = MRing1
            MRing1.Mbelow' = MRing3
            no MRing2.Mbelow'
            no MRing3.Mbelow'
            MRing1.pole' = South
            MRing2.pole' = South
            MRing3.pole' = South

            Mmove
        } is sat

        // Mmove resulting in end state
        endingMmoveEx: {
            MStartingTower.tpole = North
            MMidTower.tpole = South
            MEndingTower.tpole = South

            MStartingTower.Mtop = MRing1
            no MMidTower.Mtop
            MEndingTower.Mtop = MRing2
            no MRing1.Mbelow
            MRing2.Mbelow = MRing3
            no MRing3.Mbelow
            MRing1.pole = North
            MRing2.pole = South
            MRing3.pole = South

            no MStartingTower.Mtop'
            no MMidTower.Mtop'
            MEndingTower.Mtop' = MRing1
            MRing1.Mbelow' = MRing2
            MRing2.Mbelow' = MRing3
            no MRing3.Mbelow'
            MRing1.pole' = South
            MRing2.pole' = South
            MRing3.pole' = South

            Mmove
            next_state MendState
        } is sat
    }
}

--------------------------------------------

// PREDICATES FOR TESTING MendState 

// all rings are stacked in the ending tower
pred allMRingsInEndMTower {
    MEndingTower.Mtop = MRing1
    MRing1.Mbelow = MRing2
    MRing2.Mbelow = MRing3
}
// given a trace, it is expected that all rings are in order
pred traceMustEndInMorder {
    {Minit and always Mmove and eventually MendState} implies allMRingInOrder
}
// there is some ring in the starting tower
pred someMRingInStarting {
    some r: MRing | MStartingTower.Mtop = r
}
// there is some ring in the ending tower
pred someMRingInEndingMtop {
    some MEndingTower.Mtop
}
// there is exactly one ring in the ending tower with the correct polarity
pred oneMRingInEnding {
    some MEndingTower.Mtop
    all t: MTower | t.Mtop != MEndingTower.Mtop
    all r: MRing | r.pole = MEndingTower.tpole
}
// all rings match the polarity of the ending tower
pred allRingsMatchEndPolarity {
   {Minit and always Mmove and eventually MendState} implies {all r: MRing | r.pole = MEndingTower.tpole}
}

test suite for MendState {
    assert allMRingsInEndMTower is necessary for MendState
    assert traceMustEndInMorder is necessary for MendState
    assert someMRingInEndingMtop is necessary for MendState
    assert allRingsMatchEndPolarity is necessary for MendState
    assert oneMRingInEnding is sufficient for MendState

    test expect {
        // basic sat test
        MendStateSat: {MendState} is sat
        // some MRing in other MTower
        MRingInStarting: {someMRingInStarting and MendState} is unsat
        // no MRings means MendState is unsat
        noMRingsEndSat: {noMRings and MendState} is unsat
        // three MRings where all are in ending MTower and in Morder
        MendStateExThreeMRing: {
            MStartingTower.tpole = North
            MMidTower.tpole = South
            MEndingTower.tpole = South

            no MStartingTower.Mtop
            no MMidTower.Mtop
            MEndingTower.Mtop = MRing1
            MRing1.Mbelow = MRing2
            MRing2.Mbelow = MRing3
            no MRing3.Mbelow
            MRing1.pole = South
            MRing2.pole = South
            MRing3.pole = South
            MendState
        } is sat

        // three MRings where all are in ending MTower but not in order 
        MendStateRingUnordered: {
            MStartingTower.tpole = North
            MMidTower.tpole = South
            MEndingTower.tpole = South

            no MStartingTower.Mtop
            no MMidTower.Mtop
            MEndingTower.Mtop = MRing1
            MRing1.Mbelow = MRing3
            MRing3.Mbelow = MRing2
            no MRing2.Mbelow
            MRing1.pole = South
            MRing2.pole = South
            MRing3.pole = South
            MendState
        } is unsat


        // three MRings where all are in ending MTower but polarity is bad
        // (sat but don't expect this in a trace)
        MendStateBadPolarity: {
            MStartingTower.tpole = North
            MMidTower.tpole = South
            MEndingTower.tpole = South

            no MStartingTower.Mtop
            no MMidTower.Mtop
            MEndingTower.Mtop = MRing1
            MRing1.Mbelow = MRing2
            MRing2.Mbelow = MRing3
            no MRing3.Mbelow
            MRing1.pole = North
            MRing2.pole = South
            MRing3.pole = South
            MendState
        } is sat
    }

}

--------------------------------------------

// PREDICATES FOR TESTING TRACE

// the size order is always maintined
pred orderAlwaysPreserved {
    always {
        no MRing3.Mbelow 
        MRing2.Mbelow != MRing1
        all r: MRing | r -> r not in ^Mbelow
    }
}
// all rings end up in the end tower eventually
pred ringsEndAtEndingTower {
    eventually some MEndingTower.Mtop 
    eventually {all r: MRing | r != MEndingTower.Mtop implies MEndingTower.Mtop -> r in ^Mbelow}
}
// all rings start out at the starting tower
pred ringsStartAtStartingTower {
    some MStartingTower.Mtop
    all r: MRing | r != MStartingTower.Mtop implies MStartingTower.Mtop -> r in ^Mbelow
}
// a move always guarantees that some ring is moved to a different stack
pred oneRingMove {
    always {
        Mmove implies {
            some r: MRing | some r.Mbelow implies r.Mbelow' != r.Mbelow
        }
    }
}
// a move always guarantees that some ring flips polarity
pred oneRingChangePolarity {
    always {
        Mmove implies {
            some r: MRing | some r.Mbelow implies r.pole' != r.pole
        }
    }
}
// the counter always increment on a move, and stays the same when doing nothing
pred multipleRingsMove {
    some disj r1, r2: MRing | r1.Mbelow' != r1.Mbelow and r2.Mbelow' != r2.Mbelow
}
// multiple rings change their polarity at once
pred multipleRingsChangePolarity {
    some disj r1, r2: MRing | r1.pole' != r1.pole and r2.pole' != r2.pole

}
// there are fewer than 3 towers, and more than 1 ring in the model
pred minTowers3 {
    #{MTower} < 3
    #{MRing} > 1
}
// eventually the first ring ends up on the third ring
pred firstRingOnTopofThird {
    eventually {
        MRing1.Mbelow = MRing3
    }
}
// eventually there is one ring per tower
pred ringsSpreadOut {
    eventually {
        some disj r1, r2, r3: MRing | no r1.Mbelow and no r2.Mbelow and no r3.Mbelow
    }
}

test suite for Mtrace {
    assert orderAlwaysPreserved is necessary for Mtrace
    assert ringsEndAtEndingTower is necessary for Mtrace
    assert ringsStartAtStartingTower is necessary for Mtrace
    assert oneRingMove is necessary for Mtrace
    assert oneRingChangePolarity is necessary for Mtrace

    test expect {
        // basic sat test
        traceSat: {Mtrace} is sat
        // minimum number of towers needed for our model is 3
        minTowersTwo: {Mtrace and minTowers3} is unsat
        // multiple rings move at a time is invalid
        multRingsMove: {Mtrace and multipleRingsMove} is unsat
        // multiple rings change polarity is invalid
        multRingsFlip: {Mtrace and multipleRingsChangePolarity} is unsat
        // possible to stack first ring on top of third
        firstOnThird: {Mtrace and firstRingOnTopofThird} is sat
        // possible to have ringsSpreadOut 
        ringsAreSpreadOut: {Mtrace and ringsSpreadOut} is sat
    }
}