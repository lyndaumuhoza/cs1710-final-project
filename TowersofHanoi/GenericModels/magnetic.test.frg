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
pred allMRingInOrder {
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
    assert allMRingInOrder is necessary for Minit
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

        // three rings where all are in starting tower, in order, with correct polarity
        initExThreeRing: {
            some disj r1, r2, r3: MRing | {
                r1.Mbelow = r2 
                r2.Mbelow = r3
                r1.Morder = r2
                r2.Morder = r3
                no r3.Mbelow
                no r3.Morder
                MStartingTower.Mtop = r1
                MStartingTower.tpole = North
                r1.pole = North
                r2.pole = North
                r3.pole = North
                Minit
            }
        } for exactly 3 MRing is sat

        // two rings where all are in starting tower, in order, but not with correct polarity
        initExThreeRingBadPole: {
            some disj r1, r2: MRing | {
                r1.Morder = r2
                r1.Mbelow = r2
                no r2.Mbelow
                no r2.Morder
                MStartingTower.Mtop = r2
                MStartingTower.tpole = North
                r1.pole = North
                r2.pole = South
                Minit
            }
        } for exactly 2 MRing is unsat

        // two rings where all are in starting tower, with correct polarity, but not in order
        initExTwoRingUnordered: {
            some disj r1, r2: MRing | {
                r1.Morder = r2
                r2.Mbelow = r1
                no r1.Mbelow
                no r2.Morder
                MStartingTower.Mtop = r2
                MStartingTower.tpole = North
                r1.pole = North
                r2.pole = North
                Minit
            }
        } for exactly 2 MRing is unsat
    }
}

---------------------------------------------------

// PREDICATES FOR TESTING Mwellformed 

pred noMbelowsAndMatchTowers {
    no ^Mbelow
    all r: MRing | some t: MTower | {
        r = t.Mtop or t.Mtop -> r in ^Mbelow 
        t.tpole = r.pole
    }
}
pred noMorderNoMbelow {
    no {^Morder} implies no {^Mbelow}
}
pred MorderSmallerThanMbelow {
    #{^Morder} < #{^Mbelow}
    #{^ Morder} > 0 // int wrapping issue if not included
}
pred noMRings {
    #{MRing} = 0
}

test suite for Mwellformed {
    assert Mwellformed is necessary for Mtrace
    assert noMbelowsAndMatchTowers is sufficient for Mwellformed
    assert noMRings is sufficient for Mwellformed

    test expect {
        // basic sat test
        MwellformedSat: {Mwellformed} is sat
        // no Morder implies no Mbelow
        noMorderThenNoMbelow: {Mwellformed implies noMorderNoMbelow} is theorem
        // more MRings in Mbelow than the established Morder
        MorderSmallerThanMbelowUnsat: {Mwellformed and MorderSmallerThanMbelow} is unsat
        // Mwellformed example: MRings all in Morder but in diff towers
        MwellformedFourMRingDiffTower: {
            some disj r1, r2, r3, r4: MRing | {
                r1.Mbelow = r2 
                no r2.Mbelow
                no r3.Mbelow
                no r4.Mbelow
                r1.Morder = r2
                r2.Morder = r3
                r3.Morder = r4
                no r4.Morder
                Mwellformed
            }
        } for exactly 4 MRing is sat

        // Mwellformed example: MRings all in Morder and in same tower
        MwellformedFourMRingSameTower: {
            some disj r1, r2, r3, r4: MRing, t: MTower | {
                r1.Mbelow = r2 
                r2.Mbelow = r3
                r3.Mbelow = r4
                no r4.Mbelow
                r1.Morder = r2
                r2.Morder = r3
                r3.Morder = r4
                no r4.Morder
                t.Mtop = r1
                Mwellformed
            }
        } for exactly 4 MRing is sat

        // not-Mwellformed example: MRings out of Morder
        notMwellformedThreeMRing: {
            some disj r1, r2, r3: MRing | {
                r1.Mbelow = r2 
                r2.Mbelow = r3
                r1.Morder = r2
                r2.Morder = r2
                no r3.Mbelow
                no r3.Morder
                Mwellformed
            }
        } for exactly 3 MRing is unsat
        
    }
}

// --------------------------------------------

// PREDICATES FOR TESTING Mmove

pred oneMTowerDecMRing {
    some t: MTower | t.Mtop' = t.Mtop.Mbelow
}
pred MRingMmoveDiffMTower {
    some disj t1, t2: MTower | t1.Mtop' = t2.Mtop
}
pred onlyOneMRingMmove {
    Minit and Mmove and #{MRing} > 1 implies {
        some r: MRing | {
            r.Mbelow' != r.Mbelow 
            all r1: MRing | r1 != r implies r1.Mbelow' = r1.Mbelow
        }
    }
}
pred MorderPreserved {
    Mwellformed and Mmove implies {
        all r: MRing | no r.Morder implies no r.Mbelow
    }
}
pred oneMRingTwoMTowerMmove {
    #{MRing} = 1
    #{MTower} = 2
    some disj r1: MRing, t1, t2: MTower | {
        t1.tpole = North
        t2.tpole = South
        no r1.Morder
        no r1.Mbelow
        t1.Mtop = r1
        no t2.Mtop
        r1.pole = North
        
        no r1.Mbelow'
        no t1.Mtop'
        t2.Mtop' = r1
        r1.pole' = South
    }
}
pred tooManyMTowersChange {
    some disj t1, t2, t3: MTower | {
        t1.Mtop' != t1.Mtop
        t2.Mtop' != t2.Mtop
        t3.Mtop' != t3.Mtop
    }
}
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
    assert oneMRingTwoMTowerMmove is sufficient for Mmove

    test expect {
        // basic sat test
        MmoveSat: {Mmove} is sat
        // Mmove doesn't work with only one MTower
        MmoveOneMTower: {Mmove and #{MTower} = 1} is unsat
        // too many MTowers change Mtops
        threeMTowersChange: {Mmove and tooManyMTowersChange} is unsat

        // Mmove starting from Minitial stack
        MinitialMmoveEx: {
            some disj r1, r2, r3: MRing, t1, t2, t3: MTower | {
                t1.Mtop = r1
                r1.Mbelow = r2
                r2.Mbelow = r3
                no r3.Mbelow
                r1.Morder = r2
                r2.Morder = r3
                no r3.Morder
                no t2.Mtop
                no t3.Mtop
                t1.tpole = North
                t2.tpole = South
                t3.tpole = South
                r1.pole = North
                r2.pole = North
                r3.pole = North

                t1.Mtop' = r2
                t2.Mtop' = r1
                no r1.Mbelow'
                r2.Mbelow' = r3
                no r3.Mbelow'
                no t3.Mtop'
                r2.pole' = North
                r3.pole' = North
                r1.pole' = South

                Minit
                Mmove
            } 
        } is sat

        // basic Mmove moving smallest MRing onto largest MRing
        basicMmoveEx: {
            some disj r1, r2, r3: MRing, t1, t2, t3: MTower | {
                r1.Morder = r2
                r2.Morder = r3
                no r3.Morder

                t1.Mtop = r2
                t2.Mtop = r1
                t3.Mtop = r3
                no r1.Mbelow
                no r2.Mbelow 
                no r3.Mbelow 
                t1.tpole = North
                t2.tpole = North
                t3.tpole = South
                
                r2.pole = North
                r1.pole = North
                r3.pole = South

                t1.Mtop' = r2
                no t2.Mtop'
                t3.Mtop' = r1
                r1.Mbelow' = r3
                no r2.Mbelow'
                no r3.Mbelow'
                r2.pole' = North
                r3.pole' = South
                r1.pole' = South

                Mmove
            }
        } is sat

        // Mmove resulting in end state
        endingMmoveEx: {
            some disj r1, r2, r3: MRing, t1, t2, t3: MTower | {
                r1.Morder = r2
                r2.Morder = r3
                no r3.Morder

                no t1.Mtop
                t2.Mtop = r1
                no r1.Mbelow
                t3.Mtop = r2
                r2.Mbelow = r3
                no r3.Mbelow
                t1.tpole = North
                t2.tpole = South
                t3.tpole = South
                r1.pole = North
                r2.pole = South
                r3.pole = South

                no t1.Mtop'
                no t2.Mtop'
                t3.Mtop' = r1
                r1.Mbelow' = r2
                r2.Mbelow' = r3
                no r3.Mbelow'
                r1.pole' = South
                r2.pole' = South
                r3.pole' = South

                Mmove
                next_state MendState
            } 
        } is sat
    }
}

--------------------------------------------

// PREDICATES FOR TESTING MendState 

pred allMRingsInEndMTower {
    all r: MRing | r != MEndingTower.Mtop implies MEndingTower.Mtop -> r in ^Mbelow
}
pred traceMustEndInMorder {
    {Minit and always Mmove and eventually MendState} implies allMRingInOrder
}
pred someMRingInStarting {
    some r: MRing | MStartingTower.Mtop = r
}
pred someMRingInEndingMtop {
    some MEndingTower.Mtop
}
pred oneMRingInEnding {
    #{MRing} = 1 and some MEndingTower.Mtop
    all t: MTower | t.Mtop != MEndingTower.Mtop
    all r: MRing | r.pole = MEndingTower.tpole
}
pred allRingsMatchEndPolarity {
    all r: MRing | r.pole = MEndingTower.tpole
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
            some disj r1, r2, r3: MRing | {
                r1.Mbelow = r2 
                r2.Mbelow = r3
                r1.Morder = r2
                r2.Morder = r3
                no r3.Mbelow
                no r3.Morder
                MEndingTower.Mtop = r1
                MendState
            }
        } for exactly 3 MRing is sat

        // three MRings where all are in ending MTower but not in Morder 
        // (sat but don't expect this in a trace)
        MendStateExThreeMRingUnMordered: {
            some disj r1, r2, r3: MRing | {
                r1.Mbelow = r2 
                r2.Mbelow = r3
                r1.Morder = r2
                r2.Morder = r3
                r3.Mbelow = r2
                no r3.Morder
                MEndingTower.Mtop = r1
                MendState
            }
        } for exactly 3 MRing is sat


        // three MRings where all are in ending MTower but there is a cycle in Mbelow
        // (sat but don't expect this in a trace)
        MendStateExThreeMRingCycled: {
            some disj r1, r2, r3: MRing | {
                r1.Mbelow = r2 
                r2.Mbelow = r3
                r1.Morder = r2
                r2.Morder = r3
                r3.Mbelow = r3
                no r3.Morder
                MEndingTower.Mtop = r1
                MendState
            }
        } for exactly 3 MRing is sat
    }

}

--------------------------------------------

// PREDICATES FOR TESTING TRACE

pred orderAlwaysPreserved {
    always {
        all r: MRing | some r.Mbelow implies r->r.Mbelow in ^Morder
    }
}
pred ringsEndAtEndingTower {
    eventually some MEndingTower.Mtop 
    eventually {all r: MRing | r != MEndingTower.Mtop implies MEndingTower.Mtop -> r in ^Mbelow}
}
pred ringsStartAtStartingTower {
    some MStartingTower.Mtop
    all r: MRing | r != MStartingTower.Mtop implies MStartingTower.Mtop -> r in ^Mbelow
}
pred oneRingMove {
    always {
        Mmove implies {
            some r: MRing | some r.Mbelow implies r.Mbelow' != r.Mbelow
        }
    }
}
pred oneRingChangePolarity {
    always {
        Mmove implies {
            some r: MRing | some r.Mbelow implies r.pole' != r.pole
        }
    }
}
pred multipleRingsMove {
    some disj r1, r2: MRing | r1.Mbelow' != r1.Mbelow and r2.Mbelow' != r2.Mbelow
}
pred multipleRingsChangePolarity {
    some disj r1, r2: MRing | r1.pole' != r1.pole and r2.pole' != r2.pole

}
pred counterChangesProperly {
    always {
        MtotalMoves implies {
            MCounter.Mcounter' != MCounter.Mcounter
        }
        MdoNothing implies {
            MCounter.Mcounter' = MCounter.Mcounter
        }
    }
}
pred minTowers2 {
    #{MTower} < 2
    #{MRing} > 1
}
pred oneMoveTrace {
    #{MRing} = 1
    #{MTower} = 3
    some r: MRing, t: MTower | {
        t != MStartingTower and t != MEndingTower
        MStartingTower.Mtop = r
        no MStartingTower.Mtop'
        MEndingTower.Mtop' = r
        no MEndingTower.Mtop
        no t.Mtop
        no t.Mtop'
        no r.Mbelow
        no r.Mbelow'
        no r.Morder
        MCounter.Mcounter = 0
        MCounter.Mcounter = 1
        r.pole != r.pole'
    }
}
pred ringMoving[r: MRing] {
    r.Mbelow' != r.Mbelow or (some disj t1, t2: MTower | t1.Mtop = r and t2.Mtop' = r)
}
pred smallestRingMovedEveryOtherTime {
    {always MtotalMoves until MCounter.Mcounter = 13 and always MCounter.Mcounter < 14} implies always {
    some r: MRing | {
        no {MRing -> r & ^Morder} and {
            ringMoving[r] implies {next_state {ringMoving[r]} or next_state next_state {ringMoving[r]}}
        }
    }
    }
}
pred firstRingOnTopofThird {
    eventually {
        some disj r1, r2, r3: MRing | {
            r1.Morder = r2
            r2.Morder = r3
            r1.Mbelow = r3
        }
    }
}
pred ringsSpreadOut {
    eventually {
        some disj r1, r2, r3: MRing | no r1.Mbelow and no r2.Mbelow and no r3.Mbelow
    }
}
pred towerTopsOverlap{
    eventually {some disj t1, t2: MTower, r: MRing | t1.Mtop = r and t2.Mtop = r}
}

test suite for Mtrace {
    assert orderAlwaysPreserved is necessary for Mtrace
    assert ringsEndAtEndingTower is necessary for Mtrace
    assert ringsStartAtStartingTower is necessary for Mtrace
    assert oneRingMove is necessary for Mtrace
    assert oneRingChangePolarity is necessary for Mtrace
    assert counterChangesProperly is necessary for Mtrace
    assert smallestRingMovedEveryOtherTime is necessary for Mtrace for exactly 3 MRing, 3 MTower, 5 Int
    assert oneMoveTrace is sufficient for Mtrace

    test expect {
        // basic sat test
        traceSat: {Mtrace} is sat
        // minimum number of towers needed for puzzle is 2
        minTowersTwo: {Mtrace and minTowers2} is unsat
        // multiple rings move at a time is invalid
        multRingsMove: {Mtrace and multipleRingsMove} is unsat
        // multiple rings change polarity is invalid
        multRingsFlip: {Mtrace and multipleRingsChangePolarity} is unsat
        // possible to stack first ring on top of third
        firstOnThird: {Mtrace and firstRingOnTopofThird} is sat
        // possible to have ringsSpreadOut 
        ringsAreSpreadOut: {Mtrace and ringsSpreadOut} is sat

        // Tests take a long time to run: (Alternatively, can verify using the run statements in the model files)
        // Minimum moves: 4 for 2 Ring, 3 Tower
        // minTrace4For2R3T: {Mtrace and always MCounter.Mcounter < 4} for exactly 2 MRing, 3 MTower is unsat 
        // Minimum moves: 13
        // minTrace13For2R3T: {Mtrace and always MCounter.Mcounter < 13} for exactly 3 MRing, 3 MTower is unsat
        // Minimum moves: 7
        // minTrace13For2R3T: {Mtrace and always MCounter.Mcounter < 7} for exactly 3 MRing, 3 MTower is unsat
    }
}