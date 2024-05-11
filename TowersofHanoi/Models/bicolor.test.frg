#lang forge/temporal


open "bicolorTowers.frg"

------------------------------------------------------------------------------
// TEST SUITE SIMILAR TO OTHER "bicolor.test.frg" FILE, BUT MADE TO WORK WITH
// HARD-CODED VERSION (TO VERIFY BOTH MODEL VERSIONS)
-------------------------------------------------------------------------------

// PREDICATES FOR TESTING INIT

pred someRingsLinkToSelf {
    some r: BRing | r -> r in ^Bbelow
}
pred allRingInOrder {
    BRing1.Bbelow = BRing2
    BRing2.Bbelow = BRing3
    no BRing3.Bbelow
}
pred someStartingTop {
   some BStartingTower.Btop
}
pred allRingInStartTower {
    BStartingTower.Btop = BRing1
    BStartingTower.Btop -> BRing2 in ^Bbelow
    BStartingTower.Btop -> BRing3 in ^Bbelow
}
pred oneRingInStarting {
   some BStartingTower.Btop
   all t: BTower | t.Btop != BStartingTower.Btop
}
pred allRingsAlternatingColors {
   all disj r1, r2: BRing | {
       r1.Bbelow = r2 implies {
           r1.col != r2.col
       }  
   }
}

test suite for Binit {
   assert allRingInOrder is necessary for Binit
   assert someStartingTop is necessary for Binit
   assert allRingInStartTower is necessary for Binit
   assert oneRingInStarting is sufficient for Binit
   assert allRingsAlternatingColors is necessary for Binit

   test expect {
       // basic sat test
       initSat: {Binit} is sat
       // all rings alternate colors at first
       alternatingColors: {Binit implies allRingsAlternatingColors} is theorem
       // no cycles in below
       someCyclesInitUnsat: {Binit and someRingsLinkToSelf} is unsat
       // no rings makes init unsat
       noRingsInitUnsat: {#{BRing}=0 and Binit} is unsat

       // three rings where all are in starting tower and in order
       initExThreeRing: {
            BStartingTower.Btop = BRing1
            BRing1.Bbelow = BRing2
            BRing2.Bbelow = BRing3
            no BRing3.Bbelow
            Binit
       } is sat


       // three rings where all are in starting tower and not in order
       initExThreeRingUnordered: {
            BStartingTower.Btop = BRing1
            BRing1.Bbelow = BRing3
            BRing3.Bbelow = BRing2
            no BRing2.Bbelow
            BRing1.col = Black
            BRing2.col = White
            BRing3.col = Black
            Binit
       } is unsat

        // three rings where all are in starting tower, in order, with alternating colors
       initExThreeRingGoodColors: {
            BStartingTower.Btop = BRing1
            BRing1.Bbelow = BRing2
            BRing2.Bbelow = BRing3
            no BRing3.Bbelow
            BRing1.col = Black
            BRing2.col = White
            BRing3.col = Black
            Binit
       } is sat

       // three rings where all are in order in starting tower but not alternating in color
       initExBadColors: {
            BStartingTower.Btop = BRing1
            BRing1.Bbelow = BRing2
            BRing2.Bbelow = BRing3
            no BRing3.Bbelow
            BRing1.col = White
            BRing2.col = White
            BRing3.col = Black
            Binit
       } is unsat
   }
  
}

--------------------------------------------

// PREDICATES FOR TESTING WELLFORMED

pred noBelowsAndAlternatingColors {
    no ^Bbelow
    all r: BRing | {
        some r.Bbelow implies r.col != r.Bbelow.col
    }
}
pred noRings {
   #{BRing} = 0
}
pred someCycleInBelow {
    BRing1.Bbelow = BRing2
    BRing2.Bbelow = BRing1
}

test suite for Bwellformed {
   assert Bwellformed is necessary for Btrace
   assert noBelowsAndAlternatingColors is sufficient for Bwellformed
   assert allRingsAlternatingColors is necessary for Bwellformed
   assert noRings is sufficient for Bwellformed


   test expect {
       // basic sat test
       wellformedSat: {Bwellformed} is sat
       // all rings should be in alternating colors
       ringsAlternatingColors: {Bwellformed implies allRingsAlternatingColors} is theorem
       // not possible to have cycles in below
        someCycleInBelowUnsat: {Bwellformed and someCycleInBelow} is unsat
       // wellformed example: rings wellformed and in diff towers
       MwellformedBRingDiffTower: {
            BStartingTower.Btop = BRing1
            BMidTower.Btop = BRing2
            BEndingTower.Btop = BRing3
            no BRing1.Bbelow
            no BRing2.Bbelow
            no BRing3.Bbelow
            BRing1.col = Black
            BRing2.col = White
            BRing3.col = Black
            Bwellformed
        } is sat

       // wellformed example: rings all in order and in same tower
       wellformedRingSameTower: {
            BStartingTower.Btop = BRing1
            no BMidTower.Btop 
            no BEndingTower.Btop
            BRing1.Bbelow = BRing2
            BRing2.Bbelow = BRing3
            no BRing3.Bbelow
            BRing1.col = Black
            BRing2.col = White
            BRing3.col = Black
            Bwellformed
       } is sat

       // not-wellformed example: rings out of order
       notWellformedThreeRing: {
            BStartingTower.Btop = BRing3
            no BMidTower.Btop 
            no BEndingTower.Btop
            BRing3.Bbelow = BRing2
            BRing2.Bbelow = BRing1
            no BRing1.Bbelow
            BRing1.col = Black
            BRing2.col = White
            BRing3.col = Black
            Bwellformed
       } is unsat

       // not-wellformed example: rings all in order, not alternating colors, and in same tower
       wellformedFourRingNotAlternatingColorSameTower: {
            BStartingTower.Btop = BRing1
            no BMidTower.Btop 
            no BEndingTower.Btop
            BRing1.Bbelow = BRing2
            BRing2.Bbelow = BRing3
            no BRing3.Bbelow
            BRing1.col = Black
            BRing2.col = White
            BRing3.col = White
            Bwellformed
       } is unsat
   }
}

--------------------------------------------

// PREDICATES FOR TESTING MOVE

pred oneTowerDecRing {
   some t: BTower | t.Btop' = t.Btop.Bbelow
}
pred ringMoveDiffTower {
   some disj t1, t2: BTower | t1.Btop' = t2.Btop
}
pred onlyOneRingMove {
   Binit and Bmove implies {
       some r: BRing | {
           r.Bbelow' != r.Bbelow
           all r1: BRing | r1 != r implies r1.Bbelow' = r1.Bbelow
       }
   }
}
pred orderPreserved {
   Bwellformed and Bmove implies {
        no BRing3.Bbelow 
        BRing2.Bbelow != BRing1
        all r: BRing | r -> r not in ^Bbelow
   }
}
pred alternatingColorsPreserved {
    Bwellformed implies {
    all r: BRing | {
        some r.Bbelow implies r.col != r.Bbelow.col
    }
    }
}
pred oneRingExMove {
    no BRing1.Bbelow
    no BRing2.Bbelow
    no BRing3.Bbelow
    BStartingTower.Btop = BRing1
    BMidTower.Btop = BRing2
    BEndingTower.Btop = BRing3
    BRing1.col = Black
    BRing2.col = White
    BRing3.col = Black

    no BStartingTower.Btop'
    BMidTower.Btop' = BRing1
    BEndingTower.Btop' = BRing3
    BRing1.Bbelow' = BRing2
    no BRing2.Bbelow'
    no BRing3.Bbelow'
}
pred tooManyTowersChange {
   some disj t1, t2, t3: BTower | {
       t1.Btop' != t1.Btop
       t2.Btop' != t2.Btop
       t3.Btop' != t3.Btop
   }
}
test suite for Bmove {
   assert oneTowerDecRing is necessary for Bmove
   assert ringMoveDiffTower is necessary for Bmove
   assert onlyOneRingMove is necessary for Bmove
   assert alternatingColorsPreserved is necessary for Bmove
   assert orderPreserved is necessary for Bmove
   assert oneRingExMove is sufficient for Bmove


   test expect {
       // basic sat test
       moveSat: {Bmove} is sat
       // move doesn't work with only one tower
       moveOnetower: {Bmove and #{BTower} = 1} is unsat
       // too many towers change tops
       threeTowersChange: {Bmove and tooManyTowersChange} is unsat


       // move starting from initial stack
       initialMoveEx: {
            BStartingTower.Btop = BRing1
            no BMidTower.Btop
            no BEndingTower.Btop
            BRing1.Bbelow = BRing2
            BRing2.Bbelow = BRing3
            no BRing3.Bbelow
            BRing1.col = Black
            BRing2.col = White
            BRing3.col = Black

            BStartingTower.Btop' = BRing2
            BMidTower.Btop' = BRing1
            no BEndingTower.Btop'
            no BRing1.Bbelow'
            BRing2.Bbelow' = BRing3
            no BRing3.Bbelow'

            Binit
            Bmove

       } is sat


       // basic move moving smallest ring onto largest ring
       basicMoveEx: {
            BStartingTower.Btop = BRing1
            BMidTower.Btop = BRing3
            no BEndingTower.Btop
            BRing1.Bbelow = BRing2
            no BRing2.Bbelow
            no BRing3.Bbelow
            BRing1.col = Black
            BRing2.col = White
            BRing3.col = Black

            BStartingTower.Btop' = BRing2
            BMidTower.Btop' = BRing1
            no BEndingTower.Btop'
            BRing1.Bbelow' = BRing3
            no BRing2.Bbelow'
            no BRing3.Bbelow'

            Bmove
       } is sat


       // move resulting in end state
       endingMoveEx: {
            BStartingTower.Btop = BRing1
            no BMidTower.Btop
            BEndingTower.Btop = BRing2
            no BRing1.Bbelow 
            BRing2.Bbelow = BRing3
            no BRing3.Bbelow
            BRing1.col = Black
            BRing2.col = White
            BRing3.col = Black

            no BStartingTower.Btop' 
            no BMidTower.Btop'
            BEndingTower.Btop' = BRing1
            BRing1.Bbelow' = BRing2
            BRing2.Bbelow' = BRing3
            no BRing3.Bbelow'

            Bmove
            next_state BendState
       } is sat


       // Tests for alternating colors
       // basic move moving smallest ring onto second largest ring and preserving alternating colors
       alternatingColorsBasicMoveEx: {
            BStartingTower.Btop = BRing1
            BMidTower.Btop = BRing2
            no BEndingTower.Btop
            BRing1.Bbelow = BRing3
            no BRing2.Bbelow
            no BRing3.Bbelow
            BRing1.col = Black
            BRing2.col = White
            BRing3.col = Black

            BStartingTower.Btop' = BRing3
            BMidTower.Btop' = BRing1
            no BEndingTower.Btop'
            BRing1.Bbelow' = BRing2
            no BRing2.Bbelow'
            no BRing3.Bbelow'

            Bmove
       } is sat


        // basic move moving smallest ring onto largest ring but they are the same color
       unsatAlternatingColorsBasicMoveEx: {
            BStartingTower.Btop = BRing1
            BMidTower.Btop = BRing2
            BEndingTower.Btop = BRing3
            no BRing1.Bbelow 
            no BRing2.Bbelow
            no BRing3.Bbelow
            BRing1.col = Black
            BRing2.col = White
            BRing3.col = Black

            no BStartingTower.Btop' 
            BMidTower.Btop' = BRing2
            BEndingTower.Btop' = BRing1
            BRing1.Bbelow' = BRing3
            no BRing2.Bbelow'
            no BRing3.Bbelow'

            Bmove and next_state Bwellformed
       } is unsat
   }
}

--------------------------------------------

// PREDICATES FOR TESTING ENDSTATE


pred allRingsInEndTower {
    BEndingTower.Btop = BRing1
    BRing1.Bbelow = BRing2
    BRing2.Bbelow = BRing3
}
pred traceMustEndInOrder {
   {Binit and always Bmove and eventually BendState} implies allRingInOrder
}
pred someRingInStarting {
   some r: BRing | BStartingTower.Btop = r
}
pred someRingInEndingTop {
   some BEndingTower.Btop
}
pred sufficientForEnd {
   BEndingTower.Btop = BRing1
   no BStartingTower.Btop 
   no BMidTower.Btop
   BRing1 -> BRing2 in ^Bbelow
   BRing2 -> BRing3 in ^Bbelow
   no BRing3.Bbelow
}

test suite for BendState {
   assert allRingsInEndTower is necessary for BendState
   assert traceMustEndInOrder is necessary for BendState
   assert someRingInEndingTop is necessary for BendState
   assert sufficientForEnd is sufficient for BendState

   test expect {
       // basic sat test
       endStateSat: {BendState} is sat
       // some ring in other tower
       ringInStarting: {someRingInStarting and BendState} is unsat
       // no rings means endstate is unsat
       noRingsEndSat: {noRings and BendState} is unsat
       // three rings where all are in ending tower and in order
       endStateExThreeRing: {
            no BStartingTower.Btop 
            no BMidTower.Btop 
            BEndingTower.Btop = BRing1
            BRing1.Bbelow = BRing2
            BRing2.Bbelow = BRing3
            no BRing3.Bbelow
            BRing1.col = Black
            BRing2.col = White
            BRing3.col = Black
            BendState
       } is sat

       // three rings where all are in ending tower but not in order
       endStateExThreeRingUnordered: {
            no BStartingTower.Btop 
            no BMidTower.Btop 
            BEndingTower.Btop = BRing1
            BRing1.Bbelow = BRing3
            BRing3.Bbelow = BRing2
            no BRing2.Bbelow
            BRing1.col = Black
            BRing2.col = White
            BRing3.col = Black
            BendState
       } is unsat

       // three rings where all are in ending tower but there is a cycle in below
       endStateExThreeRingCycled: {
            no BStartingTower.Btop 
            no BMidTower.Btop 
            BEndingTower.Btop = BRing1
            BRing1.Bbelow = BRing2
            BRing2.Bbelow = BRing3
            BRing3.Bbelow = BRing1
            BRing1.col = Black
            BRing2.col = White
            BRing3.col = Black
            BendState
       } is unsat


       // three rings where all are in ending tower but not alternating
       // (sat bc endState doesn't restrict color but don't expect this in trace)
       unsatEndStateExThreeRingAlternatingColors: {
            no BStartingTower.Btop 
            no BMidTower.Btop 
            BEndingTower.Btop = BRing1
            BRing1.Bbelow = BRing2
            BRing2.Bbelow = BRing3
            no BRing3.Bbelow
            BRing1.col = White
            BRing2.col = White
            BRing3.col = Black
            BendState
       } is sat
   }
}

--------------------------------------------

// PREDICATES FOR TESTING TRACE

pred orderAlwaysPreserved {
   always {
        no BRing3.Bbelow 
        BRing2.Bbelow != BRing1
        all r: BRing | r -> r not in ^Bbelow
   }
}
pred colorOrderAlwaysPreserved {
    always {
        no disj r1, r2: BRing | r1.Bbelow = r2 and r1.col = r2.col
    }
}
pred ringsEndAtEndingTower {
   eventually some BEndingTower.Btop
   eventually {all r: BRing | r != BEndingTower.Btop implies BEndingTower.Btop -> r in ^Bbelow}
}
pred ringsStartAtStartingTower {
   some BStartingTower.Btop
   all r: BRing | r != BStartingTower.Btop implies BStartingTower.Btop -> r in ^Bbelow
}
pred oneRingMove {
   always {
       Bmove implies {
           some r: BRing | some r.Bbelow implies r.Bbelow' != r.Bbelow
       }
   }
}
pred minTowers3 {
   #{BTower} < 3
   #{BRing} > 1
}
pred multipleRingsMove {
    some disj r1, r2: BRing | r1.Bbelow' != r1.Bbelow and r2.Bbelow' != r2.Bbelow
}
pred ringsSpreadOut {
    eventually {
        some disj r1, r2, r3: BRing | no r1.Bbelow and no r2.Bbelow and no r3.Bbelow
    }
}
pred firstRingOnTopofThird {
    eventually {
        some disj r1, r2, r3: BRing | {
            r1.col = Black
            r2.col = White
            r3.col = Black
            r1.Bbelow = r3
        }
    }
}

test suite for Btrace {
    assert orderAlwaysPreserved is necessary for Btrace
    assert colorOrderAlwaysPreserved is necessary for Btrace
    assert ringsEndAtEndingTower is necessary for Btrace
    assert ringsStartAtStartingTower is necessary for Btrace
    assert oneRingMove is necessary for Btrace


    test expect {
        // basic sat test
        traceSat: {Btrace} is sat
        // too many tops change (meaning more than one ring is moved)
        tooManyTowersTopChange: {tooManyTowersChange and Btrace} is unsat
        // minimum number of towers needed for this puzzle is 3
        minTowersTwo: {Btrace and minTowers3} is unsat
        // multiple rings move at a time is invalid
        multRingsMove: {Btrace and multipleRingsMove} is unsat
        // possible to have one ring per tower
        oneRingPerTower: {Btrace and ringsSpreadOut} is sat
        // ring 1 can not be on top of ring 3 because they are the same color
        alterrnatingColorsinvalid: {Btrace and firstRingOnTopofThird} is unsat
    }
}
