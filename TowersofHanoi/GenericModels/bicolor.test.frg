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
       // no cycles in order
       someCyclesInitUnsat: {Binit and someRingsLinkToSelf} is unsat
       // no cycles in below
       someBelowCyclesInitUnsat: {Binit and someRingsLinkToSelfBelow} is unsat
       // no rings makes init unsat
       noRingsInitUnsat: {#{BRing}=0 and Binit} is unsat




       // three rings where all are in starting tower and in order
       initExThreeRing: {
           some disj r1, r2, r3: BRing | {
               r1.Bbelow = r2
               r2.Bbelow = r3
               r1.Border = r2
               r2.Border = r3
               no r3.Bbelow
               no r3.Border
               BStartingTower.Btop = r1
               Binit
           }
       } for exactly 3 BRing is sat


       // two rings where all are in starting tower and not in order
       initExThreeRingUnordered: {
           some disj r1, r2: BRing | {
               r1.Border = r2
               r2.Bbelow = r1
               no r1.Bbelow
               no r2.Border
               BStartingTower.Btop = r2
               Binit
           }
       } for exactly 2 BRing is unsat


       // Tests for alternating colors
       // three rings where all are in starting tower, alternating colors and in order
       initExThreeRingAlternatingColors: {
           some disj r1, r2, r3: BRing | {
               r1.Bbelow = r2
               r1.col = Black
               r2.col = White
               r3.col = Black
               r2.Bbelow = r3
               r1.Border = r2
               r2.Border = r3
               no r3.Bbelow
               no r3.Border
               BStartingTower.Btop = r1
               Binit
           }
       } for exactly 3 BRing is sat


       // three rings where all are in starting tower, and in order, but not alternating colors
       initExThreeRingNotAlternatingColors: {
           some disj r1, r2, r3: BRing | {
               r1.Bbelow = r2
               r1.col = Black
               r2.col = Black
               r3.col = White
               r2.Bbelow = r3
               r1.Border = r2
               r2.Border = r3
               no r3.Bbelow
               no r3.Border
               BStartingTower.Btop = r1
               Binit
               Btrace
           }
       } for exactly 3 BRing is unsat
   }
  
}




--------------------------------------------


// PREDICATES FOR TESTING WELLFORMED


pred noBelows {
   no ^Bbelow
}
pred noOrderNoBelow {
   no {^Border} implies no {^Bbelow}
}
pred orderSmallerThanBelow {
   #{^Border} < #{^Bbelow}
   #{^ Border} > 0 // int wrapping issue if not included
}
pred noRings {
   #{BRing} = 0
}




test suite for Bwellformed {
   assert Bwellformed is necessary for Btrace
   assert noBelows is sufficient for Bwellformed
   assert allRingsAlternatingColors is necessary for Bwellformed
   assert noRings is sufficient for Bwellformed


   test expect {
       // basic sat test
       wellformedSat: {Bwellformed} is sat
       // no order implies no below
       noOrderThenNoBelow: {Bwellformed implies noOrderNoBelow} is theorem
       // all rings should be in alternating colors
       ringsAlternatingColors: {Bwellformed implies allRingsAlternatingColors} is theorem
       // more rings in below than the established order
       orderSmallerThanBelowUnsat: {Bwellformed and orderSmallerThanBelow} is unsat
       // wellformed example: rings all in order but in diff towers
       wellformedFourRingDiffTower: {
           some disj r1, r2, r3, r4: BRing | {
               r1.Bbelow = r2
               no r2.Bbelow
               no r3.Bbelow
               no r4.Bbelow
               r1.Border = r2
               r2.Border = r3
               r3.Border = r4
               no r4.Border
               Bwellformed
           }
       } for exactly 4 BRing is sat


       // wellformed example: rings all in order and in same tower
       wellformedFourRingSameTower: {
           some disj r1, r2, r3, r4: BRing, t: BTower | {
               r1.Bbelow = r2
               r2.Bbelow = r3
               r3.Bbelow = r4
               no r4.Bbelow
               r1.Border = r2
               r2.Border = r3
               r3.Border = r4
               no r4.Border
               t.Btop = r1
               Bwellformed
           }
       } for exactly 4 BRing is sat


       // not-wellformed example: rings out of order
       notWellformedThreeRing: {
           some disj r1, r2, r3: BRing | {
               r1.Bbelow = r2
               r2.Bbelow = r3
               r1.Border = r2
               r2.Border = r2
               no r3.Bbelow
               no r3.Border
               Bwellformed
           }
       } for exactly 3 BRing is unsat


       // Tests for alternating colors
       // wellformed example: rings all in order, alternating colors, and in same tower
       wellformedFourRingAlternatingColorSameTower: {
           some disj r1, r2, r3, r4: BRing, t: BTower | {
               r1.Bbelow = r2
               r2.Bbelow = r3
               r3.Bbelow = r4
               r1.col = Black
               r2.col = White
               r3.col = Black
               r4.col = White
               no r4.Bbelow
               r1.Border = r2
               r2.Border = r3
               r3.Border = r4
               no r4.Border
               t.Btop = r1
               Bwellformed
           }
       } for exactly 4 BRing is sat


       // not-wellformed example: rings all in order, not alternating colors, and in same tower
       wellformedFourRingNotAlternatingColorSameTower: {
           some disj r1, r2, r3, r4: BRing, t: BTower | {
               r1.Bbelow = r2
               r2.Bbelow = r3
               r3.Bbelow = r4
               r1.col = Black
               r2.col = Black
               r3.col = White
               r4.col = White
               no r4.Bbelow
               r1.Border = r2
               r2.Border = r3
               r3.Border = r4
               no r4.Border
               t.Btop = r1
               Bwellformed
           }
       } for exactly 4 BRing is unsat


   }


}




// --------------------------------------------


// PREDICATES FOR TESTING MOVE


pred oneTowerDecRing {
   some t: BTower | t.Btop' = t.Btop.Bbelow
}


pred ringMoveDiffTower {
   some disj t1, t2: BTower | t1.Btop' = t2.Btop
}


pred onlyOneRingMove {
   Binit and Bmove and #{BRing} > 1 implies {
       some r: BRing | {
           r.Bbelow' != r.Bbelow
           all r1: BRing | r1 != r implies r1.Bbelow' = r1.Bbelow
       }
   }
}


pred orderPreserved {
   Bwellformed and Bmove implies {
       all r: BRing | no r.Border implies no r.Bbelow
   }
}


pred alternatingColorsPreserved {
   some disj t1, t2:BTower, r1:BRing {
       t1.Btop = r1
       t2.Btop' = r1
       r1.Bbelow' = t2.Btop
       t1.Btop' = r1.Bbelow
       some r1.Bbelow' implies {
           r1 -> r1.Bbelow' in ^Border
           r1.col != r1.Bbelow'.col
       }
   }
}


pred oneRingTwoTowerMove {
   #{BRing} = 1
   #{BTower} = 2
   some disj r1: BRing, t1, t2: BTower | {
       no r1.Border
       no r1.Bbelow
       t1.Btop = r1
       no t2.Btop
      
       no r1.Bbelow'
       no t1.Btop'
       t2.Btop' = r1
   }
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
   assert oneRingTwoTowerMove is sufficient for Bmove


   test expect {
       // basic sat test
       moveSat: {Bmove} is sat
       // move doesn't work with only one tower
       moveOnetower: {Bmove and #{BTower} = 1} is unsat
       // too many towers change tops
       threeTowersChange: {Bmove and tooManyTowersChange} is unsat


       // move starting from initial stack
       initialMoveEx: {
           some disj r1, r2, r3: BRing, t1, t2, t3: BTower | {
               t1.Btop = r1
               r1.Bbelow = r2
               r2.Bbelow = r3
               no r3.Bbelow
               r1.Border = r2
               r2.Border = r3
               no r3.Border
               no t2.Btop
               no t3.Btop


               t1.Btop' = r2
               t2.Btop' = r1
               no r1.Bbelow'
               r2.Bbelow' = r3
               no r3.Bbelow'
               no t3.Btop'


               Binit
               Bmove
           }
       } is sat


       // basic move moving smallest ring onto largest ring
       basicMoveEx: {
           some disj r1, r2, r3: BRing, t1, t2, t3: BTower | {
               r1.Border = r2
               r2.Border = r3
               no r3.Border


               t1.Btop = r2
               t2.Btop = r1
               t3.Btop = r3
               no r1.Bbelow
               no r2.Bbelow
               no r3.Bbelow


               t1.Btop' = r2
               no t2.Btop'
               t3.Btop' = r1
               r1.Bbelow' = r3
               no r2.Bbelow'
               no r3.Bbelow'


               Bmove
           }
       } is sat


       // move resulting in end state
       endingMoveEx: {
           some disj r1, r2, r3: BRing, t1, t2, t3: BTower | {
               r1.Border = r2
               r2.Border = r3
               no r3.Border


               no t1.Btop
               t2.Btop = r1
               no r1.Bbelow
               t3.Btop = r2
               r2.Bbelow = r3
               no r3.Bbelow


               no t1.Btop'
               no t2.Btop'
               t3.Btop' = r1
               r1.Bbelow' = r2
               r2.Bbelow' = r3
               no r3.Bbelow'


               Bmove
               next_state BendState
           }
       } is sat


       // Tests for alternating colors
       // basic move moving smallest ring onto second largest ring and preserving alternating colors
       alternatingColorsBasicMoveEx: {
           some disj r1, r2, r3: BRing, t1, t2, t3: BTower | {
               r1.Border = r2
               r2.Border = r3
               no r3.Border


               r1.col = Black
               r2.col = White
               r3.col = Black


               t1.Btop = r2
               t2.Btop = r1
               t3.Btop = r3
               no r1.Bbelow
               no r2.Bbelow
               no r3.Bbelow
               t1.Btop' = r1
               no t2.Btop'
               t3.Btop' = r3
               r1.Bbelow' = r2
               no r2.Bbelow'
               no r3.Bbelow'


               Bmove
           }
       } is sat


        // basic move moving smallest ring onto largest ring but they are the same color
       unsatAlternatingColorsBasicMoveEx: {
           some disj r1, r2, r3: BRing, t1, t2, t3: BTower | {
               r1.Border = r2
               r2.Border = r3
               no r3.Border


               r1.col = Black
               r2.col = White
               r3.col = Black


               t1.Btop = r2
               t2.Btop = r1
               t3.Btop = r3
               no r1.Bbelow
               no r2.Bbelow
               no r3.Bbelow


               t1.Btop' = r2
               no t2.Btop'
               t3.Btop' = r1
               r1.Bbelow' = r3
               no r2.Bbelow'
               no r3.Bbelow'


               Bmove
           }
       } is unsat
   }


}




// PREDICATES FOR TESTING ENDSTATE


pred allRingsInEndTower {
   all r: BRing | r != BEndingTower.Btop implies BEndingTower.Btop -> r in ^Bbelow
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
pred oneRingInEnding {
   #{BRing} = 1 and some BEndingTower.Btop
   all t: BTower | t.Btop != BEndingTower.Btop
}






test suite for BendState {


   assert allRingsInEndTower is necessary for BendState
   assert traceMustEndInOrder is necessary for BendState
   assert someRingInEndingTop is necessary for BendState
   assert oneRingInEnding is sufficient for BendState


   test expect {
       // basic sat test
       endStateSat: {BendState} is sat
       // some ring in other tower
       ringInStarting: {someRingInStarting and BendState} is unsat
       // no rings means endstate is unsat
       noRingsEndSat: {noRings and BendState} is unsat
       // three rings where all are in ending tower and in order
       endStateExThreeRing: {
           some disj r1, r2, r3: BRing | {
               r1.Bbelow = r2
               r2.Bbelow = r3
               r1.Border = r2
               r2.Border = r3
               no r3.Bbelow
               no r3.Border
               BEndingTower.Btop = r1
               BendState
           }
       } for exactly 3 BRing is sat


       // three rings where all are in ending tower but not in order
       // (sat but don't expect this in a trace)
       endStateExThreeRingUnordered: {
           some disj r1, r2, r3: BRing | {
               r1.Bbelow = r2
               r2.Bbelow = r3
               r1.Border = r2
               r2.Border = r3
               r3.Bbelow = r2
               no r3.Border
               BEndingTower.Btop = r1
               BendState
           }
       } for exactly 3 BRing is sat




       // three rings where all are in ending tower but there is a cycle in below
       // (sat but don't expect this in a trace)
       endStateExThreeRingCycled: {
           some disj r1, r2, r3: BRing | {
               r1.Bbelow = r2
               r2.Bbelow = r3
               r1.Border = r2
               r2.Border = r3
               r3.Bbelow = r3
               no r3.Border
               BEndingTower.Btop = r1
               BendState
           }
       } for exactly 3 BRing is sat


       // Tests for alternating colors
       // three rings where all are in ending tower and in order
       endStateExThreeRingAlternatingColors: {
           some disj r1, r2, r3: BRing | {
               r1.col = Black
               r2.col = White
               r3.col = Black
               r1.Bbelow = r2
               r2.Bbelow = r3
               r1.Border = r2
               r2.Border = r3
               no r3.Bbelow
               no r3.Border
               BEndingTower.Btop = r1
               BendState
           }
       } for exactly 3 BRing is sat


       // three rings where all are in ending tower and in order
       unsatEndStateExThreeRingAlternatingColors: {
           some disj r1, r2, r3: BRing | {
               r1.col = Black
               r2.col = White
               r3.col = White
               r1.Bbelow = r2
               r2.Bbelow = r3
               r1.Border = r2
               r2.Border = r3
               no r3.Bbelow
               no r3.Border
               BEndingTower.Btop = r1
               BendState
               Bwellformed
           }
       } for exactly 3 BRing is unsat
   }
}




--------------------------------------------


// PREDICATES FOR TESTING TRACE


pred orderAlwaysPreserved {
   always {
       all r: BRing | some r.Bbelow implies r->r.Bbelow in ^Border
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

pred counterChangesProperly {
    always {
        BtotalMoves implies {
            BCounter.bcounter' != BCounter.bcounter
        }
        BdoNothing implies {
            BCounter.bcounter' = BCounter.bcounter
        }
    }
}


pred traceLessThan7 {
    always BCounter.bcounter < 7
}
pred traceLessThan5 {
    always BCounter.bcounter < 5
}
pred traceLessThan3 {
    always BCounter.bcounter < 3
}

pred minTowers2 {
   #{BTower} < 2
   #{BRing} > 1
}
pred oneMoveTrace {
   #{BRing} = 1
   #{BTower} = 3
   some r: BRing, t: BTower | {
       t != BStartingTower and t != BEndingTower
       BStartingTower.Btop = r
       no BStartingTower.Btop'
       BEndingTower.Btop' = r
       no BEndingTower.Btop
       no t.Btop
       no t.Btop'
       no r.Bbelow
       no r.Bbelow'
       no r.Border
       BCounter.bcounter = 0
       BCounter.bcounter = 1
   }
}

// alternating colors are preserved
pred validMoveTrace {
    #{BRing} = 3
    #{BTower} = 3
   some disj r1, r2, r3: BRing, t1, t2, t3: BTower | {
               r1.Border = r2
               r2.Border = r3
               no r3.Border


               r1.col = Black
               r2.col = White
               r3.col = Black


               t1.Btop = r2
               t2.Btop = r1
               t3.Btop = r3
               no r1.Bbelow
               no r2.Bbelow
               no r3.Bbelow
               t1.Btop' = r1
               no t2.Btop'
               t3.Btop' = r3
               r1.Bbelow' = r2
               no r2.Bbelow'
               no r3.Bbelow'

        BCounter.bcounter = 0
        BCounter.bcounter = 1
   }
}

pred ringMoving[r: BRing] {
    r.Bbelow' != r.Bbelow or (some disj t1, t2: BTower | t1.Btop = r and t2.Btop' = r)
}
pred smallestRingMovedEveryOtherTime {
    {always BtotalMoves until BCounter.bcounter = 3 and always BCounter.bcounter < 4} implies {
    some r: BRing | {
        no {BRing -> r & ^Border} and {
            ringMoving[r] and next_state next_state {ringMoving[r]}
        }
    }
    }
}

pred multipleRingsMove {
    some disj r1, r2: BRing | r1.Bbelow' != r1.Bbelow and r2.Bbelow' != r2.Bbelow
}

pred firstRingOnTopofThird {
    eventually {
        some disj r1, r2, r3: BRing | {
            r1.col = Black
            r2.col = White
            r3.col = Black
            r1.Border = r2
            r2.Border = r3
            r1.Bbelow = r3
        }
    }
}

test suite for Btrace {
    assert orderAlwaysPreserved is necessary for Btrace
    assert ringsEndAtEndingTower is necessary for Btrace
    assert ringsStartAtStartingTower is necessary for Btrace
    assert oneRingMove is necessary for Btrace
    assert counterChangesProperly is necessary for Btrace
    assert smallestRingMovedEveryOtherTime is necessary for Btrace for exactly 2 BRing, 3 BTower
    assert allRingsAlternatingColors is necessary for Btrace
    assert oneMoveTrace is sufficient for Btrace
    assert validMoveTrace is sufficient for Btrace


    test expect {
        // too many tops change (meaning more than one ring is moved)
        tooManyTowersTopChange: {tooManyTowersChange and Btrace} is unsat
        // minimum number of moves for 2 rings is 3
        minTraceTwoRings: {Btrace and traceLessThan3} for exactly 2 BRing, 3 BTower is unsat
        // minimum trace length for two rings is 3
        twoRingTrace3Min: {Btrace and eventually BCounter.bcounter = 3} for exactly 2 BRing, 3 BTower is sat
        // minimum number of towers needed for puzzle is 2
        minTowersTwo: {Btrace and minTowers2} is unsat
        // multiple rings move at a time is invalid
        multRingsMove: {Btrace and multipleRingsMove} is unsat
        // ring 1 can not be on top of ring 3 because they are the same color
        alterrnatingColorsinvalid: {Btrace and firstRingOnTopofThird} is unsat

        // tests that take a long time to run (but can verify with a run statement):
        // minimum number of moves for 3 rings, 3 towers is 7
        minTraceThreeRings: {Btrace and traceLessThan7} for exactly 3 BRing, 3 BTower is unsat
        // minimum number of moves for 3 rings, 4 towers is 5
        minTraceThreeRingsFourTowers: {Btrace and traceLessThan5} for exactly 3 BRing, 4 BTower is unsat
        // minimum number of moves for 4 rings, 4 towers is 9
        minTraceFourRingsFourTowers: {Btrace and traceLessThan5} for exactly 3 BRing, 4 BTower is unsat
    }
}
