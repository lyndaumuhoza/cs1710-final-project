#lang forge/temporal
open "bicolorGeneric.frg"

---------------------------------------------------

// PREDICATES FOR TESTING INIT

// there is some ring whose order field links to itself
pred someRingsLinkToSelf {
   some iden & ^Border
}
// there is some ring whose below field links to itself
pred someRingsLinkToSelfBelow {
   some iden & ^Bbelow
}
// all ring stacks (defined by below) follows the expected size constraint (defined by order)
pred allRingInOrder {
   all r: BRing | some r.Bbelow implies r->r.Bbelow in ^Border
}
// the starting tower has some top ring
pred someStartingTop {
   some BStartingTower.Btop
}
// all rings are in the starting tower
pred allRingInStartTower {
   all r: BRing | r != BStartingTower.Btop implies BStartingTower.Btop -> r in ^Border
}
// there is one ring in the starting tower and no rings elsewhere
pred oneRingInStarting {
   #{BRing} = 1 and some BStartingTower.Btop
   all t: BTower | t.Btop != BStartingTower.Btop
}
// all rings should have alternating colors
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

// no rings are stacked 
pred noBelows {
   no ^Bbelow
}
// if there is no pre-defined order, then there must be no stack
pred noOrderNoBelow {
   no {^Border} implies no {^Bbelow}
}
// rings are stacked in a way that exceeds possible order constraints
pred orderSmallerThanBelow {
   #{^Border} < #{^Bbelow}
   #{^ Border} > 0 // int wrapping issue if not included
}
// there are no rings in the model
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

// some tower loses its top ring
pred oneTowerDecRing {
   some t: BTower | t.Btop' = t.Btop.Bbelow
}
// there are two towers for which the top of one became the top of the other
pred ringMoveDiffTower {
   some disj t1, t2: BTower | t1.Btop' = t2.Btop
}
// assuming a move is made from initial stack, there is some ring which gets moved 
// onto another stack
pred onlyOneRingMove {
   Binit and BtotalMoves and #{BRing} > 1 implies {
       some r: BRing | {
           r.Bbelow' != r.Bbelow
           all r1: BRing | r1 != r implies r1.Bbelow' = r1.Bbelow
       }
   }
}
// given a wellormed move, if there is no pre-defined order then there cannot be a stack
pred orderPreserved {
   Bwellformed and BtotalMoves implies {
       all r: BRing | no r.Border implies no r.Bbelow
   }
}
// given a wellormed move, if there is no pre-defined order then there cannot be a stack
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
// an example of moving the only ring in the model between two towers 
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
       BCounter.bcounter' = add[BCounter.bcounter, 1]
   }
}
// three towers' top ring changes at once
pred tooManyTowersChange {
   some disj t1, t2, t3: BTower | {
       t1.Btop' != t1.Btop
       t2.Btop' != t2.Btop
       t3.Btop' != t3.Btop
   }
}

test suite for BtotalMoves {
   assert oneTowerDecRing is necessary for BtotalMoves
   assert ringMoveDiffTower is necessary for BtotalMoves
   assert onlyOneRingMove is necessary for BtotalMoves
   assert alternatingColorsPreserved is necessary for BtotalMoves
   assert orderPreserved is necessary for BtotalMoves
   assert oneRingTwoTowerMove is sufficient for BtotalMoves


   test expect {
       // basic sat test
       moveSat: {BtotalMoves} is sat
       // move doesn't work with only one tower
       moveOnetower: {BtotalMoves and #{BTower} = 1} is unsat
       // too many towers change tops
       threeTowersChange: {BtotalMoves and tooManyTowersChange} is unsat
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
               BCounter.bcounter' = add[BCounter.bcounter, 1]

               Binit
               BtotalMoves
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
               BCounter.bcounter' = add[BCounter.bcounter, 1]

               BtotalMoves
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
               BCounter.bcounter' = add[BCounter.bcounter, 1]

               BtotalMoves
               next_state BendState
           }
       } is sat

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
               BCounter.bcounter' = add[BCounter.bcounter, 1]

               BtotalMoves
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
               BCounter.bcounter' = add[BCounter.bcounter, 1]

               BtotalMoves
           }
       } is unsat
   }

}

--------------------------------------------

// PREDICATES FOR TESTING DONOTHING

// rings don't change "below" order
pred allBelowStaysSame {
    all r: BRing | r.Bbelow' = r.Bbelow
}
// tower tops don't change
pred allTowerTopsStaySame {
    all t: BTower | t.Btop' = t.Btop
}
// counter stays the same
pred counterStaysSame {
    BCounter.bcounter' = BCounter.bcounter
}
// one ring stays in place
pred oneRingStays {
    #{BRing} = 1
    some r: BRing | BEndingTower.Btop = r and BEndingTower.Btop' = r and r.Bbelow' = r.Bbelow
    all t: BTower | t != BEndingTower implies t.Btop' = t.Btop
    BCounter.bcounter = BCounter.bcounter'
}
// rings not correctly ordered
pred unorderedRings {
    some disj r1, r2: BRing | r1.Border = r2 and r2.Bbelow = r1
}
// below (which defines ring stack) changes
pred belowChanges {
    ^Bbelow != ^Bbelow'
}

test suite for BdoNothing {
    assert allBelowStaysSame is necessary for BdoNothing
    assert allTowerTopsStaySame is necessary for BdoNothing
    assert counterStaysSame is necessary for BdoNothing
    assert oneRingStays is sufficient for BdoNothing

    test expect {
        //basic sat test
        doNothingSat: {BdoNothing} is sat
        // not possible to do transitions at once
        twoTransitionsAtOnce: {BdoNothing and BtotalMoves} is unsat
        // possible to do nothing with incorrect order 
        unorderedDoNothing: {unorderedRings and BdoNothing} is sat
        // not possible for below to change if doing nothing
        belowChangesUnsat: {BdoNothing and belowChanges} is unsat
        // do nothing example: all three rings stay in place 
        doNothingEx: {
            some disj r1, r2, r3: BRing, t1, t2, t3: BTower | {
                r1.col = Black
                r2.col = White
                r3.col = Black
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
                t2.Btop' = r1
                no r1.Bbelow'
                t3.Btop' = r2
                r2.Bbelow' = r3
                no r3.Bbelow'
                BCounter.bcounter' = BCounter.bcounter

                BdoNothing
            }
        } for exactly 3 BRing, 3 BTower is sat

                
        // do nothing non-example: ring moves to another tower
        doNothingBadMove: {
            some disj r1, r2, r3: BRing, t1, t2, t3: BTower | {
                r1.col = Black
                r2.col = White
                r3.col = Black
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
                BCounter.bcounter' = BCounter.bcounter

                BdoNothing
            }
        } for exactly 3 BRing, 3 BTower is unsat

        // do nothing non-example: counter increments
        doNothingBadCounter: {
            some disj r1, r2, r3: BRing, t1, t2, t3: BTower | {
                r1.col = Black
                r2.col = White
                r3.col = Black
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
                t2.Btop' = r1
                no r1.Bbelow'
                t3.Btop' = r2
                r2.Bbelow' = r3
                no r3.Bbelow'
                BCounter.bcounter' = add[BCounter.bcounter, 1]

                BdoNothing
            }
        } for exactly 3 BRing, 3 BTower is unsat
    }
}


 ----------------------------------

// PREDICATES FOR TESTING ENDSTATE

// all rings are stacked in the ending tower
pred allRingsInEndTower {
   all r: BRing | r != BEndingTower.Btop implies BEndingTower.Btop -> r in ^Bbelow
}
// given a trace, it is expected that all rings are in order
pred traceMustEndInOrder {
   {Binit and always BtotalMoves and eventually BendState} implies allRingInOrder
}
// there is some ring in the starting tower
pred someRingInStarting {
   some r: BRing | BStartingTower.Btop = r
}
// there is some ring in the ending tower
pred someRingInEndingTop {
   some BEndingTower.Btop
}
// there is exactly one ring in the ending tower with the correct polarity
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

// --------------------------------------------

// PREDICATES FOR TESTING TRACE

// the size order is always maintained
pred orderAlwaysPreserved {
   always {
       all r: BRing | some r.Bbelow implies r->r.Bbelow in ^Border
   }
}
// all rings end up in the end tower eventually
pred ringsEndAtEndingTower {
   eventually some BEndingTower.Btop
   eventually {all r: BRing | r != BEndingTower.Btop implies BEndingTower.Btop -> r in ^Bbelow}
}
// all rings start out at the starting tower
pred ringsStartAtStartingTower {
   some BStartingTower.Btop
   all r: BRing | r != BStartingTower.Btop implies BStartingTower.Btop -> r in ^Bbelow
}
// a move always guarantees that some ring is moved to a different stack
pred oneRingMove {
   always {
       BtotalMoves implies {
           some r: BRing | some r.Bbelow implies r.Bbelow' != r.Bbelow
       }
   }
}
// the counter always increment on a move, and stays the same when doing nothing
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
// there are fewer than 2 towers, and more than 1 ring in the model
pred minTowers2 {
   #{BTower} < 2
   #{BRing} > 1
}
// a trace where there is only one ring, moved from starting to ending tower
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
       BCounter.bcounter' = 1
   }
}
// alternating colors are preserved
pred validMoveTrace {
    #{BRing} = 3
    #{BTower} = 3
    eventually {
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

            BCounter.bcounter' = add[BCounter.bcounter, 1]
    }
    }
}
// some ring is moved
pred ringMoving[r: BRing] {
    r.Bbelow' != r.Bbelow or (some disj t1, t2: BTower | t1.Btop = r and t2.Btop' = r)
}
// for a trace done in the minimum number of moves, the smallest ring is moved every other step
pred smallestRingMovedEveryOtherTime {
    {always BtotalMoves until BCounter.bcounter = 3 and always BCounter.bcounter < 4} implies {
    some r: BRing | {
        no {BRing -> r & ^Border} and {
            ringMoving[r] and next_state next_state {ringMoving[r]}
        }
    }
    }
}
// only one ring can move at a time
pred multipleRingsMove {
    some disj r1, r2: BRing | r1.Bbelow' != r1.Bbelow and r2.Bbelow' != r2.Bbelow
}
// eventually the first ring ends up on the third ring
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

    test expect {
        // too many tops change (meaning more than one ring is moved)
        tooManyTowersTopChange: {tooManyTowersChange and Btrace} is unsat
        // minimum number of moves for 2 rings is 3
        minTraceTwoRings: {Btrace and (always BCounter.bcounter < 3)} for exactly 2 BRing, 3 BTower is unsat
        // minimum trace length for two rings is 3
        twoRingTrace3Min: {Btrace and eventually BCounter.bcounter = 3} for exactly 2 BRing, 3 BTower is sat
        // minimum number of towers needed for puzzle is 2
        minTowersTwo: {Btrace and minTowers2} is unsat
        // multiple rings move at a time is invalid
        multRingsMove: {Btrace and multipleRingsMove} is unsat
        // ring 1 can not be on top of ring 3 because they are the same color
        alterrnatingColorsinvalid: {Btrace and firstRingOnTopofThird} is unsat
        // possible to have one move trace 
        oneMoveSat: {Btrace and oneMoveTrace} is sat
        // possible to have this specific move
        validMoveSat: {Btrace and validMoveTrace} is sat

        // tests that take a long time to run (but can verify with a run statement):
        // minimum number of moves for 3 rings, 3 towers is 7
        // minTraceThreeRings: {Btrace and always BCounter.bcounter < 7} for exactly 3 BRing, 3 BTower is unsat
        // minimum number of moves for 3 rings, 4 towers is 5
        // minTraceThreeRingsFourTowers: {Btrace and always BCounter.bcounter < 5} for exactly 3 BRing, 4 BTower is unsat
        // minimum number of moves for 4 rings, 4 towers is 9
        // minTraceFourRingsFourTowers: {Btrace and always BCounter.bcounter < 9} for exactly 3 BRing, 4 BTower is unsat
    }
}
