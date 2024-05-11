#lang forge/temporal

open "towersGeneric.frg"

--------------------------------------------

// PREDICATES FOR TESTING INIT

// there is some ring whose order field links to itself
pred someRingsLinkToSelf {
    some iden & ^order
}
// there is some ring whose below field links to itself
pred someRingsLinkToSelfBelow {
    some iden & ^below
}
// all ring stacks (defined by below) follows the expected size constraint (defined by order)
pred allRingInOrder {
    all r: Ring | some r.below implies r->r.below in ^order
}
// the starting tower has some top ring
pred someStartingTop {
    some StartingTower.top
}
// all rings are in the starting tower
pred allRingInStartTower {
    all r: Ring | r != StartingTower.top implies StartingTower.top -> r in ^order
}
// there is one ring in the starting tower and no rings elsewhere
pred oneRingInStarting {
    #{Ring} = 1 and some StartingTower.top
    all t: Tower | t.top != StartingTower.top
}

test suite for init {
    assert allRingInOrder is necessary for init
    assert someStartingTop is necessary for init
    assert allRingInStartTower is necessary for init
    assert oneRingInStarting is sufficient for init

    test expect {
        // basic sat test
        initSat: {init} is sat
        // no cycles in order
        someCyclesInitUnsat: {init and someRingsLinkToSelf} is unsat
        // no cycles in below
        someBelowCyclesInitUnsat: {init and someRingsLinkToSelfBelow} is unsat
        // no rings makes init unsat
        noRingsInitUnsat: {#{Ring}=0 and init} is unsat

        // three rings where all are in starting tower and in order
        initExThreeRing: {
            some disj r1, r2, r3: Ring | {
                r1.below = r2 
                r2.below = r3
                r1.order = r2
                r2.order = r3
                no r3.below
                no r3.order
                StartingTower.top = r1
                init
            }
        } for exactly 3 Ring is sat

        // two rings where all are in starting tower and not in order
        initExThreeRingUnordered: {
            some disj r1, r2: Ring | {
                r1.order = r2
                r2.below = r1
                no r1.below
                no r2.order
                StartingTower.top = r2
                init
            }
        } for exactly 2 Ring is unsat
    }
}

--------------------------------------------

// PREDICATES FOR TESTING WELLFORMED 

// no rings are stacked 
pred noBelows {
    no ^below
}
// if there is no pre-defined order, then there must be no stack
pred noOrderNoBelow {
    no {^order} implies no {^below}
}
// rings are stacked in a way that exceeds possible order constraints
pred orderSmallerThanBelow {
    #{^order} < #{^below}
    #{^ order} > 0 // int wrapping issue if not included
}
// there are no rings in the model
pred noRings {
    #{Ring} = 0
}

test suite for wellformed {
    assert wellformed is necessary for trace
    assert noBelows is sufficient for wellformed
    assert noRings is sufficient for wellformed

    test expect {
        // basic sat test
        wellformedSat: {wellformed} is sat
        // no order implies no below
        noOrderThenNoBelow: {wellformed implies noOrderNoBelow} is theorem
        // more rings in below than the established order
        orderSmallerThanBelowUnsat: {wellformed and orderSmallerThanBelow} is unsat
        // wellformed example: rings all in order but in diff towers
        wellformedFourRingDiffTower: {
            some disj r1, r2, r3, r4: Ring | {
                r1.below = r2 
                no r2.below
                no r3.below
                no r4.below
                r1.order = r2
                r2.order = r3
                r3.order = r4
                no r4.order
                wellformed
            }
        } for exactly 4 Ring is sat

        // wellformed example: rings all in order and in same tower
        wellformedFourRingSameTower: {
            some disj r1, r2, r3, r4: Ring, t: Tower | {
                r1.below = r2 
                r2.below = r3
                r3.below = r4
                no r4.below
                r1.order = r2
                r2.order = r3
                r3.order = r4
                no r4.order
                t.top = r1
                wellformed
            }
        } for exactly 4 Ring is sat

        // not-wellformed example: rings out of order
        notWellformedThreeRing: {
            some disj r1, r2, r3: Ring | {
                r1.below = r2 
                r2.below = r3
                r1.order = r2
                r2.order = r2
                no r3.below
                no r3.order
                wellformed
            }
        } for exactly 3 Ring is unsat
        
    }
}

// --------------------------------------------

// PREDICATES FOR TESTING MOVE

// some tower loses its top ring
pred oneTowerDecRing {
    some t: Tower | t.top' = t.top.below
}
// there are two towers for which the top of one became the top of the other
pred ringMoveDiffTower {
    some disj t1, t2: Tower | t1.top' = t2.top
}
// assuming a move is made from initial stack, there is some ring who gets moved 
// onto another stack
pred onlyOneRingMove {
    init and move and #{Ring} > 1 implies {
        some r: Ring | {
            r.below' != r.below 
            all r1: Ring | r1 != r implies r1.below' = r1.below
        }
    }
}
// given a wellormed move, if there is no pre-defined order then there cannot be a stack
pred orderPreserved {
    wellformed and move implies {
        all r: Ring | no r.order implies no r.below
    }
}

// an example of moving the only ring in the model between two towers 
pred oneRingTwoTowerMove {
    #{Ring} = 1
    #{Tower} = 2
    some disj r1: Ring, t1, t2: Tower | {
        no r1.order
        no r1.below
        t1.top = r1
        no t2.top
        
        no r1.below'
        no t1.top'
        t2.top' = r1
    }
}
// three towers' top ring changes at once
pred tooManyTowersChange {
    some disj t1, t2, t3: Tower | {
        t1.top' != t1.top
        t2.top' != t2.top
        t3.top' != t3.top
    }
}

test suite for move {
    assert oneTowerDecRing is necessary for move
    assert ringMoveDiffTower is necessary for move
    assert onlyOneRingMove is necessary for move
    assert orderPreserved is necessary for move
    assert oneRingTwoTowerMove is sufficient for move

    test expect {
        // basic sat test
        moveSat: {move} is sat
        // move doesn't work with only one tower
        moveOnetower: {move and #{Tower} = 1} is unsat
        // too many towers change tops
        threeTowersChange: {move and tooManyTowersChange} is unsat

        // move starting from initial stack
        initialMoveEx: {
            some disj r1, r2, r3: Ring, t1, t2, t3: Tower | {
                t1.top = r1
                r1.below = r2
                r2.below = r3
                no r3.below
                r1.order = r2
                r2.order = r3
                no r3.order
                no t2.top
                no t3.top

                t1.top' = r2
                t2.top' = r1
                no r1.below'
                r2.below' = r3
                no r3.below'
                no t3.top'

                init
                move
            } 
        } is sat

        // basic move moving smallest ring onto largest ring
        basicMoveEx: {
            some disj r1, r2, r3: Ring, t1, t2, t3: Tower | {
                r1.order = r2
                r2.order = r3
                no r3.order

                t1.top = r2
                t2.top = r1
                t3.top = r3
                no r1.below
                no r2.below 
                no r3.below 

                t1.top' = r2
                no t2.top'
                t3.top' = r1
                r1.below' = r3
                no r2.below'
                no r3.below'

                move
            }
        } is sat

        // move resulting in end state
        endingMoveEx: {
            some disj r1, r2, r3: Ring, t1, t2, t3: Tower | {
                r1.order = r2
                r2.order = r3
                no r3.order

                no t1.top
                t2.top = r1
                no r1.below
                t3.top = r2
                r2.below = r3
                no r3.below

                no t1.top'
                no t2.top'
                t3.top' = r1
                r1.below' = r2
                r2.below' = r3
                no r3.below'

                move
                next_state endState
            } 
        } is sat
    }
}


--------------------------------------------

// PREDICATES FOR TESTING ENDSTATE 

// all rings are stacked in the ending tower
pred allRingsInEndTower {
    all r: Ring | r != EndingTower.top implies EndingTower.top -> r in ^below
}
// given a trace, it is expected that all rings are in order
pred traceMustEndInOrder {
    {init and always move and eventually endState} implies allRingInOrder
}
// there is some ring in the starting tower
pred someRingInStarting {
    some r: Ring | StartingTower.top = r
}
// there is some ring in the ending tower
pred someRingInEndingTop {
    some EndingTower.top
}
// there is exactly one ring in the ending tower
pred oneRingInEnding {
    #{Ring} = 1 and some EndingTower.top
    all t: Tower | t.top != EndingTower.top
}

test suite for endState {
    assert allRingsInEndTower is necessary for endState
    assert traceMustEndInOrder is necessary for endState
    assert someRingInEndingTop is necessary for endState
    assert oneRingInEnding is sufficient for endState

    test expect {
        // basic sat test
        endStateSat: {endState} is sat
        // some ring in other tower
        ringInStarting: {someRingInStarting and endState} is unsat
        // no rings means endstate is unsat
        noRingsEndSat: {noRings and endState} is unsat
        // three rings where all are in ending tower and in order
        endStateExThreeRing: {
            some disj r1, r2, r3: Ring | {
                r1.below = r2 
                r2.below = r3
                r1.order = r2
                r2.order = r3
                no r3.below
                no r3.order
                EndingTower.top = r1
                endState
            }
        } for exactly 3 Ring is sat

        // three rings where all are in ending tower but not in order 
        // (sat but don't expect this in a trace)
        endStateExThreeRingUnordered: {
            some disj r1, r2, r3: Ring | {
                r1.below = r2 
                r2.below = r3
                r1.order = r2
                r2.order = r3
                r3.below = r2
                no r3.order
                EndingTower.top = r1
                endState
            }
        } for exactly 3 Ring is sat


        // three rings where all are in ending tower but there is a cycle in below
        // (sat but don't expect this in a trace)
        endStateExThreeRingCycled: {
            some disj r1, r2, r3: Ring | {
                r1.below = r2 
                r2.below = r3
                r1.order = r2
                r2.order = r3
                r3.below = r3
                no r3.order
                EndingTower.top = r1
                endState
            }
        } for exactly 3 Ring is sat
    }

}

--------------------------------------------

// PREDICATES FOR TESTING TRACE

// the size order is always maintained
pred orderAlwaysPreserved {
    always {
        all r: Ring | some r.below implies r->r.below in ^order
    }
}
// all rings end up in the end tower eventually
pred ringsEndAtEndingTower {
    eventually some EndingTower.top 
    eventually {all r: Ring | r != EndingTower.top implies EndingTower.top -> r in ^below}
}
// all rings start out at the starting tower
pred ringsStartAtStartingTower {
    some StartingTower.top
    all r: Ring | r != StartingTower.top implies StartingTower.top -> r in ^below
}
// a move always guarantees that some ring is moved to a different stack
pred oneRingMove {
    always {
        move implies {
            some r: Ring | some r.below implies r.below' != r.below
        }
    }
}
// the counter always increment on a move, and stays the same when doing nothing
pred counterChangesProperly {
    always {
        totalMoves implies {
            Counter.counter' != Counter.counter
        }
        doNothing implies {
            Counter.counter' = Counter.counter
        }
    }
}
// there are fewer than 2 towers, and more than 1 ring in the model
pred minTowers2 {
    #{Tower} < 2
    #{Ring} > 1
}
// a trace where there is only one ring, moved from starting to ending tower
pred oneMoveTrace {
    #{Ring} = 1
    #{Tower} = 3
    some r: Ring, t: Tower | {
        t != StartingTower and t != EndingTower
        StartingTower.top = r
        no StartingTower.top'
        EndingTower.top' = r
        no EndingTower.top
        no t.top
        no t.top'
        no r.below
        no r.below'
        no r.order
        Counter.counter = 0
        Counter.counter' = 1
    }
}
// some ring is moved
pred ringMoving[r: Ring] {
    r.below' != r.below or (some disj t1, t2: Tower | t1.top = r and t2.top' = r)
}
// for a trace done in the minimum number of moves, the smallest ring is moved every other step
pred smallestRingMovedEveryOtherTime {
    {always totalMoves until Counter.counter = 3 and always Counter.counter < 4} implies {
    some r: Ring | {
        no {Ring -> r & ^order} and {
            ringMoving[r] and next_state next_state {ringMoving[r]} 
        }
    }
    }
}
// eventually the first ring ends up on the third ring
pred firstRingOnTopofThird {
    eventually {
        some disj r1, r2, r3: Ring | {
            r1.order = r2
            r2.order = r3
            r1.below = r3
        }
    }
}
// eventually there is one ring per tower
pred ringsSpreadOut {
    eventually {
        some disj r1, r2, r3: Ring | no r1.below and no r2.below and no r3.below
    }
}
// eventually all rings stacked, not in starting or ending tower
pred ringsAllInMiddle {
    eventually {
        no StartingTower.top
        no EndingTower.top
        some t: Tower | t != StartingTower and t != EndingTower implies {
            all r: Ring | (r != t.top) implies t.top -> r in ^below
        }
    }
}

test suite for trace {
    assert orderAlwaysPreserved is necessary for trace
    assert ringsEndAtEndingTower is necessary for trace
    assert ringsStartAtStartingTower is necessary for trace
    assert oneRingMove is necessary for trace
    assert counterChangesProperly is necessary for trace
    assert smallestRingMovedEveryOtherTime is necessary for trace for exactly 2 Ring, 3 Tower

    test expect {
        // too many tops change (meaning more than one ring is moved)
        tooManyTowersTopChange: {tooManyTowersChange and trace} is unsat
        // can't solve puzzle in less than 3 moves
        minTraceTwoRings: {trace and always Counter.counter < 3} for exactly 2 Ring, 3 Tower is unsat
        // can solve puzzle in 3 moves
        twoRingTrace3Min: {trace and always Counter.counter < 4} for exactly 2 Ring, 3 Tower is sat
        // minimum number of towers needed for puzzle is 2
        minTowersTwo: {trace and minTowers2} is unsat
        // possible to stack first ring on third
        firstOnThird: {trace and firstRingOnTopofThird} is sat
        // possible that all rings are spread out
        ringsSpreadOutSat: {trace and ringsSpreadOut} is sat
        // possible that all rings are stacked but not in starting or ending
        ringsAllMiddle: {trace and ringsAllInMiddle} is sat
        // possible to have a one move trace
        oneMoveSat: {oneMoveTrace and trace} is sat

        // tests that take a long time to run (Alternatively, can verify with a run statement in model file):
        // minimum number of moves for 3 rings, 3 towers is 7
        // minTraceThreeRings: {trace and always Counter.counter < 7} for exactly 3 Ring, 3 Tower is unsat
        // // minimum number of moves for 3 rings, 4 towers is 5
        // minTraceThreeRingsFourTowers: {trace and always Counter.counter < 5} for exactly 3 Ring, 4 Tower is unsat
        //minimum number of moves for 4 rings, 4 towers is 9
        // minTraceFourRingsFourTowers: {trace and traceLessThan5} for exactly 3 Ring, 4 Tower is unsat
    }
}
