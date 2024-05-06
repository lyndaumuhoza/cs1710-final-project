#lang forge/temporal

open "towersGeneric.frg"

--------------------------------------------

// PREDICATES FOR TESTING INIT

pred someRingsLinkToSelf {
    some iden & ^order
}
pred someRingsLinkToSelfBelow {
    some iden & ^below
}
pred allRingInOrder {
    all r: Ring | some r.below implies r->r.below in ^order
}
pred someStartingTop {
    some StartingTower.top
}
pred allRingInStartTower {
    all r: Ring | r != StartingTower.top implies StartingTower.top -> r in ^order
}
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

pred noBelows {
    no ^below
}
pred noOrderNoBelow {
    no {^order} implies no {^below}
}
pred orderSmallerThanBelow {
    #{^order} < #{^below}
    #{^ order} > 0 // int wrapping issue if not included
}
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

--------------------------------------------

// PREDICATES FOR TESTING MOVE

pred oneTowerDecRing {
    some t: Tower | t.top' = t.top.below
}

pred ringMoveDiffTower {
    some disj t1, t2: Tower | t1.top' = t2.top
}

pred onlyOneRingMove {
    init and move and #{Ring} > 1 implies {
        some r: Ring | {
            r.below' != r.below 
            all r1: Ring | r1 != r implies r1.below' = r1.below
        }
    }
}

test suite for move {
    assert oneTowerDecRing is necessary for move
    assert ringMoveDiffTower is necessary for move
    assert onlyOneRingMove is necessary for move

    test expect {
        // basic sat test
        moveSat: {move} is sat
        // move doesn't work with only one tower
        moveOnetower: {move and #{Tower} = 1} is unsat
    }
}


--------------------------------------------

// PREDICATES FOR TESTING ENDSTATE 

pred allRingsInEndTower {
    all r: Ring | r != EndingTower.top implies EndingTower.top -> r in ^below
}
pred traceMustEndInOrder {
    {init and always move and eventually endState} implies allRingInOrder
}
pred someRingInStarting {
    some r: Ring | StartingTower.top = r
}
pred someRingInEndingTop {
    some EndingTower.top
}
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