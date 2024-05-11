#lang forge/temporal

open "towers.frg"

------------------------------------------------------------------------------
// TEST SUITE SIMILAR TO OTHER "towers.test.frg" FILE, BUT MADE TO WORK WITH
// HARD-CODED VERSION (TO VERIFY BOTH MODEL VERSIONS)
-------------------------------------------------------------------------------

// PREDICATES FOR TESTING INIT

// there is some ring whose below field links to itself
pred someRingsLinkToSelf {
    some r: Ring  | r -> r in ^below
}
// all ring stacks follow the correct order (1 -> 2 -> 3)
pred allRingInOrder {
    Ring1.below = Ring2
    Ring2.below = Ring3
}
// the starting tower has some top ring
pred someStartingTop {
    some StartingTower.top
}
// all rings are in the starting tower
pred allRingInStartTower {
    StartingTower.top = Ring1
    StartingTower.top -> Ring2 in ^below
    StartingTower.top -> Ring3 in ^below
}
// there is one ring in the starting tower and no rings elsewhere
pred oneRingInStarting {
    some StartingTower.top
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
        // no cycles in below
        someCyclesInitUnsat: {init and someRingsLinkToSelf} is unsat
        // no rings makes init unsat
        noRingsInitUnsat: {#{Ring}=0 and init} is unsat

        // three rings where all are in starting tower and in order
        initExThreeRing: {
            some disj r1, r2, r3: Ring | {
                r1.below = r2 
                r2.below = r3
                no r3.below
                StartingTower.top = r1
                init
            }
        } is sat

        // three rings where all are in starting tower and not in order
        initExThreeRingUnordered: {
            some disj r1, r2: Ring | {
                r2.below = r1
                no r1.below
                StartingTower.top = r2
                init
            }
        } is unsat
    }
}

--------------------------------------------

// PREDICATES FOR TESTING WELLFORMED 

// there is a cycle between ring 1 and ring 2
pred someCycleInBelow {
    Ring1.below = Ring2
    Ring2.below = Ring1
}
// there are no rings in the model
pred noRings {
    #{Ring} = 0
}
// no rings are stacked 
pred noBelow {
    no ^below
}

test suite for wellformed {
    assert wellformed is necessary for trace
    assert noRings is sufficient for wellformed
    assert noBelow is sufficient for wellformed

    test expect {
        // basic sat test
        wellformedSat: {wellformed} is sat
        // not possible to have cycles in below
        someCycleInBelowUnsat: {wellformed and someCycleInBelow} is unsat
        // wellformed example: rings in diff towers
        wellformedRingDiffTower: {
            StartingTower.top = Ring1
            MidTower.top = Ring3
            EndingTower.top = Ring2
            no below
            wellformed
        } is sat

        // wellformed example: rings all in order and in same tower
        wellformedRingSameTower: {
            MidTower.top = Ring1
            Ring1.below = Ring2
            Ring2.below = Ring3
            wellformed
        } is sat

        // not-wellformed example: rings out of order
        notWellformedThreeRing: {
            Ring1.below = Ring3
            Ring3.below = Ring2
            wellformed
        } is unsat
        
    }
}

--------------------------------------------

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
    init and move implies {
        some r: Ring | {
            r.below' != r.below 
            all r1: Ring | r1 != r implies r1.below' = r1.below
        }
    }
}

// given a wellormed move, if there is no pre-defined order then there cannot be a stack
pred orderPreserved {
    wellformed and move implies {
        no Ring3.below 
        Ring2.below != Ring1
        all r: Ring | r -> r not in ^below
    }
}

// an example of moving the only ring in the model between two towers 
pred oneRingTwoTowerMove {
    no Ring1.below
    no Ring2.below
    no Ring3.below
    StartingTower.top = Ring1
    MidTower.top = Ring2
    EndingTower.top = Ring3
    no StartingTower.top'
    MidTower.top' = Ring1
    EndingTower.top' = Ring3
    Ring1.below' = Ring2
    no Ring2.below'
    no Ring3.below'
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
            StartingTower.top = Ring1
            no MidTower.top
            no EndingTower.top
            Ring1.below = Ring2
            Ring2.below = Ring3
            no Ring3.below

            StartingTower.top' = Ring2
            MidTower.top' = Ring1
            no EndingTower.top'
            no Ring1.below'
            Ring2.below' = Ring3
            no Ring3.below'

            init
            move
        } is sat

        // basic move moving smallest ring onto largest ring
        basicMoveEx: {
            no StartingTower.top
            MidTower.top = Ring1
            EndingTower.top = Ring3
            Ring1.below = Ring2
            no Ring2.below
            no Ring3.below

            no StartingTower.top'
            MidTower.top' = Ring2
            EndingTower.top' = Ring1
            Ring1.below' = Ring3
            no Ring2.below'
            no Ring3.below'

            move
        } is sat

        // move resulting in end state
        endingMoveEx: {
            no StartingTower.top 
            MidTower.top = Ring1
            EndingTower.top = Ring2
            no Ring1.below
            Ring2.below = Ring3
            no Ring3.below

            no StartingTower.top'
            no MidTower.top'
            EndingTower.top' = Ring1
            Ring1.below' = Ring2
            Ring2.below' = Ring3
            no Ring3.below'

            move
            next_state endState
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
    some EndingTower.top
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
            EndingTower.top = Ring1
            no MidTower.top
            no StartingTower.top
            Ring1.below = Ring2
            Ring2.below = Ring3
            no Ring3.below

            endState
        } is sat

        // three rings where all are in ending tower but not in order 
        // (sat but don't expect this in a trace)
        endStateExThreeRingUnordered: {
            EndingTower.top = Ring1
            no MidTower.top
            no StartingTower.top
            Ring1.below = Ring3
            Ring3.below = Ring2
            no Ring2.below

            endState
        } is unsat


        // three rings where all are in ending tower but there is a cycle in below
        // (sat but don't expect this in a trace)
        endStateExThreeRingCycled: {
            EndingTower.top = Ring1
            no MidTower.top
            no StartingTower.top
            Ring1.below = Ring2
            Ring2.below = Ring3
            Ring3.below = Ring3

            endState
        } is unsat
    }

}

--------------------------------------------

// PREDICATES FOR TESTING TRACE

// the size order is always maintained
pred orderAlwaysPreserved {
    always {
        no Ring3.below 
        Ring2.below != Ring1
        all r: Ring | r -> r not in ^below
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
// there are fewer than 3 towers, and more than 1 ring in the model
pred minTowers3 {
    #{Tower} < 3
    #{Ring} > 1
}
// eventually the first ring ends up on the third ring
pred firstRingOnTopofThird {
    eventually {
        Ring1.below = Ring3
    }
}
// eventually there is one ring per tower
pred ringsSpreadOut {
    eventually {
        no Ring1.below and no Ring2.below and no Ring3.below
    }
}

test suite for trace {
    assert orderAlwaysPreserved is necessary for trace
    assert ringsEndAtEndingTower is necessary for trace
    assert ringsStartAtStartingTower is necessary for trace
    assert oneRingMove is necessary for trace

    test expect {
        // too many tops change (meaning more than one ring is moved)
        tooManyTowersTopChange: {tooManyTowersChange and trace} is unsat
        // minimum number of towers needed for our model is 3
        minTowersTwo: {trace and minTowers3} is unsat
        // possible to stack first ring on third
        firstOnThird: {trace and firstRingOnTopofThird} is sat
        // possible that all rings are spread out
        ringsSpreadOutSat: {trace and ringsSpreadOut} is sat
    }
}