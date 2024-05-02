#lang forge/temporal

open "towersGeneric.frg"

test suite for init {

}

test suite for wellformed {

}

test suite for move {

}


--------------------------------------------
pred allRingsInEndTower {
    all r: Ring | r != EndingTower.top implies EndingTower.top -> r in ^below
}
pred allRingInOrder {
    all r: Ring | some r.below implies r->r.below in ^order
}

test suite for endState {
    assert allRingsInEndTower is necessary for endState
    assert allRingInOrder is necessary for endState

    test expect {
        endStateExThreeRing: {
            some disj r1, r2, r3: Ring | {
                r1.below = r2 
                r2.below = r3
                r1.order = r2
                r2.order = r3
                no r3.below
                no r3.order
                EndingTower.top = r1
            }
        } for exactly 3 Ring is theorem
    }

}

