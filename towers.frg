#lang forge/temporal


option max_tracelength 13
option min_tracelength 6

abstract sig Tower {
    var top: lone Ring
}
one sig StartingTower, BasicTower, EndingTower extends Tower{}

abstract sig Ring {
    var below: lone Ring // order on stack valid if top ring is bigger
}

one sig Ring1, Ring2, Ring3 extends Ring {}



pred init {
    // linearity
    Ring1.below = Ring2
    Ring2.below = Ring3
    no Ring3.below 
    StartingTower.top = Ring1
    no BasicTower.top
    no EndingTower.top 
}

pred wellformed {
    all r: Ring | r.below != r
    Ring2.below != Ring1
    Ring3.below != Ring1 and Ring3.below != Ring2
}

pred move {
    //t1's top ring will be the next ring, t2's top ring will be t1's previous top ring
    some disj t1, t2, t3: Tower | {
        some t1.top
        t2.top' = t1.top
        t2.top'.below = t2.top
        t1.top' = t1.top.below 
        t3.top' = t3.top
        all r: Ring | r != t1.top implies r.below' = r.below // all other rings stay the same
    }
    
}

pred endState {
    Ring1.below = Ring2
    Ring2.below = Ring3
    no Ring3.below
    no StartingTower.top
    EndingTower.top = Ring1
}

test expect {
    initSat: {init} is sat
    wellformedSat: {always wellformed} is sat
    moveSat: {always move} is sat 
    endSat: {eventually endState} is sat
}
run {init and always move} for exactly 3 Ring