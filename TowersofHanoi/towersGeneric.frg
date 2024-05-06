#lang forge/temporal


option max_tracelength 20
option min_tracelength 6

sig Tower {
    var top: lone Ring
}
one sig StartingTower, EndingTower extends Tower{}

sig Ring {
    var below: lone Ring, // order on stack valid if top ring is bigger
    order: lone Ring
}

one sig Counter {
  var counter: one Int // counter for the number of moves
}

pred numRings[i: Int] {
    #{Ring} = i
}

pred initialOrder {
    StartingTower.top->(Ring - StartingTower.top) in ^order
    StartingTower.top->(Ring - StartingTower.top) in ^below
    not {some iden & ^order}
    ^below in ^order
}

pred init {
    // linearity
    initialOrder
    some StartingTower.top
    all t: Tower | (t != StartingTower) implies no t.top
    Counter.counter = 0
}

pred wellformed {
    // below must always follow the same sequence set by order
    {^below in ^order}
}

pred move {
    some disj t1, t2: Tower, r1: Ring {
        t1.top = r1
        t2.top' = r1
        r1.below' = t2.top
        t1.top' = r1.below 
        some r1.below' implies r1 -> r1.below' in ^order
        all t: Tower | (t != t1 and t != t2) implies t.top' = t.top
        all r: Ring | r != r1 implies r.below' = r.below // all other rings stay the same
    }
}

pred doNothing {
    Counter.counter' = Counter.counter
    all r: Ring | r.below' = r.below
    all t: Tower | t.top' = t.top
}

pred totalMoves {
    // I put this in a separate predicate becuase it was harder to debug within move
    move
    Counter.counter' = add[Counter.counter, 1]
}

pred endState {
    EndingTower.top->(Ring - EndingTower.top) in ^below
    some EndingTower.top
    all t: Tower | (t != EndingTower) implies no t.top
}

pred trace {
    init and always wellformed and always move and eventually endState
}

pred traceNotWell {
    init
    always move
    eventually endState
}

// test expect {
//     initSat: {init} is sat
//     wellformedSat: {always wellformed} is sat
//     moveSat: {always move} is sat 
//     endSat: {eventually endState} is sat
// }
run {init and always wellformed and always {totalMoves or doNothing} and eventually endState} for exactly 4 Ring, 3 Tower, 6 Int
