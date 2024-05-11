#lang forge/temporal




option max_tracelength 20
option min_tracelength 6




// BICOLOR
abstract sig Color {}
one sig Black, White extends Color{}


// Tower sig keeps track of teh top ring in its stack
sig BTower {
  var Btop: lone BRing
}


// Starting tower is where all rings start, Ending tower is where all the rings should get to
one sig BStartingTower, BEndingTower extends BTower{}


// Ring keeps track of the ring immediately below it, the proper size order of rings
// and its color which never change
sig BRing {
  var Bbelow: lone BRing, // order on stack valid if top ring is bigger
  Border: lone BRing,
  col: one Color
}


// Counter that keeps track of how many moves were made
one sig BCounter {
var bcounter: one Int
}


// Establishes the proper size order of rings and forces all rings in the starting
// tower to be in order and ensures that ring colors are alternating
pred BinitialOrder {
  BStartingTower.Btop->(BRing - BStartingTower.Btop) in ^Border
  BStartingTower.Btop->(BRing - BStartingTower.Btop) in ^Bbelow
  not {some iden & ^Border}
  all r: BRing | some r.Bbelow implies r.col != r.Bbelow.col
  // no cycles
  ^Bbelow in ^Border
}


// Sets the initial order of rings in the starting tower, and ensures no other
// tower has a top ring.
pred Binit {
  // linearity
  BinitialOrder
  some BStartingTower.Btop
  all t: BTower | (t != BStartingTower) implies no t.Btop
  BCounter.bcounter = 0
}


// Ensures rings are always in order, and that ring colors are alternating
pred Bwellformed {
  // below must always follow the same sequence set by order
  {^Bbelow in ^Border}

  all r: BRing | {
      some r.Bbelow implies {
          r.col != r.Bbelow.col
      }
  }
}


// Defines the constraints to make a move. Two towers will have their tops changed
// to reflect this movement. The ring that moves also has to change the ring below it
// to the appropriate new ring. Ring colors should always be alternating.
pred Bmove {
  some disj t1, t2:BTower, r1:BRing {
      t1.Btop = r1
      t2.Btop' = r1
      r1.Bbelow' = t2.Btop
      t1.Btop' = r1.Bbelow
      some r1.Bbelow' implies {
          r1 -> r1.Bbelow' in ^Border
          r1.col != r1.Bbelow'.col
      }
      all t:BTower | (t != t1 and t != t2) implies t.Btop' = t.Btop
      all r: BRing | r != r1 implies {
          r.Bbelow' = r.Bbelow // all other rings stay the same
          r.col' = r.col
      }
  }
}


// predicate for BtraceNotWell for testing correspondance
pred BmoveNotWell {
  some disj t1, t2:BTower, r1:BRing {
      t1.Btop = r1
      t2.Btop' = r1
      r1.Bbelow' = t2.Btop
      t1.Btop' = r1.Bbelow
      all t:BTower | (t != t1 and t != t2) implies t.Btop' = t.Btop
      all r: BRing | r != r1 implies {
          r.Bbelow' = r.Bbelow // all other rings stay the same
      }
  }
}




// Allows for a transition where nothing is changed. Need this to ensure counter
// is able to stop in lasso trace.
pred BdoNothing {
  BCounter.bcounter' = BCounter.bcounter
  all r: BRing | r.Bbelow' = r.Bbelow
  all t: BTower | t.Btop' = t.Btop
}


// Makes a move, then ensures counter increments.
pred BtotalMoves {
  Bmove
  BCounter.bcounter' = add[BCounter.bcounter, 1]
}


// The end state, when the puzzle is satisfied. All rings should end up in the
// ending tower. All other towers should not have any top rings.
pred BendState {
  BEndingTower.Btop->(BRing - BEndingTower.Btop) in ^Bbelow
  some BEndingTower.Btop
  all t: BTower | (t != BEndingTower) implies no t.Btop
}


// A trace that solves the puzzle from init to endState
pred Btrace {
  Binit and always Bwellformed and always {BtotalMoves or BdoNothing} and eventually BendState
}

// Trace for correspondace testing purposes
pred BtraceNotWell {
  Binit and always BmoveNotWell and eventually BendState
}


// RUN STATEMENTS
// Minimum moves: 7
run {Btrace} for exactly 3 BRing, 3 BTower
