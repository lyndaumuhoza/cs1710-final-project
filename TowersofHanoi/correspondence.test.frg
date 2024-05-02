#lang forge/temporal

open "towersGeneric.frg"
open "magneticGeneric.frg"

// Checks for correspondence between a move in the basic towers of hanoi simultaneously with the magnetic variation
// The two versions correspond when the number of rings on each tower are the same (a ring is moved)
pred BMCorrespondence {
    #{EndingTower.top->(Ring - EndingTower.top)} =  #{MEndingTower.Mtop->(MRing - MEndingTower.Mtop)}
    #{StartingTower.top->(Ring - StartingTower.top)} =  #{MStartingTower.Mtop->(MRing - MStartingTower.Mtop)}
    all t: Tower | (t != StartingTower and t != EndingTower) implies {
      some m: MTower | #{t.top->(Ring - t.top)} = #{m.Mtop->(MRing - m.Mtop)}
    }
}

test expect {
  // if wellformed for magnetic is sat, then wellformed for basic towers is also sat, but th reverse is not true  
    basicMagneticCorres: {
      (traceNotWell and Mtrace and BMcorrespondence) implies always wellformed
    } for exactly 3 Ring, exactly 3 MRing, exactly 3 Tower, exactly 3 MTower is theorem

    magneticBasicNoCorres: {
      (trace and MtraceNotWell and BMcorrespondence) and not always Mwellformed
    } for exactly 3 Ring, 3 MRing, 3 Tower, 3 MTower is sat
}

// run {traceNotWell and Mtrace} for exactly 3 Ring, 3 MRing, 3 Tower, 3 MTower

