#lang forge/temporal

open "towersGeneric.frg"
open "magneticGeneric.frg"
open "bicolorGeneric.frg"

// Checks for correspondence between a move in the basic towers of hanoi simultaneously with the magnetic variation
// The two versions correspond when the number of rings on each tower are the same (a ring is moved)
pred BasicMagneticCorrespondence {
    #{EndingTower.top->(Ring - EndingTower.top)} =  #{MEndingTower.Mtop->(MRing - MEndingTower.Mtop)}
    #{StartingTower.top->(Ring - StartingTower.top)} =  #{MStartingTower.Mtop->(MRing - MStartingTower.Mtop)}
    all t: Tower | (t != StartingTower and t != EndingTower) implies {
      some m: MTower | #{t.top->(Ring - t.top)} = #{m.Mtop->(MRing - m.Mtop)}
    }
}

test expect {
  // if wellformed for magnetic is sat, then wellformed for basic towers is also sat, but the reverse is not true  
    basicMagneticCorres: {
      (traceNotWell and Mtrace and BasicMagneticCorrespondence) implies always wellformed
    } for exactly 3 Ring, exactly 3 MRing, exactly 3 Tower, exactly 3 MTower is theorem

    magneticBasicNoCorres: {
      (trace and MtraceNotWell and BasicMagneticCorrespondence) and not always Mwellformed
    } for exactly 3 Ring, 3 MRing, 3 Tower, 3 MTower is sat
}

// run {traceNotWell and Mtrace} for exactly 3 Ring, 3 MRing, 3 Tower, 3 MTower

// magnetic and bicolor
pred BicolorMagneticCorrespondence {
    #{BEndingTower.Btop->(BRing - BEndingTower.Btop)} =  #{MEndingTower.Mtop->(MRing - MEndingTower.Mtop)}
    #{BStartingTower.Btop->(BRing - BStartingTower.Btop)} =  #{MStartingTower.Mtop->(MRing - MStartingTower.Mtop)}
    all t: BTower | (t != BStartingTower and t != BEndingTower) implies {
      some m: MTower | #{t.Btop->(BRing - t.Btop)} = #{m.Mtop->(MRing - m.Mtop)}
    }
}

test expect {
  // no correspondance 
    bicolorMagneticCorres: { 
      (BtraceNotWell and Mtrace and BicolorMagneticCorrespondence) and not always Bwellformed
    } for exactly 3 BRing, exactly 3 MRing, exactly 3 BTower, exactly 3 MTower is sat
  
    magneticBicolorNoCorres: {
      (Btrace and MtraceNotWell and BicolorMagneticCorrespondence) and not always Mwellformed
    } for exactly 3 BRing, 3 MRing, 3 BTower, 3 MTower is sat
}



pred BasicBicolorCorrespondence {
    #{EndingTower.top->(Ring - EndingTower.top)} =  #{BEndingTower.Btop->(BRing - BEndingTower.Btop)}
    #{StartingTower.top->(Ring - StartingTower.top)} =  #{BStartingTower.Btop->(BRing - BStartingTower.Btop)}
    all t: Tower | (t != StartingTower and t != EndingTower) implies {
      some b: BTower | #{t.top->(Ring - t.top)} = #{b.Btop->(BRing - b.Btop)}
    }
}

test expect {
  // if wellformed for bicolor is sat, then wellformed for basic towers is also sat, but the reverse is not true  
    basicBicolorCorres: {
      (traceNotWell and Btrace and BasicBicolorCorrespondence) implies always wellformed
    } for exactly 3 Ring, exactly 3 BRing, exactly 3 Tower, exactly 3 BTower is theorem

    bicolorBasicNoCorres: {
      (trace and BtraceNotWell and BasicBicolorCorrespondence) and not always Bwellformed
    } for exactly 3 Ring, 3 BRing, 3 Tower, 3 BTower is sat
}
