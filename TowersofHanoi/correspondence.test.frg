#lang forge/temporal


open "Models/towers.frg"
open "Models/magneticTowers.frg"
open "Models/bicolorTowers.frg"

------------------------------------------------------------------------------
// TEST SUITE LOOKING FOR CORRESPONDENCE. THESE TESTS CHECK WHETHER A TRACE
// FOR ONE MODEL WILL ALWAYS CORRESPOND TO ANOTHER (IF ONE MODEL IS WELLFORMED,
// WILL THE CORRESPONDING TRACE FOR ANOTHER MODEL ALSO BE WELLFORMED?)
-------------------------------------------------------------------------------


// Constrains basic and magnetic traces to run correspondingly. A corresponding move means the same ring is moved to the
// same tower (ex: Ring1 to EndingTower corresponds to MRing1 to MEndingTower)
pred BasicMagneticCorrespondence {
    some EndingTower.top iff some MEndingTower.Mtop
    some StartingTower.top iff some MStartingTower.Mtop
    some MidTower.top iff some MMidTower.Mtop
    #{EndingTower.top.^below} =  #{MEndingTower.Mtop.^Mbelow}
    #{StartingTower.top.^below} =  #{MStartingTower.Mtop.^Mbelow}
    #{MidTower.top.^below} =  #{MMidTower.Mtop.^Mbelow}
}

test expect {
    // if the magnetic trace is wellformed, the corresponding basic trace is guaranteed to be wellformed
    basicMagneticCorres: {
      (traceNotWell and Mtrace and always BasicMagneticCorrespondence) implies always wellformed
    } for exactly 3 Ring, exactly 3 MRing, exactly 3 Tower, exactly 3 MTower is theorem

    // if the basic trace is wellformed, the corresponding magnetic trace is not guaranteed to be wellformed
    magneticBasicNoCorres: {
      (trace and MtraceNotWell and always BasicMagneticCorrespondence) and not always Mwellformed
    } for exactly 3 Ring, 3 MRing, 3 Tower, 3 MTower is sat
}

// Constrains bicolor and magnetic traces to run correspondingly. A corresponding move means the same ring is moved to the
// same tower (ex: BRing1 to BEndingTower corresponds to MRing1 to MEndingTower)
pred BicolorMagneticCorrespondence {
    some BEndingTower.Btop iff some MEndingTower.Mtop
    some BStartingTower.Btop iff some MStartingTower.Mtop
    some BMidTower.Btop iff some MMidTower.Mtop
    #{BEndingTower.Btop.^Bbelow} =  #{MEndingTower.Mtop.^Mbelow}
    #{BStartingTower.Btop.^Bbelow} =  #{MStartingTower.Mtop.^Mbelow}
    #{BMidTower.Btop.^Bbelow} =  #{MMidTower.Mtop.^Mbelow}
}

test expect {
    // if the magnetic trace is wellformed, the corresponding bicolor trace is not guaranteed to be wellformed
    bicolorMagneticCorres: { 
      (BtraceNotWell and Mtrace and always BicolorMagneticCorrespondence) and not always Bwellformed
    } for exactly 3 BRing, exactly 3 MRing, exactly 3 BTower, exactly 3 MTower is sat
  
    // if bicolor trace is wellformed, the corresponding magnetic trace is not guaranteed to be wellformed 
    magneticBicolorNoCorres: {
      (Btrace and MtraceNotWell and always BicolorMagneticCorrespondence) and not always Mwellformed
    } for exactly 3 BRing, 3 MRing, 3 BTower, 3 MTower is sat
}


// Constrains basic and bicolor traces to run correspondingly. A corresponding move means the same ring is moved to the
// same tower (ex: Ring1 to EndingTower corresponds to BRing1 to BEndingTower)
pred BasicBicolorCorrespondence {
    some EndingTower.top iff some BEndingTower.Btop
    some StartingTower.top iff some BStartingTower.Btop
    some MidTower.top iff some BMidTower.Btop
    #{EndingTower.top.^below} =  #{BEndingTower.Btop.^Bbelow}
    #{StartingTower.top.^below} =  #{BStartingTower.Btop.^Bbelow}
    #{MidTower.top.^below} =  #{BMidTower.Btop.^Bbelow}
}


test expect {
    // if bicolor trace is wellformed, the corresponding basic trace is guaranteed to be wellformed
    bicolorBasicCorres: {
      (traceNotWell and Btrace and always BasicBicolorCorrespondence) implies always wellformed
    } for exactly 3 Ring, exactly 3 BRing, exactly 3 Tower, exactly 3 BTower is theorem

    // if basic trace is wellformed, the corresponding bicolor trace is not guaranteed to be wellformed 
    bicolorBasicNoCorres: {
      (trace and BtraceNotWell and always BasicBicolorCorrespondence) and not always Bwellformed
    } for exactly 3 Ring, 3 BRing, 3 Tower, 3 BTower is sat
}

// run bicolor trace (not wellformed) and magnetic trace (wellformed) and force traces to run in correspondence
// run {BtraceNotWell and Mtrace and always BicolorMagneticCorrespondence} for exactly 3 BRing, 3 BTower, 3 MTower, 3 MRing

// // run bicolor trace (wellformed) and magnetic trace (wellformed) and force traces to run in correspondence
// run {Btrace and MtraceNotWell and always BicolorMagneticCorrespondence} for exactly 3 BRing, 3 BTower, 3 MTower, 3 MRing

// run basic trace (wellformed) and magnetic trace (not wellformed) and force traces to run in correspondence
// run {trace and MtraceNotWell and always BasicMagneticCorrespondence} for exactly 3 Ring, 3 Tower, 3 MTower, 3 MRing

// // run basic trace (not wellformed) and magnetic trace (wellformed) and force traces to run in correspondence
// run {traceNotWell and Mtrace and always BasicMagneticCorrespondence} for exactly 3 Ring, 3 Tower, 3 MTower, 3 MRing

// // run bicolor trace (wellformed) and basic (not wellformed) and force traces to run in correspondence
// run {Btrace and traceNotWell and always BasicBicolorCorrespondence} for exactly 3 BRing, 3 BTower, 3 Tower, 3 Ring

// // run bicolor trace (not wellformed) and magnetic trace (wellformed) and force traces to run in correspondence
// run {BtraceNotWell and trace and always BasicBicolorCorrespondence} for exactly 3 BRing, 3 BTower, 3 MTower, 3 MRing