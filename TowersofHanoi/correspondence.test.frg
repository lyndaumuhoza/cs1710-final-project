#lang forge/temporal

// open "towersGeneric.frg"
// open "magneticGeneric.frg"
// open "bicolorGeneric.frg"
open "Models/towers.frg"
open "Models/magneticTowers.frg"
open "Models/bicolorTowers.frg"



// // Checks for correspondence between a move in the basic towers of hanoi simultaneously with the magnetic variation
// // The two versions correspond when the number of rings on each tower are the same (a ring is moved)
pred BasicMagneticCorrespondence {
    some EndingTower.top iff some MEndingTower.Mtop
    some StartingTower.top iff some MStartingTower.Mtop
    some MidTower.top iff some MMidTower.Mtop
    #{EndingTower.top.^below} =  #{MEndingTower.Mtop.^Mbelow}
    #{StartingTower.top.^below} =  #{MStartingTower.Mtop.^Mbelow}
    #{MidTower.top.^below} =  #{MMidTower.Mtop.^Mbelow}
}

// test expect {
//   // if wellformed for magnetic is sat, then wellformed for basic towers is also sat, but the reverse is not true  
//     basicMagneticCorres: {
//       (traceNotWell and Mtrace and always BasicMagneticCorrespondence) implies always wellformed
//     } for exactly 3 Ring, exactly 3 MRing, exactly 3 Tower, exactly 3 MTower is theorem

//     magneticBasicNoCorres: {
//       (trace and MtraceNotWell and always BasicMagneticCorrespondence) and not always Mwellformed
//     } for exactly 3 Ring, 3 MRing, 3 Tower, 3 MTower is sat
// }

// // run {traceNotWell and Mtrace} for exactly 3 Ring, 3 MRing, 3 Tower, 3 MTower

// // magnetic and bicolor
pred BicolorMagneticCorrespondence {
    some BEndingTower.Btop iff some MEndingTower.Mtop
    some BStartingTower.Btop iff some MStartingTower.Mtop
    some BMidTower.Btop iff some MMidTower.Mtop
    #{BEndingTower.Btop.^Bbelow} =  #{MEndingTower.Mtop.^Mbelow}
    #{BStartingTower.Btop.^Bbelow} =  #{MStartingTower.Mtop.^Mbelow}
    #{BMidTower.Btop.^Bbelow} =  #{MMidTower.Mtop.^Mbelow}
}

// test expect {
//   // if wellformed for magnetic is sat, then wellformed for bicolor towers is also sat, but the reverse is not true 
//     bicolorMagneticCorres: { 
//       (BtraceNotWell and Mtrace and always BicolorMagneticCorrespondence) and not always Bwellformed
//     } for exactly 3 BRing, exactly 3 MRing, exactly 3 BTower, exactly 3 MTower is sat
  
//     magneticBicolorNoCorres: {
//       (Btrace and MtraceNotWell and always BicolorMagneticCorrespondence) and not always Mwellformed
//     } for exactly 3 BRing, 3 MRing, 3 BTower, 3 MTower is sat
// }



pred BasicBicolorCorrespondence {
    some EndingTower.top iff some BEndingTower.Btop
    some StartingTower.top iff some BStartingTower.Btop
    some MidTower.top iff some BMidTower.Btop
    #{EndingTower.top.^below} =  #{BEndingTower.Btop.^Bbelow}
    #{StartingTower.top.^below} =  #{BStartingTower.Btop.^Bbelow}
    #{MidTower.top.^below} =  #{BMidTower.Btop.^Bbelow}
}


// // // 2 minutes to run
// test expect {
//   // if wellformed for bicolor is sat, then wellformed for basic towers is also sat, but the resverse is not true
//     bicolorBasicCorres: {
//       (traceNotWell and Btrace and always BasicBicolorCorrespondence) implies always wellformed
//     } for exactly 3 Ring, exactly 3 BRing, exactly 3 Tower, exactly 3 BTower is theorem

//     bicolorBasicNoCorres: {
//       (trace and BtraceNotWell and always BasicBicolorCorrespondence) and not always Bwellformed
//     } for exactly 3 Ring, 3 BRing, 3 Tower, 3 BTower is sat
// }

// run bicolor trace (not wellformed) and magnetic trace (wellformed) and force traces to run in correspondence
run {BtraceNotWell and Mtrace and always BicolorMagneticCorrespondence} for exactly 3 BRing, 3 BTower, 3 MTower, 3 MRing

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