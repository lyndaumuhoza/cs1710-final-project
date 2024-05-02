#lang forge/temporal

open "towersv2.frg"
open "magneticGeneric.frg"

pred BMcorrespondence {
    #{EndingTower.top->(Ring - EndingTower.top)} =  #{MEndingTower.Mtop->(MRing - MEndingTower.Mtop)}
    #{StartingTower.top->(Ring - StartingTower.top)} =  #{MStartingTower.Mtop->(MRing - MStartingTower.Mtop)}
    all t: Tower | (t != StartingTower and t != EndingTower) implies {
      some m: MTower | #{t.top->(Ring - t.top)} = #{m.Mtop->(MRing - m.Mtop)}
    }
}

test expect {
    basicMagneticCorres: {
      (traceNotWell and Mtrace and BMcorrespondence) implies always wellformed
    } for exactly 3 Ring, exactly 3 MRing, exactly 3 Tower, exactly 3 MTower is theorem

    magneticBasicNoCorres: {
      (trace and MtraceNotWell and BMcorrespondence) and not always Mwellformed
    } for exactly 3 Ring, 3 MRing, 3 Tower, 3 MTower is sat
}

// run {traceNotWell and Mtrace} for exactly 3 Ring, 3 MRing, 3 Tower, 3 MTower

