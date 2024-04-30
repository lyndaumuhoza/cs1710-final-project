#lang forge/temporal

open "towers.frg"
open "comparetowers.frg"

pred correspondence {
    #{EndingTower.top->(Ring - EndingTower.top)} =  #{EndingTower2.top2->(RingD - EndingTower2.top2)}
}

test expect {
    corres: {
      trace and trace2 and not always correspondence 
    } for exactly 3 Ring, exactly 2 StartingTower, 2 BasicTower, 2 EndingTower is unsat
}

