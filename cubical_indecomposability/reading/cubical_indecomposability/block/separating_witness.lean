import cubical_indecomposability.block.data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace CubicalIndecomposability.Block

/-- A candidate separating facet; every required property is checked in `Separation`. -/
def separatingWitness (v w : Fin 32) : Fin 24 :=
    if v.val < 16 then
      if v.val < 8 then
        if v.val < 4 then
          if v.val < 2 then
            if v.val < 1 then
              (if incident 0 w then (if incident 8 w then 23 else 8) else 0)
            else
              (if incident 0 w then (if incident 8 w then 15 else 8) else 0)
          else
            if v.val < 3 then
              (if incident 2 w then (if incident 16 w then 23 else 16) else 2)
            else
              (if incident 1 w then (if incident 12 w then 19 else 12) else 1)
        else
          if v.val < 6 then
            if v.val < 5 then
              (if incident 0 w then (if incident 10 w then 23 else 10) else 0)
            else
              (if incident 0 w then (if incident 10 w then 15 else 10) else 0)
          else
            if v.val < 7 then
              (if incident 2 w then (if incident 18 w then 23 else 18) else 2)
            else
              (if incident 1 w then (if incident 14 w then 19 else 14) else 1)
      else
        if v.val < 12 then
          if v.val < 10 then
            if v.val < 9 then
              (if incident 0 w then (if incident 8 w then 21 else 8) else 0)
            else
              (if incident 0 w then (if incident 8 w then 13 else 8) else 0)
          else
            if v.val < 11 then
              (if incident 2 w then (if incident 16 w then 21 else 16) else 2)
            else
              (if incident 1 w then (if incident 12 w then 17 else 12) else 1)
        else
          if v.val < 14 then
            if v.val < 13 then
              (if incident 0 w then (if incident 9 w then 22 else 9) else 0)
            else
              (if incident 0 w then (if incident 9 w then 14 else 9) else 0)
          else
            if v.val < 15 then
              (if incident 2 w then (if incident 17 w then 22 else 17) else 2)
            else
              (if incident 1 w then (if incident 13 w then 18 else 13) else 1)
    else
      if v.val < 24 then
        if v.val < 20 then
          if v.val < 18 then
            if v.val < 17 then
              (if incident 4 w then (if incident 8 w then 23 else 8) else 4)
            else
              (if incident 4 w then (if incident 8 w then 15 else 8) else 4)
          else
            if v.val < 19 then
              (if incident 4 w then (if incident 16 w then 23 else 16) else 4)
            else
              (if incident 4 w then (if incident 12 w then 19 else 12) else 4)
        else
          if v.val < 22 then
            if v.val < 21 then
              (if incident 6 w then (if incident 10 w then 23 else 10) else 6)
            else
              (if incident 6 w then (if incident 10 w then 15 else 10) else 6)
          else
            if v.val < 23 then
              (if incident 6 w then (if incident 18 w then 23 else 18) else 6)
            else
              (if incident 6 w then (if incident 14 w then 19 else 14) else 6)
      else
        if v.val < 28 then
          if v.val < 26 then
            if v.val < 25 then
              (if incident 4 w then (if incident 8 w then 21 else 8) else 4)
            else
              (if incident 4 w then (if incident 8 w then 13 else 8) else 4)
          else
            if v.val < 27 then
              (if incident 4 w then (if incident 16 w then 21 else 16) else 4)
            else
              (if incident 4 w then (if incident 12 w then 17 else 12) else 4)
        else
          if v.val < 30 then
            if v.val < 29 then
              (if incident 5 w then (if incident 9 w then 22 else 9) else 5)
            else
              (if incident 5 w then (if incident 9 w then 14 else 9) else 5)
          else
            if v.val < 31 then
              (if incident 5 w then (if incident 17 w then 22 else 17) else 5)
            else
              (if incident 5 w then (if incident 13 w then 18 else 13) else 5)

end CubicalIndecomposability.Block
