import cubical_indecomposability.data

/-!
# A small exact separating-support search

For each vertex label, inspect at most four facets whose common labels isolate that
vertex, choosing the first one that does not contain the second label. The balanced dispatch
avoids searching a large table during kernel reduction.  It supplies a
candidate only: all separating properties are proved independently by the
finite kernel certificates in `Certificates/Separation*`.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace CubicalIndecomposability

def separatingWitness (v w : Fin 144) : Fin 130 :=
  if v.val < 72 then
    if v.val < 36 then
      if v.val < 18 then
        if v.val < 9 then
          if v.val < 4 then
            if v.val < 2 then
              if v.val < 1 then
                (if incident 2 w then (if incident 15 w then 18 else 15) else 2)
              else
                (if incident 2 w then 66 else 2)
            else
              if v.val < 3 then
                (if incident 0 w then (if incident 3 w then 11 else 3) else 0)
              else
                (if incident 0 w then 67 else 0)
          else
            if v.val < 6 then
              if v.val < 5 then
                (if incident 15 w then (if incident 16 w then 19 else 16) else 15)
              else
                (if incident 14 w then 65 else 14)
            else
              if v.val < 7 then
                (if incident 0 w then (if incident 3 w then 19 else 3) else 0)
              else
                if v.val < 8 then
                  (if incident 0 w then 68 else 0)
                else
                  (if incident 2 w then 22 else 2)
        else
          if v.val < 13 then
            if v.val < 11 then
              if v.val < 10 then
                (if incident 2 w then 78 else 2)
              else
                (if incident 3 w then 22 else 3)
            else
              if v.val < 12 then
                (if incident 3 w then 82 else 3)
              else
                (if incident 4 w then 35 else 4)
          else
            if v.val < 15 then
              if v.val < 14 then
                (if incident 4 w then 65 else 4)
              else
                (if incident 3 w then 27 else 3)
            else
              if v.val < 16 then
                (if incident 3 w then 71 else 3)
              else
                if v.val < 17 then
                  (if incident 2 w then (if incident 8 w then 11 else 8) else 2)
                else
                  (if incident 1 w then (if incident 2 w then 8 else 2) else 1)
      else
        if v.val < 27 then
          if v.val < 22 then
            if v.val < 20 then
              if v.val < 19 then
                (if incident 0 w then (if incident 8 w then 11 else 8) else 0)
              else
                (if incident 0 w then (if incident 1 w then 8 else 1) else 0)
            else
              if v.val < 21 then
                (if incident 7 w then (if incident 16 w then 18 else 16) else 7)
              else
                (if incident 7 w then (if incident 13 w then 16 else 13) else 7)
          else
            if v.val < 24 then
              if v.val < 23 then
                (if incident 0 w then (if incident 7 w then 18 else 7) else 0)
              else
                (if incident 0 w then (if incident 7 w then 13 else 7) else 0)
            else
              if v.val < 25 then
                (if incident 2 w then 32 else 2)
              else
                if v.val < 26 then
                  (if incident 1 w then 45 else 1)
                else
                  (if incident 9 w then 32 else 9)
        else
          if v.val < 31 then
            if v.val < 29 then
              if v.val < 28 then
                (if incident 1 w then 46 else 1)
              else
                (if incident 4 w then 41 else 4)
            else
              if v.val < 30 then
                (if incident 5 w then 61 else 5)
              else
                (if incident 6 w then 41 else 6)
          else
            if v.val < 33 then
              if v.val < 32 then
                (if incident 5 w then 49 else 5)
              else
                (if incident 23 w then (if incident 37 w then 40 else 37) else 23)
            else
              if v.val < 34 then
                (if incident 22 w then (if incident 34 w then 38 else 34) else 22)
              else
                if v.val < 35 then
                  (if incident 21 w then (if incident 24 w then 32 else 24) else 21)
                else
                  (if incident 21 w then (if incident 22 w then 24 else 22) else 21)
    else
      if v.val < 54 then
        if v.val < 45 then
          if v.val < 40 then
            if v.val < 38 then
              if v.val < 37 then
                (if incident 37 w then (if incident 38 w then 41 else 38) else 37)
              else
                (if incident 34 w then (if incident 35 w then 38 else 35) else 34)
            else
              if v.val < 39 then
                (if incident 21 w then (if incident 24 w then 41 else 24) else 21)
              else
                (if incident 21 w then (if incident 24 w then 35 else 24) else 21)
          else
            if v.val < 42 then
              if v.val < 41 then
                (if incident 23 w then 44 else 23)
              else
                (if incident 22 w then (if incident 25 w then 34 else 25) else 22)
            else
              if v.val < 43 then
                (if incident 24 w then 44 else 24)
              else
                if v.val < 44 then
                  (if incident 22 w then (if incident 24 w then 26 else 24) else 22)
                else
                  (if incident 25 w then 57 else 25)
        else
          if v.val < 49 then
            if v.val < 47 then
              if v.val < 46 then
                (if incident 25 w then (if incident 34 w then 35 else 34) else 25)
              else
                (if incident 24 w then 49 else 24)
            else
              if v.val < 48 then
                (if incident 24 w then (if incident 26 w then 27 else 26) else 24)
              else
                (if incident 23 w then (if incident 29 w then 32 else 29) else 23)
          else
            if v.val < 51 then
              if v.val < 50 then
                (if incident 22 w then (if incident 23 w then 29 else 23) else 22)
              else
                (if incident 21 w then (if incident 29 w then 32 else 29) else 21)
            else
              if v.val < 52 then
                (if incident 21 w then (if incident 22 w then 29 else 22) else 21)
              else
                if v.val < 53 then
                  (if incident 28 w then (if incident 38 w then 40 else 38) else 28)
                else
                  (if incident 28 w then (if incident 35 w then 38 else 35) else 28)
      else
        if v.val < 63 then
          if v.val < 58 then
            if v.val < 56 then
              if v.val < 55 then
                (if incident 21 w then (if incident 28 w then 40 else 28) else 21)
              else
                (if incident 21 w then (if incident 28 w then 35 else 28) else 21)
            else
              if v.val < 57 then
                (if incident 45 w then (if incident 59 w then 62 else 59) else 45)
              else
                (if incident 44 w then (if incident 56 w then 60 else 56) else 44)
          else
            if v.val < 60 then
              if v.val < 59 then
                (if incident 43 w then (if incident 46 w then 54 else 46) else 43)
              else
                (if incident 43 w then (if incident 44 w then 46 else 44) else 43)
            else
              if v.val < 61 then
                (if incident 59 w then (if incident 60 w then 63 else 60) else 59)
              else
                if v.val < 62 then
                  (if incident 56 w then (if incident 57 w then 60 else 57) else 56)
                else
                  (if incident 43 w then (if incident 46 w then 63 else 46) else 43)
        else
          if v.val < 67 then
            if v.val < 65 then
              if v.val < 64 then
                (if incident 43 w then (if incident 46 w then 57 else 46) else 43)
              else
                (if incident 44 w then (if incident 47 w then 56 else 47) else 44)
            else
              if v.val < 66 then
                (if incident 44 w then (if incident 46 w then 48 else 46) else 44)
              else
                (if incident 47 w then (if incident 56 w then 57 else 56) else 47)
          else
            if v.val < 69 then
              if v.val < 68 then
                (if incident 46 w then (if incident 48 w then 49 else 48) else 46)
              else
                (if incident 45 w then (if incident 51 w then 54 else 51) else 45)
            else
              if v.val < 70 then
                (if incident 44 w then (if incident 45 w then 51 else 45) else 44)
              else
                if v.val < 71 then
                  (if incident 43 w then (if incident 51 w then 54 else 51) else 43)
                else
                  (if incident 43 w then (if incident 44 w then 51 else 44) else 43)
  else
    if v.val < 108 then
      if v.val < 90 then
        if v.val < 81 then
          if v.val < 76 then
            if v.val < 74 then
              if v.val < 73 then
                (if incident 50 w then (if incident 60 w then 62 else 60) else 50)
              else
                (if incident 50 w then (if incident 57 w then 60 else 57) else 50)
            else
              if v.val < 75 then
                (if incident 43 w then (if incident 50 w then 62 else 50) else 43)
              else
                (if incident 43 w then (if incident 50 w then 57 else 50) else 43)
          else
            if v.val < 78 then
              if v.val < 77 then
                (if incident 67 w then (if incident 80 w then 83 else 80) else 67)
              else
                (if incident 65 w then (if incident 68 w then 76 else 68) else 65)
            else
              if v.val < 79 then
                (if incident 80 w then (if incident 81 w then 84 else 81) else 80)
              else
                if v.val < 80 then
                  (if incident 65 w then (if incident 68 w then 84 else 68) else 65)
                else
                  (if incident 67 w then 87 else 67)
        else
          if v.val < 85 then
            if v.val < 83 then
              if v.val < 82 then
                (if incident 68 w then 87 else 68)
              else
                (if incident 69 w then 100 else 69)
            else
              if v.val < 84 then
                (if incident 68 w then 92 else 68)
              else
                (if incident 67 w then (if incident 73 w then 76 else 73) else 67)
          else
            if v.val < 87 then
              if v.val < 86 then
                (if incident 66 w then (if incident 67 w then 73 else 67) else 66)
              else
                (if incident 65 w then (if incident 73 w then 76 else 73) else 65)
            else
              if v.val < 88 then
                (if incident 65 w then (if incident 66 w then 73 else 66) else 65)
              else
                if v.val < 89 then
                  (if incident 72 w then (if incident 81 w then 83 else 81) else 72)
                else
                  (if incident 72 w then (if incident 78 w then 81 else 78) else 72)
      else
        if v.val < 99 then
          if v.val < 94 then
            if v.val < 92 then
              if v.val < 91 then
                (if incident 65 w then (if incident 72 w then 83 else 72) else 65)
              else
                (if incident 65 w then (if incident 72 w then 78 else 72) else 65)
            else
              if v.val < 93 then
                (if incident 67 w then 97 else 67)
              else
                (if incident 66 w then 110 else 66)
          else
            if v.val < 96 then
              if v.val < 95 then
                (if incident 74 w then 97 else 74)
              else
                (if incident 66 w then 111 else 66)
            else
              if v.val < 97 then
                (if incident 69 w then 106 else 69)
              else
                if v.val < 98 then
                  (if incident 70 w then 126 else 70)
                else
                  (if incident 71 w then 106 else 71)
        else
          if v.val < 103 then
            if v.val < 101 then
              if v.val < 100 then
                (if incident 70 w then 114 else 70)
              else
                (if incident 88 w then (if incident 102 w then 105 else 102) else 88)
            else
              if v.val < 102 then
                (if incident 87 w then (if incident 99 w then 103 else 99) else 87)
              else
                (if incident 86 w then (if incident 89 w then 97 else 89) else 86)
          else
            if v.val < 105 then
              if v.val < 104 then
                (if incident 86 w then (if incident 87 w then 89 else 87) else 86)
              else
                (if incident 102 w then (if incident 103 w then 106 else 103) else 102)
            else
              if v.val < 106 then
                (if incident 99 w then (if incident 100 w then 103 else 100) else 99)
              else
                if v.val < 107 then
                  (if incident 86 w then (if incident 89 w then 106 else 89) else 86)
                else
                  (if incident 86 w then (if incident 89 w then 100 else 89) else 86)
    else
      if v.val < 126 then
        if v.val < 117 then
          if v.val < 112 then
            if v.val < 110 then
              if v.val < 109 then
                (if incident 88 w then 109 else 88)
              else
                (if incident 87 w then (if incident 90 w then 99 else 90) else 87)
            else
              if v.val < 111 then
                (if incident 89 w then 109 else 89)
              else
                (if incident 87 w then (if incident 89 w then 91 else 89) else 87)
          else
            if v.val < 114 then
              if v.val < 113 then
                (if incident 90 w then 122 else 90)
              else
                (if incident 90 w then (if incident 99 w then 100 else 99) else 90)
            else
              if v.val < 115 then
                (if incident 89 w then 114 else 89)
              else
                if v.val < 116 then
                  (if incident 89 w then (if incident 91 w then 92 else 91) else 89)
                else
                  (if incident 88 w then (if incident 94 w then 97 else 94) else 88)
        else
          if v.val < 121 then
            if v.val < 119 then
              if v.val < 118 then
                (if incident 87 w then (if incident 88 w then 94 else 88) else 87)
              else
                (if incident 86 w then (if incident 94 w then 97 else 94) else 86)
            else
              if v.val < 120 then
                (if incident 86 w then (if incident 87 w then 94 else 87) else 86)
              else
                (if incident 93 w then (if incident 103 w then 105 else 103) else 93)
          else
            if v.val < 123 then
              if v.val < 122 then
                (if incident 93 w then (if incident 100 w then 103 else 100) else 93)
              else
                (if incident 86 w then (if incident 93 w then 105 else 93) else 86)
            else
              if v.val < 124 then
                (if incident 86 w then (if incident 93 w then 100 else 93) else 86)
              else
                if v.val < 125 then
                  (if incident 110 w then (if incident 124 w then 127 else 124) else 110)
                else
                  (if incident 109 w then (if incident 121 w then 125 else 121) else 109)
      else
        if v.val < 135 then
          if v.val < 130 then
            if v.val < 128 then
              if v.val < 127 then
                (if incident 108 w then (if incident 111 w then 119 else 111) else 108)
              else
                (if incident 108 w then (if incident 109 w then 111 else 109) else 108)
            else
              if v.val < 129 then
                (if incident 124 w then (if incident 125 w then 128 else 125) else 124)
              else
                (if incident 121 w then (if incident 122 w then 125 else 122) else 121)
          else
            if v.val < 132 then
              if v.val < 131 then
                (if incident 108 w then (if incident 111 w then 128 else 111) else 108)
              else
                (if incident 108 w then (if incident 111 w then 122 else 111) else 108)
            else
              if v.val < 133 then
                (if incident 109 w then (if incident 112 w then 121 else 112) else 109)
              else
                if v.val < 134 then
                  (if incident 109 w then (if incident 111 w then 113 else 111) else 109)
                else
                  (if incident 112 w then (if incident 121 w then 122 else 121) else 112)
        else
          if v.val < 139 then
            if v.val < 137 then
              if v.val < 136 then
                (if incident 111 w then (if incident 113 w then 114 else 113) else 111)
              else
                (if incident 110 w then (if incident 116 w then 119 else 116) else 110)
            else
              if v.val < 138 then
                (if incident 109 w then (if incident 110 w then 116 else 110) else 109)
              else
                (if incident 108 w then (if incident 116 w then 119 else 116) else 108)
          else
            if v.val < 141 then
              if v.val < 140 then
                (if incident 108 w then (if incident 109 w then 116 else 109) else 108)
              else
                (if incident 115 w then (if incident 125 w then 127 else 125) else 115)
            else
              if v.val < 142 then
                (if incident 115 w then (if incident 122 w then 125 else 122) else 115)
              else
                if v.val < 143 then
                  (if incident 108 w then (if incident 115 w then 127 else 115) else 108)
                else
                  (if incident 108 w then (if incident 115 w then 122 else 115) else 108)

end CubicalIndecomposability
