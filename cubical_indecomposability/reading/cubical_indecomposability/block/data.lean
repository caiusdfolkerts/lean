import verification_bundle

/-!
# Exact data for the normalized 32-vertex block

This is the rational block in Proposition 5, after the paper's normalization.
The source preparation stores inward normals; `normal` is their negative, so
the supporting convention agrees with the 144-vertex construction:
`normal[f][0] * x + ... + normal[f][3] * t + normal[f][4] ≤ 0`.
All coordinates and labels below are explicit constants.  Their required
properties are proved by kernel reduction and ordinary convex geometry.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace CubicalIndecomposability.Block

private def qTable : ℕ → (Fin 5 → ℤ) :=
  fun index =>
    if index < 16 then
      if index < 8 then
        if index < 4 then
          if index < 2 then
            if index < 1 then
              ![0, 0, 0, 51, 44]
            else
              ![0, 0, 0, 0, 1]
          else
            if index < 3 then
              ![272, -17, -17, 408, 420]
            else
              ![1, 0, 0, 0, 1]
        else
          if index < 6 then
            if index < 5 then
              ![0, 121, 0, 102, 88]
            else
              ![0, 1, 0, 0, 1]
          else
            if index < 7 then
              ![544, 1121, -34, 816, 840]
            else
              ![1, 1, 0, 0, 1]
      else
        if index < 12 then
          if index < 10 then
            if index < 9 then
              ![0, 0, 51, 51, 44]
            else
              ![0, 0, 1, 0, 1]
          else
            if index < 11 then
              ![272, -17, 510, 408, 420]
            else
              ![1, 0, 1, 0, 1]
        else
          if index < 14 then
            if index < 13 then
              ![0, 121, 102, 102, 88]
            else
              ![0, 1, 1, 0, 1]
          else
            if index < 15 then
              ![544, 1121, 1020, 816, 840]
            else
              ![1, 1, 1, 0, 1]
    else
      if index < 24 then
        if index < 20 then
          if index < 18 then
            if index < 17 then
              ![106344, -106344, -106344, 248829, 270380]
            else
              ![2499, -2499, -2499, 4998, 7342]
          else
            if index < 19 then
              ![1021370, -840665, -840665, 1946364, 2161442]
            else
              ![4220, -2499, -2499, 4998, 7342]
        else
          if index < 22 then
            if index < 21 then
              ![612612, 3096445, -612612, 2081514, 2116708]
            else
              ![102, 701, -102, 204, 584]
          else
            if index < 23 then
              ![9059368, 24668895, -4777918, 15835296, 17156752]
            else
              ![3196, 4907, -714, 1428, 4088]
      else
        if index < 28 then
          if index < 26 then
            if index < 25 then
              ![306306, -306306, 1813815, 1040757, 1058354]
            else
              ![51, -51, 408, 102, 292]
          else
            if index < 27 then
              ![4529684, -2388959, 14443030, 7917648, 8578376]
            else
              ![1598, -357, 2856, 714, 2044]
        else
          if index < 30 then
            if index < 29 then
              ![612612, 3096445, 3627630, 2081514, 2116708]
            else
              ![102, 701, 816, 204, 584]
          else
            if index < 31 then
              ![9059368, 24668895, 28886060, 15835296, 17156752]
            else
              ![3196, 4907, 5712, 1428, 4088]

def q (i : Fin 32) : Fin 5 → ℤ := qTable i.val

private def normalTable : ℕ → (Fin 5 → ℤ) :=
  fun index =>
    if index < 12 then
      if index < 6 then
        if index < 3 then
          if index < 1 then
            ![-1, 0, 0, 0, 0]
          else
            if index < 2 then
              ![0, 0, 0, -1, 0]
            else
              ![102, 0, 0, 37, -102]
        else
          if index < 4 then
            ![51, 0, 0, 176, -204]
          else
            if index < 5 then
              ![0, -13932, 774, -2908, -2499]
            else
              ![0, 0, 26316, -13138, -32181]
      else
        if index < 9 then
          if index < 7 then
            ![0, 105264, 0, -43582, -111129]
          else
            if index < 8 then
              ![0, 710532, -11276406, -2335124, -2006697]
            else
              ![-1, -1, 0, 0, 0]
        else
          if index < 10 then
            ![-102, 0, 51, -7, -51]
          else
            if index < 11 then
              ![-17, 34, 0, -11, -34]
            else
              ![-1, 0, -1, 0, 0]
    else
      if index < 18 then
        if index < 15 then
          if index < 13 then
            ![0, -2, 0, -1, 0]
          else
            if index < 14 then
              ![0, 0, 51, -58, -51]
            else
              ![0, 68, 0, -39, -68]
        else
          if index < 16 then
            ![0, 0, -2, -1, 0]
          else
            if index < 17 then
              ![357, -204, 0, 121, -357]
            else
              ![357, 0, 102, 107, -459]
      else
        if index < 21 then
          if index < 19 then
            ![357, 408, 0, -11, -765]
          else
            if index < 20 then
              ![357, 0, -204, 121, -357]
            else
              ![1241, -1564, 0, 4620, -5355]
        else
          if index < 22 then
            ![3723, 0, 2346, 13538, -18411]
          else
            if index < 23 then
              ![1241, 3128, 0, 3608, -8483]
            else
              ![1241, 0, -1564, 4620, -5355]

def normal (i : Fin 24) : Fin 5 → ℤ := normalTable i.val

private def facetLabelsTable : ℕ → (Finset (Fin 32)) :=
  fun index =>
    if index < 12 then
      if index < 6 then
        if index < 3 then
          if index < 1 then
            {0, 1, 4, 5, 8, 9, 12, 13}
          else
            if index < 2 then
              {1, 3, 5, 7, 9, 11, 13, 15}
            else
              {2, 3, 6, 7, 10, 11, 14, 15}
        else
          if index < 4 then
            {0, 2, 4, 6, 8, 10, 12, 14}
          else
            if index < 5 then
              {16, 17, 18, 19, 24, 25, 26, 27}
            else
              {24, 25, 26, 27, 28, 29, 30, 31}
      else
        if index < 9 then
          if index < 7 then
            {20, 21, 22, 23, 28, 29, 30, 31}
          else
            if index < 8 then
              {16, 17, 18, 19, 20, 21, 22, 23}
            else
              {0, 1, 8, 9, 16, 17, 24, 25}
        else
          if index < 10 then
            {8, 9, 12, 13, 24, 25, 28, 29}
          else
            if index < 11 then
              {4, 5, 12, 13, 20, 21, 28, 29}
            else
              {0, 1, 4, 5, 16, 17, 20, 21}
    else
      if index < 18 then
        if index < 15 then
          if index < 13 then
            {1, 3, 9, 11, 17, 19, 25, 27}
          else
            if index < 14 then
              {9, 11, 13, 15, 25, 27, 29, 31}
            else
              {5, 7, 13, 15, 21, 23, 29, 31}
        else
          if index < 16 then
            {1, 3, 5, 7, 17, 19, 21, 23}
          else
            if index < 17 then
              {2, 3, 10, 11, 18, 19, 26, 27}
            else
              {10, 11, 14, 15, 26, 27, 30, 31}
      else
        if index < 21 then
          if index < 19 then
            {6, 7, 14, 15, 22, 23, 30, 31}
          else
            if index < 20 then
              {2, 3, 6, 7, 18, 19, 22, 23}
            else
              {0, 2, 8, 10, 16, 18, 24, 26}
        else
          if index < 22 then
            {8, 10, 12, 14, 24, 26, 28, 30}
          else
            if index < 23 then
              {4, 6, 12, 14, 20, 22, 28, 30}
            else
              {0, 2, 4, 6, 16, 18, 20, 22}

def facetLabels (i : Fin 24) : Finset (Fin 32) := facetLabelsTable i.val

def incident (f : Fin 24) (v : Fin 32) : Prop := v ∈ facetLabels f

instance (f : Fin 24) (v : Fin 32) : Decidable (incident f v) :=
  inferInstanceAs (Decidable (v ∈ facetLabels f))

private def cubeVertexTable : ℕ → (Fin 8 → Fin 32) :=
  fun index =>
    if index < 12 then
      if index < 6 then
        if index < 3 then
          if index < 1 then
            ![0, 1, 4, 5, 8, 9, 12, 13]
          else
            if index < 2 then
              ![1, 3, 5, 7, 9, 11, 13, 15]
            else
              ![2, 3, 6, 7, 10, 11, 14, 15]
        else
          if index < 4 then
            ![0, 2, 4, 6, 8, 10, 12, 14]
          else
            if index < 5 then
              ![16, 17, 18, 19, 24, 25, 26, 27]
            else
              ![24, 25, 26, 27, 28, 29, 30, 31]
      else
        if index < 9 then
          if index < 7 then
            ![20, 21, 22, 23, 28, 29, 30, 31]
          else
            if index < 8 then
              ![16, 17, 18, 19, 20, 21, 22, 23]
            else
              ![0, 1, 8, 9, 16, 17, 24, 25]
        else
          if index < 10 then
            ![8, 9, 12, 13, 24, 25, 28, 29]
          else
            if index < 11 then
              ![4, 5, 12, 13, 20, 21, 28, 29]
            else
              ![0, 1, 4, 5, 16, 17, 20, 21]
    else
      if index < 18 then
        if index < 15 then
          if index < 13 then
            ![1, 3, 9, 11, 17, 19, 25, 27]
          else
            if index < 14 then
              ![9, 11, 13, 15, 25, 27, 29, 31]
            else
              ![5, 7, 13, 15, 21, 23, 29, 31]
        else
          if index < 16 then
            ![1, 3, 5, 7, 17, 19, 21, 23]
          else
            if index < 17 then
              ![2, 3, 10, 11, 18, 19, 26, 27]
            else
              ![10, 11, 14, 15, 26, 27, 30, 31]
      else
        if index < 21 then
          if index < 19 then
            ![6, 7, 14, 15, 22, 23, 30, 31]
          else
            if index < 20 then
              ![2, 3, 6, 7, 18, 19, 22, 23]
            else
              ![0, 2, 8, 10, 16, 18, 24, 26]
        else
          if index < 22 then
            ![8, 10, 12, 14, 24, 26, 28, 30]
          else
            if index < 23 then
              ![4, 6, 12, 14, 20, 22, 28, 30]
            else
              ![0, 2, 4, 6, 16, 18, 20, 22]

def cubeVertex (i : Fin 24) : Fin 8 → Fin 32 := cubeVertexTable i.val

private def neighborFacetTable : ℕ → (Fin 6 → Fin 24) :=
  fun index =>
    if index < 12 then
      if index < 6 then
        if index < 3 then
          if index < 1 then
            ![3, 1, 8, 10, 11, 9]
          else
            if index < 2 then
              ![0, 2, 12, 14, 15, 13]
            else
              ![3, 1, 16, 18, 19, 17]
        else
          if index < 4 then
            ![0, 2, 20, 22, 23, 21]
          else
            if index < 5 then
              ![20, 12, 8, 16, 7, 5]
            else
              ![21, 13, 9, 17, 4, 6]
      else
        if index < 9 then
          if index < 7 then
            ![22, 14, 10, 18, 7, 5]
          else
            if index < 8 then
              ![23, 15, 11, 19, 4, 6]
            else
              ![20, 12, 11, 9, 0, 4]
        else
          if index < 10 then
            ![21, 13, 8, 10, 0, 5]
          else
            if index < 11 then
              ![22, 14, 11, 9, 0, 6]
            else
              ![23, 15, 8, 10, 0, 7]
    else
      if index < 18 then
        if index < 15 then
          if index < 13 then
            ![8, 16, 15, 13, 1, 4]
          else
            if index < 14 then
              ![9, 17, 12, 14, 1, 5]
            else
              ![10, 18, 15, 13, 1, 6]
        else
          if index < 16 then
            ![11, 19, 12, 14, 1, 7]
          else
            if index < 17 then
              ![20, 12, 19, 17, 2, 4]
            else
              ![21, 13, 16, 18, 2, 5]
      else
        if index < 21 then
          if index < 19 then
            ![22, 14, 19, 17, 2, 6]
          else
            if index < 20 then
              ![23, 15, 16, 18, 2, 7]
            else
              ![8, 16, 23, 21, 3, 4]
        else
          if index < 22 then
            ![9, 17, 20, 22, 3, 5]
          else
            if index < 23 then
              ![10, 18, 23, 21, 3, 6]
            else
              ![11, 19, 20, 22, 3, 7]

def neighborFacet (i : Fin 24) : Fin 6 → Fin 24 := neighborFacetTable i.val

private def edgeVertexTable : ℕ → (Fin 2 → Fin 32) :=
  fun index =>
    if index < 40 then
      if index < 20 then
        if index < 10 then
          if index < 5 then
            if index < 2 then
              if index < 1 then
                ![0, 1]
              else
                ![0, 2]
            else
              if index < 3 then
                ![0, 4]
              else
                if index < 4 then
                  ![0, 8]
                else
                  ![0, 16]
          else
            if index < 7 then
              if index < 6 then
                ![1, 3]
              else
                ![1, 5]
            else
              if index < 8 then
                ![1, 9]
              else
                if index < 9 then
                  ![1, 17]
                else
                  ![2, 3]
        else
          if index < 15 then
            if index < 12 then
              if index < 11 then
                ![2, 6]
              else
                ![2, 10]
            else
              if index < 13 then
                ![2, 18]
              else
                if index < 14 then
                  ![3, 7]
                else
                  ![3, 11]
          else
            if index < 17 then
              if index < 16 then
                ![3, 19]
              else
                ![4, 5]
            else
              if index < 18 then
                ![4, 6]
              else
                if index < 19 then
                  ![4, 12]
                else
                  ![4, 20]
      else
        if index < 30 then
          if index < 25 then
            if index < 22 then
              if index < 21 then
                ![5, 7]
              else
                ![5, 13]
            else
              if index < 23 then
                ![5, 21]
              else
                if index < 24 then
                  ![6, 7]
                else
                  ![6, 14]
          else
            if index < 27 then
              if index < 26 then
                ![6, 22]
              else
                ![7, 15]
            else
              if index < 28 then
                ![7, 23]
              else
                if index < 29 then
                  ![8, 9]
                else
                  ![8, 10]
        else
          if index < 35 then
            if index < 32 then
              if index < 31 then
                ![8, 12]
              else
                ![8, 24]
            else
              if index < 33 then
                ![9, 11]
              else
                if index < 34 then
                  ![9, 13]
                else
                  ![9, 25]
          else
            if index < 37 then
              if index < 36 then
                ![10, 11]
              else
                ![10, 14]
            else
              if index < 38 then
                ![10, 26]
              else
                if index < 39 then
                  ![11, 15]
                else
                  ![11, 27]
    else
      if index < 60 then
        if index < 50 then
          if index < 45 then
            if index < 42 then
              if index < 41 then
                ![12, 13]
              else
                ![12, 14]
            else
              if index < 43 then
                ![12, 28]
              else
                if index < 44 then
                  ![13, 15]
                else
                  ![13, 29]
          else
            if index < 47 then
              if index < 46 then
                ![14, 15]
              else
                ![14, 30]
            else
              if index < 48 then
                ![15, 31]
              else
                if index < 49 then
                  ![16, 17]
                else
                  ![16, 18]
        else
          if index < 55 then
            if index < 52 then
              if index < 51 then
                ![16, 20]
              else
                ![16, 24]
            else
              if index < 53 then
                ![17, 19]
              else
                if index < 54 then
                  ![17, 21]
                else
                  ![17, 25]
          else
            if index < 57 then
              if index < 56 then
                ![18, 19]
              else
                ![18, 22]
            else
              if index < 58 then
                ![18, 26]
              else
                if index < 59 then
                  ![19, 23]
                else
                  ![19, 27]
      else
        if index < 70 then
          if index < 65 then
            if index < 62 then
              if index < 61 then
                ![20, 21]
              else
                ![20, 22]
            else
              if index < 63 then
                ![20, 28]
              else
                if index < 64 then
                  ![21, 23]
                else
                  ![21, 29]
          else
            if index < 67 then
              if index < 66 then
                ![22, 23]
              else
                ![22, 30]
            else
              if index < 68 then
                ![23, 31]
              else
                if index < 69 then
                  ![24, 25]
                else
                  ![24, 26]
        else
          if index < 75 then
            if index < 72 then
              if index < 71 then
                ![24, 28]
              else
                ![25, 27]
            else
              if index < 73 then
                ![25, 29]
              else
                if index < 74 then
                  ![26, 27]
                else
                  ![26, 30]
          else
            if index < 77 then
              if index < 76 then
                ![27, 31]
              else
                ![28, 29]
            else
              if index < 78 then
                ![28, 30]
              else
                if index < 79 then
                  ![29, 31]
                else
                  ![30, 31]

def edgeVertex (i : Fin 80) : Fin 2 → Fin 32 := edgeVertexTable i.val

def squareBit (k : Fin 6) (b : Fin 8) : Prop :=
  b.val / (2 ^ (k.val / 2)) % 2 = k.val % 2

instance (k : Fin 6) (b : Fin 8) : Decidable (squareBit k b) :=
  inferInstanceAs (Decidable (b.val / (2 ^ (k.val / 2)) % 2 = k.val % 2))

def slackNumerator (f : Fin 24) (v : Fin 32) : ℤ :=
  -(normal f 0 * q v 0 + normal f 1 * q v 1 + normal f 2 * q v 2 +
    normal f 3 * q v 3 + normal f 4 * q v 4)

end CubicalIndecomposability.Block
