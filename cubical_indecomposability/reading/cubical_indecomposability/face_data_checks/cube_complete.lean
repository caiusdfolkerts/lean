import cubical_indecomposability.face_data_checks.anchors
import Lean.Elab.Tactic.Omega

/-!
# Every face inside a listed facet has a cube code

An arbitrary catalogue face is nonempty. Choose one of its vertices, and
test containment only in the facets incident to that vertex. The exact
vertex/facet transpose and the anchor membership are proved below. Thus
the sparse search still covers every face and every facet.

The final numerical certificate traverses only the 3510 actual incidences.
Its explicit `Finset.decidableDforallFinset` instance recurses over the
members of the small finite set, and an explicit cube-code witness avoids
searching over the 27 possible codes. All numerical checks use Lean's
ordinary kernel reduction; the proposed data have no trusted status.

Regenerate with `python3 scripts/sparse_cube_complete.py`.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace CubicalIndecomposability

private def cubeIncidentFacetsTable : ℕ → Finset (Fin 130) :=
fun index =>
    if index < 72 then
      if index < 36 then
        if index < 18 then
          if index < 9 then
            if index < 4 then
              if index < 2 then
                if index < 1 then
                  {2, 11, 15, 16, 18, 20}
                else
                  {1, 2, 14, 15, 16, 66, 67, 79, 80, 81}
              else
                if index < 3 then
                  {0, 3, 11, 12, 18, 20}
                else
                  {0, 1, 3, 12, 14, 66, 67, 69, 70, 80}
            else
              if index < 6 then
                if index < 5 then
                  {15, 16, 17, 18, 19, 20}
                else
                  {13, 14, 15, 16, 17, 65, 66, 68, 77, 79}
              else
                if index < 7 then
                  {0, 3, 6, 18, 19, 20}
                else
                  if index < 8 then
                    {0, 3, 6, 13, 14, 66, 68, 70, 74, 77}
                  else
                    {2, 4, 11, 15, 20, 22, 23, 25, 26, 31}
          else
            if index < 13 then
              if index < 11 then
                if index < 10 then
                  {1, 2, 4, 5, 15, 78, 79, 80, 81, 82}
                else
                  {3, 9, 11, 12, 20, 22, 26, 30, 31, 33}
              else
                if index < 12 then
                  {1, 3, 5, 9, 12, 69, 70, 78, 80, 82}
                else
                  {4, 15, 17, 19, 20, 25, 26, 28, 35, 39}
            else
              if index < 15 then
                if index < 14 then
                  {4, 5, 13, 15, 17, 65, 68, 71, 78, 79}
                else
                  {3, 6, 9, 19, 20, 26, 27, 28, 30, 35}
              else
                if index < 16 then
                  {3, 5, 6, 9, 13, 68, 70, 71, 74, 78}
                else
                  if index < 17 then
                    {2, 8, 10, 11, 16, 18}
                  else
                    {1, 2, 8, 10, 14, 16}
        else
          if index < 27 then
            if index < 22 then
              if index < 20 then
                if index < 19 then
                  {0, 8, 10, 11, 12, 18}
                else
                  {0, 1, 8, 10, 12, 14}
              else
                if index < 21 then
                  {7, 8, 16, 17, 18, 19}
                else
                  {7, 8, 13, 14, 16, 17}
            else
              if index < 24 then
                if index < 23 then
                  {0, 6, 7, 8, 18, 19}
                else
                  {0, 6, 7, 8, 13, 14}
              else
                if index < 25 then
                  {2, 4, 10, 11, 23, 25, 31, 32, 45, 47, 53, 54}
                else
                  if index < 26 then
                    {1, 2, 4, 5, 10, 45, 47, 54, 59, 64}
                  else
                    {9, 10, 11, 12, 30, 31, 32, 33, 52, 53, 54, 55}
          else
            if index < 31 then
              if index < 29 then
                if index < 28 then
                  {1, 5, 9, 10, 12, 46, 52, 54, 55, 64}
                else
                  {4, 7, 17, 19, 25, 28, 39, 41, 47, 50, 61, 63}
              else
                if index < 30 then
                  {4, 5, 7, 13, 17, 47, 59, 61, 63, 64}
                else
                  {6, 7, 9, 19, 27, 28, 30, 41, 49, 50, 52, 63}
            else
              if index < 33 then
                if index < 32 then
                  {5, 6, 7, 9, 13, 46, 49, 52, 63, 64}
                else
                  {23, 32, 37, 38, 40, 42}
              else
                if index < 34 then
                  {22, 23, 34, 36, 37, 38}
                else
                  if index < 35 then
                    {21, 24, 32, 33, 40, 42}
                  else
                    {21, 22, 24, 33, 34, 36}
      else
        if index < 54 then
          if index < 45 then
            if index < 40 then
              if index < 38 then
                if index < 37 then
                  {37, 38, 39, 40, 41, 42}
                else
                  {34, 35, 36, 37, 38, 39}
              else
                if index < 39 then
                  {21, 24, 27, 40, 41, 42}
                else
                  {21, 24, 27, 34, 35, 36}
            else
              if index < 42 then
                if index < 41 then
                  {23, 25, 32, 37, 42, 44, 45, 47, 48, 53}
                else
                  {22, 23, 25, 26, 34, 37}
              else
                if index < 43 then
                  {24, 30, 32, 33, 42, 44, 48, 52, 53, 55}
                else
                  if index < 44 then
                    {22, 24, 26, 30, 33, 34}
                  else
                    {25, 37, 39, 41, 42, 47, 48, 50, 57, 61}
          else
            if index < 49 then
              if index < 47 then
                if index < 46 then
                  {25, 26, 34, 35, 37, 39}
                else
                  {24, 27, 30, 41, 42, 48, 49, 50, 52, 57}
              else
                if index < 48 then
                  {24, 26, 27, 30, 34, 35}
                else
                  {23, 29, 31, 32, 38, 40}
            else
              if index < 51 then
                if index < 50 then
                  {22, 23, 29, 31, 36, 38}
                else
                  {21, 29, 31, 32, 33, 40}
              else
                if index < 52 then
                  {21, 22, 29, 31, 33, 36}
                else
                  if index < 53 then
                    {28, 29, 38, 39, 40, 41}
                  else
                    {28, 29, 35, 36, 38, 39}
        else
          if index < 63 then
            if index < 58 then
              if index < 56 then
                if index < 55 then
                  {21, 27, 28, 29, 40, 41}
                else
                  {21, 27, 28, 29, 35, 36}
              else
                if index < 57 then
                  {45, 54, 59, 60, 62, 64}
                else
                  {44, 45, 56, 58, 59, 60}
            else
              if index < 60 then
                if index < 59 then
                  {43, 46, 54, 55, 62, 64}
                else
                  {43, 44, 46, 55, 56, 58}
              else
                if index < 61 then
                  {59, 60, 61, 62, 63, 64}
                else
                  if index < 62 then
                    {56, 57, 58, 59, 60, 61}
                  else
                    {43, 46, 49, 62, 63, 64}
          else
            if index < 67 then
              if index < 65 then
                if index < 64 then
                  {43, 46, 49, 56, 57, 58}
                else
                  {44, 45, 47, 48, 56, 59}
              else
                if index < 66 then
                  {44, 46, 48, 52, 55, 56}
                else
                  {47, 48, 56, 57, 59, 61}
            else
              if index < 69 then
                if index < 68 then
                  {46, 48, 49, 52, 56, 57}
                else
                  {45, 51, 53, 54, 60, 62}
              else
                if index < 70 then
                  {44, 45, 51, 53, 58, 60}
                else
                  if index < 71 then
                    {43, 51, 53, 54, 55, 62}
                  else
                    {43, 44, 51, 53, 55, 58}
    else
      if index < 108 then
        if index < 90 then
          if index < 81 then
            if index < 76 then
              if index < 74 then
                if index < 73 then
                  {50, 51, 60, 61, 62, 63}
                else
                  {50, 51, 57, 58, 60, 61}
              else
                if index < 75 then
                  {43, 49, 50, 51, 62, 63}
                else
                  {43, 49, 50, 51, 57, 58}
            else
              if index < 78 then
                if index < 77 then
                  {67, 76, 80, 81, 83, 85}
                else
                  {65, 68, 76, 77, 83, 85}
              else
                if index < 79 then
                  {80, 81, 82, 83, 84, 85}
                else
                  if index < 80 then
                    {65, 68, 71, 83, 84, 85}
                  else
                    {67, 69, 76, 80, 85, 87, 88, 90, 91, 96}
          else
            if index < 85 then
              if index < 83 then
                if index < 82 then
                  {68, 74, 76, 77, 85, 87, 91, 95, 96, 98}
                else
                  {69, 80, 82, 84, 85, 90, 91, 93, 100, 104}
              else
                if index < 84 then
                  {68, 71, 74, 84, 85, 91, 92, 93, 95, 100}
                else
                  {67, 73, 75, 76, 81, 83}
            else
              if index < 87 then
                if index < 86 then
                  {66, 67, 73, 75, 79, 81}
                else
                  {65, 73, 75, 76, 77, 83}
              else
                if index < 88 then
                  {65, 66, 73, 75, 77, 79}
                else
                  if index < 89 then
                    {72, 73, 81, 82, 83, 84}
                  else
                    {72, 73, 78, 79, 81, 82}
        else
          if index < 99 then
            if index < 94 then
              if index < 92 then
                if index < 91 then
                  {65, 71, 72, 73, 83, 84}
                else
                  {65, 71, 72, 73, 78, 79}
              else
                if index < 93 then
                  {67, 69, 75, 76, 88, 90, 96, 97, 110, 112, 118, 119}
                else
                  {66, 67, 69, 70, 75, 110, 112, 119, 124, 129}
            else
              if index < 96 then
                if index < 95 then
                  {74, 75, 76, 77, 95, 96, 97, 98, 117, 118, 119, 120}
                else
                  {66, 70, 74, 75, 77, 111, 117, 119, 120, 129}
              else
                if index < 97 then
                  {69, 72, 82, 84, 90, 93, 104, 106, 112, 115, 126, 128}
                else
                  if index < 98 then
                    {69, 70, 72, 78, 82, 112, 124, 126, 128, 129}
                  else
                    {71, 72, 74, 84, 92, 93, 95, 106, 114, 115, 117, 128}
          else
            if index < 103 then
              if index < 101 then
                if index < 100 then
                  {70, 71, 72, 74, 78, 111, 114, 117, 128, 129}
                else
                  {88, 97, 102, 103, 105, 107}
              else
                if index < 102 then
                  {87, 88, 99, 101, 102, 103}
                else
                  {86, 89, 97, 98, 105, 107}
            else
              if index < 105 then
                if index < 104 then
                  {86, 87, 89, 98, 99, 101}
                else
                  {102, 103, 104, 105, 106, 107}
              else
                if index < 106 then
                  {99, 100, 101, 102, 103, 104}
                else
                  if index < 107 then
                    {86, 89, 92, 105, 106, 107}
                  else
                    {86, 89, 92, 99, 100, 101}
      else
        if index < 126 then
          if index < 117 then
            if index < 112 then
              if index < 110 then
                if index < 109 then
                  {88, 90, 97, 102, 107, 109, 110, 112, 113, 118}
                else
                  {87, 88, 90, 91, 99, 102}
              else
                if index < 111 then
                  {89, 95, 97, 98, 107, 109, 113, 117, 118, 120}
                else
                  {87, 89, 91, 95, 98, 99}
            else
              if index < 114 then
                if index < 113 then
                  {90, 102, 104, 106, 107, 112, 113, 115, 122, 126}
                else
                  {90, 91, 99, 100, 102, 104}
              else
                if index < 115 then
                  {89, 92, 95, 106, 107, 113, 114, 115, 117, 122}
                else
                  if index < 116 then
                    {89, 91, 92, 95, 99, 100}
                  else
                    {88, 94, 96, 97, 103, 105}
          else
            if index < 121 then
              if index < 119 then
                if index < 118 then
                  {87, 88, 94, 96, 101, 103}
                else
                  {86, 94, 96, 97, 98, 105}
              else
                if index < 120 then
                  {86, 87, 94, 96, 98, 101}
                else
                  {93, 94, 103, 104, 105, 106}
            else
              if index < 123 then
                if index < 122 then
                  {93, 94, 100, 101, 103, 104}
                else
                  {86, 92, 93, 94, 105, 106}
              else
                if index < 124 then
                  {86, 92, 93, 94, 100, 101}
                else
                  if index < 125 then
                    {110, 119, 124, 125, 127, 129}
                  else
                    {109, 110, 121, 123, 124, 125}
        else
          if index < 135 then
            if index < 130 then
              if index < 128 then
                if index < 127 then
                  {108, 111, 119, 120, 127, 129}
                else
                  {108, 109, 111, 120, 121, 123}
              else
                if index < 129 then
                  {124, 125, 126, 127, 128, 129}
                else
                  {121, 122, 123, 124, 125, 126}
            else
              if index < 132 then
                if index < 131 then
                  {108, 111, 114, 127, 128, 129}
                else
                  {108, 111, 114, 121, 122, 123}
              else
                if index < 133 then
                  {109, 110, 112, 113, 121, 124}
                else
                  if index < 134 then
                    {109, 111, 113, 117, 120, 121}
                  else
                    {112, 113, 121, 122, 124, 126}
          else
            if index < 139 then
              if index < 137 then
                if index < 136 then
                  {111, 113, 114, 117, 121, 122}
                else
                  {110, 116, 118, 119, 125, 127}
              else
                if index < 138 then
                  {109, 110, 116, 118, 123, 125}
                else
                  {108, 116, 118, 119, 120, 127}
            else
              if index < 141 then
                if index < 140 then
                  {108, 109, 116, 118, 120, 123}
                else
                  {115, 116, 125, 126, 127, 128}
              else
                if index < 142 then
                  {115, 116, 122, 123, 125, 126}
                else
                  if index < 143 then
                    {108, 114, 115, 116, 127, 128}
                  else
                    {108, 114, 115, 116, 122, 123}

private def cubeIncidentFacets (v : Fin 144) : Finset (Fin 130) :=
  cubeIncidentFacetsTable v.val

private theorem transpose0000 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨0, by decide⟩ : Fin 144) ↔ (⟨0, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0001 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨1, by decide⟩ : Fin 144) ↔ (⟨1, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0002 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨2, by decide⟩ : Fin 144) ↔ (⟨2, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0003 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨3, by decide⟩ : Fin 144) ↔ (⟨3, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0004 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨4, by decide⟩ : Fin 144) ↔ (⟨4, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0005 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨5, by decide⟩ : Fin 144) ↔ (⟨5, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0006 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨6, by decide⟩ : Fin 144) ↔ (⟨6, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0007 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨7, by decide⟩ : Fin 144) ↔ (⟨7, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0008 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨8, by decide⟩ : Fin 144) ↔ (⟨8, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0009 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨9, by decide⟩ : Fin 144) ↔ (⟨9, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0010 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨10, by decide⟩ : Fin 144) ↔ (⟨10, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0011 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨11, by decide⟩ : Fin 144) ↔ (⟨11, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0012 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨12, by decide⟩ : Fin 144) ↔ (⟨12, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0013 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨13, by decide⟩ : Fin 144) ↔ (⟨13, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0014 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨14, by decide⟩ : Fin 144) ↔ (⟨14, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0015 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨15, by decide⟩ : Fin 144) ↔ (⟨15, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0016 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨16, by decide⟩ : Fin 144) ↔ (⟨16, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0017 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨17, by decide⟩ : Fin 144) ↔ (⟨17, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0018 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨18, by decide⟩ : Fin 144) ↔ (⟨18, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0019 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨19, by decide⟩ : Fin 144) ↔ (⟨19, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0020 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨20, by decide⟩ : Fin 144) ↔ (⟨20, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0021 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨21, by decide⟩ : Fin 144) ↔ (⟨21, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0022 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨22, by decide⟩ : Fin 144) ↔ (⟨22, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0023 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨23, by decide⟩ : Fin 144) ↔ (⟨23, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0024 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨24, by decide⟩ : Fin 144) ↔ (⟨24, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0025 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨25, by decide⟩ : Fin 144) ↔ (⟨25, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0026 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨26, by decide⟩ : Fin 144) ↔ (⟨26, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0027 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨27, by decide⟩ : Fin 144) ↔ (⟨27, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0028 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨28, by decide⟩ : Fin 144) ↔ (⟨28, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0029 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨29, by decide⟩ : Fin 144) ↔ (⟨29, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0030 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨30, by decide⟩ : Fin 144) ↔ (⟨30, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0031 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨31, by decide⟩ : Fin 144) ↔ (⟨31, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0032 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨32, by decide⟩ : Fin 144) ↔ (⟨32, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0033 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨33, by decide⟩ : Fin 144) ↔ (⟨33, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0034 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨34, by decide⟩ : Fin 144) ↔ (⟨34, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0035 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨35, by decide⟩ : Fin 144) ↔ (⟨35, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0036 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨36, by decide⟩ : Fin 144) ↔ (⟨36, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0037 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨37, by decide⟩ : Fin 144) ↔ (⟨37, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0038 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨38, by decide⟩ : Fin 144) ↔ (⟨38, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0039 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨39, by decide⟩ : Fin 144) ↔ (⟨39, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0040 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨40, by decide⟩ : Fin 144) ↔ (⟨40, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0041 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨41, by decide⟩ : Fin 144) ↔ (⟨41, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0042 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨42, by decide⟩ : Fin 144) ↔ (⟨42, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0043 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨43, by decide⟩ : Fin 144) ↔ (⟨43, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0044 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨44, by decide⟩ : Fin 144) ↔ (⟨44, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0045 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨45, by decide⟩ : Fin 144) ↔ (⟨45, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0046 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨46, by decide⟩ : Fin 144) ↔ (⟨46, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0047 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨47, by decide⟩ : Fin 144) ↔ (⟨47, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0048 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨48, by decide⟩ : Fin 144) ↔ (⟨48, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0049 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨49, by decide⟩ : Fin 144) ↔ (⟨49, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0050 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨50, by decide⟩ : Fin 144) ↔ (⟨50, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0051 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨51, by decide⟩ : Fin 144) ↔ (⟨51, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0052 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨52, by decide⟩ : Fin 144) ↔ (⟨52, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0053 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨53, by decide⟩ : Fin 144) ↔ (⟨53, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0054 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨54, by decide⟩ : Fin 144) ↔ (⟨54, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0055 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨55, by decide⟩ : Fin 144) ↔ (⟨55, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0056 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨56, by decide⟩ : Fin 144) ↔ (⟨56, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0057 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨57, by decide⟩ : Fin 144) ↔ (⟨57, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0058 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨58, by decide⟩ : Fin 144) ↔ (⟨58, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0059 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨59, by decide⟩ : Fin 144) ↔ (⟨59, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0060 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨60, by decide⟩ : Fin 144) ↔ (⟨60, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0061 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨61, by decide⟩ : Fin 144) ↔ (⟨61, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0062 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨62, by decide⟩ : Fin 144) ↔ (⟨62, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0063 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨63, by decide⟩ : Fin 144) ↔ (⟨63, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0064 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨64, by decide⟩ : Fin 144) ↔ (⟨64, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0065 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨65, by decide⟩ : Fin 144) ↔ (⟨65, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0066 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨66, by decide⟩ : Fin 144) ↔ (⟨66, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0067 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨67, by decide⟩ : Fin 144) ↔ (⟨67, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0068 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨68, by decide⟩ : Fin 144) ↔ (⟨68, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0069 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨69, by decide⟩ : Fin 144) ↔ (⟨69, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0070 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨70, by decide⟩ : Fin 144) ↔ (⟨70, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0071 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨71, by decide⟩ : Fin 144) ↔ (⟨71, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0072 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨72, by decide⟩ : Fin 144) ↔ (⟨72, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0073 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨73, by decide⟩ : Fin 144) ↔ (⟨73, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0074 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨74, by decide⟩ : Fin 144) ↔ (⟨74, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0075 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨75, by decide⟩ : Fin 144) ↔ (⟨75, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0076 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨76, by decide⟩ : Fin 144) ↔ (⟨76, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0077 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨77, by decide⟩ : Fin 144) ↔ (⟨77, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0078 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨78, by decide⟩ : Fin 144) ↔ (⟨78, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0079 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨79, by decide⟩ : Fin 144) ↔ (⟨79, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0080 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨80, by decide⟩ : Fin 144) ↔ (⟨80, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0081 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨81, by decide⟩ : Fin 144) ↔ (⟨81, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0082 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨82, by decide⟩ : Fin 144) ↔ (⟨82, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0083 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨83, by decide⟩ : Fin 144) ↔ (⟨83, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0084 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨84, by decide⟩ : Fin 144) ↔ (⟨84, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0085 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨85, by decide⟩ : Fin 144) ↔ (⟨85, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0086 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨86, by decide⟩ : Fin 144) ↔ (⟨86, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0087 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨87, by decide⟩ : Fin 144) ↔ (⟨87, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0088 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨88, by decide⟩ : Fin 144) ↔ (⟨88, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0089 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨89, by decide⟩ : Fin 144) ↔ (⟨89, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0090 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨90, by decide⟩ : Fin 144) ↔ (⟨90, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0091 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨91, by decide⟩ : Fin 144) ↔ (⟨91, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0092 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨92, by decide⟩ : Fin 144) ↔ (⟨92, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0093 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨93, by decide⟩ : Fin 144) ↔ (⟨93, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0094 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨94, by decide⟩ : Fin 144) ↔ (⟨94, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0095 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨95, by decide⟩ : Fin 144) ↔ (⟨95, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0096 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨96, by decide⟩ : Fin 144) ↔ (⟨96, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0097 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨97, by decide⟩ : Fin 144) ↔ (⟨97, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0098 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨98, by decide⟩ : Fin 144) ↔ (⟨98, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0099 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨99, by decide⟩ : Fin 144) ↔ (⟨99, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0100 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨100, by decide⟩ : Fin 144) ↔ (⟨100, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0101 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨101, by decide⟩ : Fin 144) ↔ (⟨101, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0102 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨102, by decide⟩ : Fin 144) ↔ (⟨102, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0103 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨103, by decide⟩ : Fin 144) ↔ (⟨103, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0104 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨104, by decide⟩ : Fin 144) ↔ (⟨104, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0105 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨105, by decide⟩ : Fin 144) ↔ (⟨105, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0106 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨106, by decide⟩ : Fin 144) ↔ (⟨106, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0107 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨107, by decide⟩ : Fin 144) ↔ (⟨107, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0108 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨108, by decide⟩ : Fin 144) ↔ (⟨108, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0109 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨109, by decide⟩ : Fin 144) ↔ (⟨109, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0110 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨110, by decide⟩ : Fin 144) ↔ (⟨110, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0111 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨111, by decide⟩ : Fin 144) ↔ (⟨111, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0112 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨112, by decide⟩ : Fin 144) ↔ (⟨112, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0113 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨113, by decide⟩ : Fin 144) ↔ (⟨113, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0114 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨114, by decide⟩ : Fin 144) ↔ (⟨114, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0115 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨115, by decide⟩ : Fin 144) ↔ (⟨115, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0116 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨116, by decide⟩ : Fin 144) ↔ (⟨116, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0117 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨117, by decide⟩ : Fin 144) ↔ (⟨117, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0118 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨118, by decide⟩ : Fin 144) ↔ (⟨118, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0119 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨119, by decide⟩ : Fin 144) ↔ (⟨119, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0120 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨120, by decide⟩ : Fin 144) ↔ (⟨120, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0121 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨121, by decide⟩ : Fin 144) ↔ (⟨121, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0122 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨122, by decide⟩ : Fin 144) ↔ (⟨122, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0123 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨123, by decide⟩ : Fin 144) ↔ (⟨123, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0124 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨124, by decide⟩ : Fin 144) ↔ (⟨124, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0125 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨125, by decide⟩ : Fin 144) ↔ (⟨125, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0126 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨126, by decide⟩ : Fin 144) ↔ (⟨126, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0127 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨127, by decide⟩ : Fin 144) ↔ (⟨127, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0128 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨128, by decide⟩ : Fin 144) ↔ (⟨128, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0129 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨129, by decide⟩ : Fin 144) ↔ (⟨129, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0130 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨130, by decide⟩ : Fin 144) ↔ (⟨130, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0131 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨131, by decide⟩ : Fin 144) ↔ (⟨131, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0132 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨132, by decide⟩ : Fin 144) ↔ (⟨132, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0133 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨133, by decide⟩ : Fin 144) ↔ (⟨133, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0134 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨134, by decide⟩ : Fin 144) ↔ (⟨134, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0135 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨135, by decide⟩ : Fin 144) ↔ (⟨135, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0136 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨136, by decide⟩ : Fin 144) ↔ (⟨136, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0137 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨137, by decide⟩ : Fin 144) ↔ (⟨137, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0138 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨138, by decide⟩ : Fin 144) ↔ (⟨138, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0139 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨139, by decide⟩ : Fin 144) ↔ (⟨139, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0140 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨140, by decide⟩ : Fin 144) ↔ (⟨140, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0141 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨141, by decide⟩ : Fin 144) ↔ (⟨141, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0142 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨142, by decide⟩ : Fin 144) ↔ (⟨142, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transpose0143 : ∀ f : Fin 130,
    f ∈ cubeIncidentFacets (⟨143, by decide⟩ : Fin 144) ↔ (⟨143, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

private theorem transposeGroup0000 (i : Fin 144)
    (hlo : 0 ≤ i.val) (hhi : i.val < 32) :
    ∀ f : Fin 130, f ∈ cubeIncidentFacets i ↔ i ∈ facetLabels f := by
  have hi_bound := i.isLt
  by_cases h16 : i.val < 16
  ·
    by_cases h8 : i.val < 8
    ·
      by_cases h4 : i.val < 4
      ·
        by_cases h2 : i.val < 2
        ·
          by_cases h1 : i.val < 1
          ·
            have he : (⟨0, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 0 = i.val
              omega
            simpa only [he] using transpose0000
          ·
            have he : (⟨1, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 1 = i.val
              omega
            simpa only [he] using transpose0001
        ·
          by_cases h3 : i.val < 3
          ·
            have he : (⟨2, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 2 = i.val
              omega
            simpa only [he] using transpose0002
          ·
            have he : (⟨3, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 3 = i.val
              omega
            simpa only [he] using transpose0003
      ·
        by_cases h6 : i.val < 6
        ·
          by_cases h5 : i.val < 5
          ·
            have he : (⟨4, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 4 = i.val
              omega
            simpa only [he] using transpose0004
          ·
            have he : (⟨5, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 5 = i.val
              omega
            simpa only [he] using transpose0005
        ·
          by_cases h7 : i.val < 7
          ·
            have he : (⟨6, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 6 = i.val
              omega
            simpa only [he] using transpose0006
          ·
            have he : (⟨7, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 7 = i.val
              omega
            simpa only [he] using transpose0007
    ·
      by_cases h12 : i.val < 12
      ·
        by_cases h10 : i.val < 10
        ·
          by_cases h9 : i.val < 9
          ·
            have he : (⟨8, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 8 = i.val
              omega
            simpa only [he] using transpose0008
          ·
            have he : (⟨9, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 9 = i.val
              omega
            simpa only [he] using transpose0009
        ·
          by_cases h11 : i.val < 11
          ·
            have he : (⟨10, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 10 = i.val
              omega
            simpa only [he] using transpose0010
          ·
            have he : (⟨11, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 11 = i.val
              omega
            simpa only [he] using transpose0011
      ·
        by_cases h14 : i.val < 14
        ·
          by_cases h13 : i.val < 13
          ·
            have he : (⟨12, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 12 = i.val
              omega
            simpa only [he] using transpose0012
          ·
            have he : (⟨13, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 13 = i.val
              omega
            simpa only [he] using transpose0013
        ·
          by_cases h15 : i.val < 15
          ·
            have he : (⟨14, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 14 = i.val
              omega
            simpa only [he] using transpose0014
          ·
            have he : (⟨15, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 15 = i.val
              omega
            simpa only [he] using transpose0015
  ·
    by_cases h24 : i.val < 24
    ·
      by_cases h20 : i.val < 20
      ·
        by_cases h18 : i.val < 18
        ·
          by_cases h17 : i.val < 17
          ·
            have he : (⟨16, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 16 = i.val
              omega
            simpa only [he] using transpose0016
          ·
            have he : (⟨17, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 17 = i.val
              omega
            simpa only [he] using transpose0017
        ·
          by_cases h19 : i.val < 19
          ·
            have he : (⟨18, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 18 = i.val
              omega
            simpa only [he] using transpose0018
          ·
            have he : (⟨19, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 19 = i.val
              omega
            simpa only [he] using transpose0019
      ·
        by_cases h22 : i.val < 22
        ·
          by_cases h21 : i.val < 21
          ·
            have he : (⟨20, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 20 = i.val
              omega
            simpa only [he] using transpose0020
          ·
            have he : (⟨21, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 21 = i.val
              omega
            simpa only [he] using transpose0021
        ·
          by_cases h23 : i.val < 23
          ·
            have he : (⟨22, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 22 = i.val
              omega
            simpa only [he] using transpose0022
          ·
            have he : (⟨23, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 23 = i.val
              omega
            simpa only [he] using transpose0023
    ·
      by_cases h28 : i.val < 28
      ·
        by_cases h26 : i.val < 26
        ·
          by_cases h25 : i.val < 25
          ·
            have he : (⟨24, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 24 = i.val
              omega
            simpa only [he] using transpose0024
          ·
            have he : (⟨25, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 25 = i.val
              omega
            simpa only [he] using transpose0025
        ·
          by_cases h27 : i.val < 27
          ·
            have he : (⟨26, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 26 = i.val
              omega
            simpa only [he] using transpose0026
          ·
            have he : (⟨27, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 27 = i.val
              omega
            simpa only [he] using transpose0027
      ·
        by_cases h30 : i.val < 30
        ·
          by_cases h29 : i.val < 29
          ·
            have he : (⟨28, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 28 = i.val
              omega
            simpa only [he] using transpose0028
          ·
            have he : (⟨29, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 29 = i.val
              omega
            simpa only [he] using transpose0029
        ·
          by_cases h31 : i.val < 31
          ·
            have he : (⟨30, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 30 = i.val
              omega
            simpa only [he] using transpose0030
          ·
            have he : (⟨31, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 31 = i.val
              omega
            simpa only [he] using transpose0031

private theorem transposeGroup0001 (i : Fin 144)
    (hlo : 32 ≤ i.val) (hhi : i.val < 64) :
    ∀ f : Fin 130, f ∈ cubeIncidentFacets i ↔ i ∈ facetLabels f := by
  have hi_bound := i.isLt
  by_cases h48 : i.val < 48
  ·
    by_cases h40 : i.val < 40
    ·
      by_cases h36 : i.val < 36
      ·
        by_cases h34 : i.val < 34
        ·
          by_cases h33 : i.val < 33
          ·
            have he : (⟨32, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 32 = i.val
              omega
            simpa only [he] using transpose0032
          ·
            have he : (⟨33, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 33 = i.val
              omega
            simpa only [he] using transpose0033
        ·
          by_cases h35 : i.val < 35
          ·
            have he : (⟨34, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 34 = i.val
              omega
            simpa only [he] using transpose0034
          ·
            have he : (⟨35, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 35 = i.val
              omega
            simpa only [he] using transpose0035
      ·
        by_cases h38 : i.val < 38
        ·
          by_cases h37 : i.val < 37
          ·
            have he : (⟨36, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 36 = i.val
              omega
            simpa only [he] using transpose0036
          ·
            have he : (⟨37, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 37 = i.val
              omega
            simpa only [he] using transpose0037
        ·
          by_cases h39 : i.val < 39
          ·
            have he : (⟨38, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 38 = i.val
              omega
            simpa only [he] using transpose0038
          ·
            have he : (⟨39, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 39 = i.val
              omega
            simpa only [he] using transpose0039
    ·
      by_cases h44 : i.val < 44
      ·
        by_cases h42 : i.val < 42
        ·
          by_cases h41 : i.val < 41
          ·
            have he : (⟨40, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 40 = i.val
              omega
            simpa only [he] using transpose0040
          ·
            have he : (⟨41, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 41 = i.val
              omega
            simpa only [he] using transpose0041
        ·
          by_cases h43 : i.val < 43
          ·
            have he : (⟨42, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 42 = i.val
              omega
            simpa only [he] using transpose0042
          ·
            have he : (⟨43, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 43 = i.val
              omega
            simpa only [he] using transpose0043
      ·
        by_cases h46 : i.val < 46
        ·
          by_cases h45 : i.val < 45
          ·
            have he : (⟨44, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 44 = i.val
              omega
            simpa only [he] using transpose0044
          ·
            have he : (⟨45, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 45 = i.val
              omega
            simpa only [he] using transpose0045
        ·
          by_cases h47 : i.val < 47
          ·
            have he : (⟨46, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 46 = i.val
              omega
            simpa only [he] using transpose0046
          ·
            have he : (⟨47, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 47 = i.val
              omega
            simpa only [he] using transpose0047
  ·
    by_cases h56 : i.val < 56
    ·
      by_cases h52 : i.val < 52
      ·
        by_cases h50 : i.val < 50
        ·
          by_cases h49 : i.val < 49
          ·
            have he : (⟨48, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 48 = i.val
              omega
            simpa only [he] using transpose0048
          ·
            have he : (⟨49, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 49 = i.val
              omega
            simpa only [he] using transpose0049
        ·
          by_cases h51 : i.val < 51
          ·
            have he : (⟨50, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 50 = i.val
              omega
            simpa only [he] using transpose0050
          ·
            have he : (⟨51, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 51 = i.val
              omega
            simpa only [he] using transpose0051
      ·
        by_cases h54 : i.val < 54
        ·
          by_cases h53 : i.val < 53
          ·
            have he : (⟨52, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 52 = i.val
              omega
            simpa only [he] using transpose0052
          ·
            have he : (⟨53, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 53 = i.val
              omega
            simpa only [he] using transpose0053
        ·
          by_cases h55 : i.val < 55
          ·
            have he : (⟨54, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 54 = i.val
              omega
            simpa only [he] using transpose0054
          ·
            have he : (⟨55, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 55 = i.val
              omega
            simpa only [he] using transpose0055
    ·
      by_cases h60 : i.val < 60
      ·
        by_cases h58 : i.val < 58
        ·
          by_cases h57 : i.val < 57
          ·
            have he : (⟨56, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 56 = i.val
              omega
            simpa only [he] using transpose0056
          ·
            have he : (⟨57, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 57 = i.val
              omega
            simpa only [he] using transpose0057
        ·
          by_cases h59 : i.val < 59
          ·
            have he : (⟨58, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 58 = i.val
              omega
            simpa only [he] using transpose0058
          ·
            have he : (⟨59, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 59 = i.val
              omega
            simpa only [he] using transpose0059
      ·
        by_cases h62 : i.val < 62
        ·
          by_cases h61 : i.val < 61
          ·
            have he : (⟨60, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 60 = i.val
              omega
            simpa only [he] using transpose0060
          ·
            have he : (⟨61, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 61 = i.val
              omega
            simpa only [he] using transpose0061
        ·
          by_cases h63 : i.val < 63
          ·
            have he : (⟨62, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 62 = i.val
              omega
            simpa only [he] using transpose0062
          ·
            have he : (⟨63, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 63 = i.val
              omega
            simpa only [he] using transpose0063

private theorem transposeGroup0002 (i : Fin 144)
    (hlo : 64 ≤ i.val) (hhi : i.val < 96) :
    ∀ f : Fin 130, f ∈ cubeIncidentFacets i ↔ i ∈ facetLabels f := by
  have hi_bound := i.isLt
  by_cases h80 : i.val < 80
  ·
    by_cases h72 : i.val < 72
    ·
      by_cases h68 : i.val < 68
      ·
        by_cases h66 : i.val < 66
        ·
          by_cases h65 : i.val < 65
          ·
            have he : (⟨64, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 64 = i.val
              omega
            simpa only [he] using transpose0064
          ·
            have he : (⟨65, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 65 = i.val
              omega
            simpa only [he] using transpose0065
        ·
          by_cases h67 : i.val < 67
          ·
            have he : (⟨66, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 66 = i.val
              omega
            simpa only [he] using transpose0066
          ·
            have he : (⟨67, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 67 = i.val
              omega
            simpa only [he] using transpose0067
      ·
        by_cases h70 : i.val < 70
        ·
          by_cases h69 : i.val < 69
          ·
            have he : (⟨68, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 68 = i.val
              omega
            simpa only [he] using transpose0068
          ·
            have he : (⟨69, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 69 = i.val
              omega
            simpa only [he] using transpose0069
        ·
          by_cases h71 : i.val < 71
          ·
            have he : (⟨70, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 70 = i.val
              omega
            simpa only [he] using transpose0070
          ·
            have he : (⟨71, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 71 = i.val
              omega
            simpa only [he] using transpose0071
    ·
      by_cases h76 : i.val < 76
      ·
        by_cases h74 : i.val < 74
        ·
          by_cases h73 : i.val < 73
          ·
            have he : (⟨72, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 72 = i.val
              omega
            simpa only [he] using transpose0072
          ·
            have he : (⟨73, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 73 = i.val
              omega
            simpa only [he] using transpose0073
        ·
          by_cases h75 : i.val < 75
          ·
            have he : (⟨74, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 74 = i.val
              omega
            simpa only [he] using transpose0074
          ·
            have he : (⟨75, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 75 = i.val
              omega
            simpa only [he] using transpose0075
      ·
        by_cases h78 : i.val < 78
        ·
          by_cases h77 : i.val < 77
          ·
            have he : (⟨76, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 76 = i.val
              omega
            simpa only [he] using transpose0076
          ·
            have he : (⟨77, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 77 = i.val
              omega
            simpa only [he] using transpose0077
        ·
          by_cases h79 : i.val < 79
          ·
            have he : (⟨78, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 78 = i.val
              omega
            simpa only [he] using transpose0078
          ·
            have he : (⟨79, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 79 = i.val
              omega
            simpa only [he] using transpose0079
  ·
    by_cases h88 : i.val < 88
    ·
      by_cases h84 : i.val < 84
      ·
        by_cases h82 : i.val < 82
        ·
          by_cases h81 : i.val < 81
          ·
            have he : (⟨80, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 80 = i.val
              omega
            simpa only [he] using transpose0080
          ·
            have he : (⟨81, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 81 = i.val
              omega
            simpa only [he] using transpose0081
        ·
          by_cases h83 : i.val < 83
          ·
            have he : (⟨82, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 82 = i.val
              omega
            simpa only [he] using transpose0082
          ·
            have he : (⟨83, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 83 = i.val
              omega
            simpa only [he] using transpose0083
      ·
        by_cases h86 : i.val < 86
        ·
          by_cases h85 : i.val < 85
          ·
            have he : (⟨84, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 84 = i.val
              omega
            simpa only [he] using transpose0084
          ·
            have he : (⟨85, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 85 = i.val
              omega
            simpa only [he] using transpose0085
        ·
          by_cases h87 : i.val < 87
          ·
            have he : (⟨86, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 86 = i.val
              omega
            simpa only [he] using transpose0086
          ·
            have he : (⟨87, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 87 = i.val
              omega
            simpa only [he] using transpose0087
    ·
      by_cases h92 : i.val < 92
      ·
        by_cases h90 : i.val < 90
        ·
          by_cases h89 : i.val < 89
          ·
            have he : (⟨88, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 88 = i.val
              omega
            simpa only [he] using transpose0088
          ·
            have he : (⟨89, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 89 = i.val
              omega
            simpa only [he] using transpose0089
        ·
          by_cases h91 : i.val < 91
          ·
            have he : (⟨90, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 90 = i.val
              omega
            simpa only [he] using transpose0090
          ·
            have he : (⟨91, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 91 = i.val
              omega
            simpa only [he] using transpose0091
      ·
        by_cases h94 : i.val < 94
        ·
          by_cases h93 : i.val < 93
          ·
            have he : (⟨92, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 92 = i.val
              omega
            simpa only [he] using transpose0092
          ·
            have he : (⟨93, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 93 = i.val
              omega
            simpa only [he] using transpose0093
        ·
          by_cases h95 : i.val < 95
          ·
            have he : (⟨94, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 94 = i.val
              omega
            simpa only [he] using transpose0094
          ·
            have he : (⟨95, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 95 = i.val
              omega
            simpa only [he] using transpose0095

private theorem transposeGroup0003 (i : Fin 144)
    (hlo : 96 ≤ i.val) (hhi : i.val < 128) :
    ∀ f : Fin 130, f ∈ cubeIncidentFacets i ↔ i ∈ facetLabels f := by
  have hi_bound := i.isLt
  by_cases h112 : i.val < 112
  ·
    by_cases h104 : i.val < 104
    ·
      by_cases h100 : i.val < 100
      ·
        by_cases h98 : i.val < 98
        ·
          by_cases h97 : i.val < 97
          ·
            have he : (⟨96, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 96 = i.val
              omega
            simpa only [he] using transpose0096
          ·
            have he : (⟨97, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 97 = i.val
              omega
            simpa only [he] using transpose0097
        ·
          by_cases h99 : i.val < 99
          ·
            have he : (⟨98, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 98 = i.val
              omega
            simpa only [he] using transpose0098
          ·
            have he : (⟨99, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 99 = i.val
              omega
            simpa only [he] using transpose0099
      ·
        by_cases h102 : i.val < 102
        ·
          by_cases h101 : i.val < 101
          ·
            have he : (⟨100, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 100 = i.val
              omega
            simpa only [he] using transpose0100
          ·
            have he : (⟨101, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 101 = i.val
              omega
            simpa only [he] using transpose0101
        ·
          by_cases h103 : i.val < 103
          ·
            have he : (⟨102, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 102 = i.val
              omega
            simpa only [he] using transpose0102
          ·
            have he : (⟨103, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 103 = i.val
              omega
            simpa only [he] using transpose0103
    ·
      by_cases h108 : i.val < 108
      ·
        by_cases h106 : i.val < 106
        ·
          by_cases h105 : i.val < 105
          ·
            have he : (⟨104, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 104 = i.val
              omega
            simpa only [he] using transpose0104
          ·
            have he : (⟨105, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 105 = i.val
              omega
            simpa only [he] using transpose0105
        ·
          by_cases h107 : i.val < 107
          ·
            have he : (⟨106, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 106 = i.val
              omega
            simpa only [he] using transpose0106
          ·
            have he : (⟨107, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 107 = i.val
              omega
            simpa only [he] using transpose0107
      ·
        by_cases h110 : i.val < 110
        ·
          by_cases h109 : i.val < 109
          ·
            have he : (⟨108, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 108 = i.val
              omega
            simpa only [he] using transpose0108
          ·
            have he : (⟨109, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 109 = i.val
              omega
            simpa only [he] using transpose0109
        ·
          by_cases h111 : i.val < 111
          ·
            have he : (⟨110, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 110 = i.val
              omega
            simpa only [he] using transpose0110
          ·
            have he : (⟨111, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 111 = i.val
              omega
            simpa only [he] using transpose0111
  ·
    by_cases h120 : i.val < 120
    ·
      by_cases h116 : i.val < 116
      ·
        by_cases h114 : i.val < 114
        ·
          by_cases h113 : i.val < 113
          ·
            have he : (⟨112, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 112 = i.val
              omega
            simpa only [he] using transpose0112
          ·
            have he : (⟨113, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 113 = i.val
              omega
            simpa only [he] using transpose0113
        ·
          by_cases h115 : i.val < 115
          ·
            have he : (⟨114, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 114 = i.val
              omega
            simpa only [he] using transpose0114
          ·
            have he : (⟨115, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 115 = i.val
              omega
            simpa only [he] using transpose0115
      ·
        by_cases h118 : i.val < 118
        ·
          by_cases h117 : i.val < 117
          ·
            have he : (⟨116, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 116 = i.val
              omega
            simpa only [he] using transpose0116
          ·
            have he : (⟨117, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 117 = i.val
              omega
            simpa only [he] using transpose0117
        ·
          by_cases h119 : i.val < 119
          ·
            have he : (⟨118, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 118 = i.val
              omega
            simpa only [he] using transpose0118
          ·
            have he : (⟨119, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 119 = i.val
              omega
            simpa only [he] using transpose0119
    ·
      by_cases h124 : i.val < 124
      ·
        by_cases h122 : i.val < 122
        ·
          by_cases h121 : i.val < 121
          ·
            have he : (⟨120, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 120 = i.val
              omega
            simpa only [he] using transpose0120
          ·
            have he : (⟨121, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 121 = i.val
              omega
            simpa only [he] using transpose0121
        ·
          by_cases h123 : i.val < 123
          ·
            have he : (⟨122, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 122 = i.val
              omega
            simpa only [he] using transpose0122
          ·
            have he : (⟨123, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 123 = i.val
              omega
            simpa only [he] using transpose0123
      ·
        by_cases h126 : i.val < 126
        ·
          by_cases h125 : i.val < 125
          ·
            have he : (⟨124, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 124 = i.val
              omega
            simpa only [he] using transpose0124
          ·
            have he : (⟨125, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 125 = i.val
              omega
            simpa only [he] using transpose0125
        ·
          by_cases h127 : i.val < 127
          ·
            have he : (⟨126, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 126 = i.val
              omega
            simpa only [he] using transpose0126
          ·
            have he : (⟨127, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 127 = i.val
              omega
            simpa only [he] using transpose0127

private theorem transposeGroup0004 (i : Fin 144)
    (hlo : 128 ≤ i.val) (hhi : i.val < 144) :
    ∀ f : Fin 130, f ∈ cubeIncidentFacets i ↔ i ∈ facetLabels f := by
  have hi_bound := i.isLt
  by_cases h136 : i.val < 136
  ·
    by_cases h132 : i.val < 132
    ·
      by_cases h130 : i.val < 130
      ·
        by_cases h129 : i.val < 129
        ·
          have he : (⟨128, by decide⟩ : Fin 144) = i := by
            apply Fin.ext
            change 128 = i.val
            omega
          simpa only [he] using transpose0128
        ·
          have he : (⟨129, by decide⟩ : Fin 144) = i := by
            apply Fin.ext
            change 129 = i.val
            omega
          simpa only [he] using transpose0129
      ·
        by_cases h131 : i.val < 131
        ·
          have he : (⟨130, by decide⟩ : Fin 144) = i := by
            apply Fin.ext
            change 130 = i.val
            omega
          simpa only [he] using transpose0130
        ·
          have he : (⟨131, by decide⟩ : Fin 144) = i := by
            apply Fin.ext
            change 131 = i.val
            omega
          simpa only [he] using transpose0131
    ·
      by_cases h134 : i.val < 134
      ·
        by_cases h133 : i.val < 133
        ·
          have he : (⟨132, by decide⟩ : Fin 144) = i := by
            apply Fin.ext
            change 132 = i.val
            omega
          simpa only [he] using transpose0132
        ·
          have he : (⟨133, by decide⟩ : Fin 144) = i := by
            apply Fin.ext
            change 133 = i.val
            omega
          simpa only [he] using transpose0133
      ·
        by_cases h135 : i.val < 135
        ·
          have he : (⟨134, by decide⟩ : Fin 144) = i := by
            apply Fin.ext
            change 134 = i.val
            omega
          simpa only [he] using transpose0134
        ·
          have he : (⟨135, by decide⟩ : Fin 144) = i := by
            apply Fin.ext
            change 135 = i.val
            omega
          simpa only [he] using transpose0135
  ·
    by_cases h140 : i.val < 140
    ·
      by_cases h138 : i.val < 138
      ·
        by_cases h137 : i.val < 137
        ·
          have he : (⟨136, by decide⟩ : Fin 144) = i := by
            apply Fin.ext
            change 136 = i.val
            omega
          simpa only [he] using transpose0136
        ·
          have he : (⟨137, by decide⟩ : Fin 144) = i := by
            apply Fin.ext
            change 137 = i.val
            omega
          simpa only [he] using transpose0137
      ·
        by_cases h139 : i.val < 139
        ·
          have he : (⟨138, by decide⟩ : Fin 144) = i := by
            apply Fin.ext
            change 138 = i.val
            omega
          simpa only [he] using transpose0138
        ·
          have he : (⟨139, by decide⟩ : Fin 144) = i := by
            apply Fin.ext
            change 139 = i.val
            omega
          simpa only [he] using transpose0139
    ·
      by_cases h142 : i.val < 142
      ·
        by_cases h141 : i.val < 141
        ·
          have he : (⟨140, by decide⟩ : Fin 144) = i := by
            apply Fin.ext
            change 140 = i.val
            omega
          simpa only [he] using transpose0140
        ·
          have he : (⟨141, by decide⟩ : Fin 144) = i := by
            apply Fin.ext
            change 141 = i.val
            omega
          simpa only [he] using transpose0141
      ·
        by_cases h143 : i.val < 143
        ·
          have he : (⟨142, by decide⟩ : Fin 144) = i := by
            apply Fin.ext
            change 142 = i.val
            omega
          simpa only [he] using transpose0142
        ·
          have he : (⟨143, by decide⟩ : Fin 144) = i := by
            apply Fin.ext
            change 143 = i.val
            omega
          simpa only [he] using transpose0143

private theorem cubeIncidentFacets_iff : ∀ (v : Fin 144) (f : Fin 130),
    f ∈ cubeIncidentFacets v ↔ v ∈ facetLabels f := by
  intro i
  have hi_bound := i.isLt
  by_cases h64 : i.val < 64
  ·
    by_cases h32 : i.val < 32
    ·
      exact transposeGroup0000 i (by omega) (by omega)
    ·
      exact transposeGroup0001 i (by omega) (by omega)
  ·
    by_cases h96 : i.val < 96
    ·
      exact transposeGroup0002 i (by omega) (by omega)
    ·
      by_cases h128 : i.val < 128
      ·
        exact transposeGroup0003 i (by omega) (by omega)
      ·
        exact transposeGroup0004 i (by omega) (by omega)

private def cubeCofacets (i : Fin 1069) : Finset (Fin 130) :=
  (cubeIncidentFacets (faceAnchor i)).filter
    (fun f => faceMask i ⊆ facetLabels f)

private theorem cubeCofacets_iff (i : Fin 1069) (f : Fin 130) :
    f ∈ cubeCofacets i ↔ faceMask i ⊆ facetLabels f := by
  constructor
  · intro hf
    exact (Finset.mem_filter.mp hf).2
  · intro h
    apply Finset.mem_filter.mpr
    exact ⟨(cubeIncidentFacets_iff (faceAnchor i) f).mpr
      (h (faceAnchor_mem i)), h⟩

private def cubeCofacetCodeTable : ℕ → Fin 130 → Fin 27 :=
fun index =>
    if index < 534 then
      if index < 267 then
        if index < 133 then
          if index < 66 then
            if index < 33 then
              if index < 16 then
                if index < 8 then
                  if index < 4 then
                    if index < 2 then
                      if index < 1 then
                        fun f => if f.val = 2 then 13 else if f.val = 11 then 13 else if f.val = 15 then 13 else if f.val = 16 then 13 else if f.val = 18 then 13 else if f.val = 20 then 13 else 0
                      else
                        fun f => if f.val = 1 then 13 else if f.val = 2 then 14 else if f.val = 14 then 13 else if f.val = 15 then 14 else if f.val = 16 then 14 else if f.val = 66 then 13 else if f.val = 67 then 13 else if f.val = 79 then 13 else if f.val = 80 then 13 else if f.val = 81 then 13 else 0
                    else
                      if index < 3 then
                        fun f => if f.val = 0 then 13 else if f.val = 3 then 13 else if f.val = 11 then 14 else if f.val = 12 then 13 else if f.val = 18 then 14 else if f.val = 20 then 14 else 0
                      else
                        fun f => if f.val = 0 then 14 else if f.val = 1 then 14 else if f.val = 3 then 14 else if f.val = 12 then 14 else if f.val = 14 then 14 else if f.val = 66 then 14 else if f.val = 67 then 14 else if f.val = 69 then 13 else if f.val = 70 then 13 else if f.val = 80 then 14 else 0
                  else
                    if index < 6 then
                      if index < 5 then
                        fun f => if f.val = 15 then 16 else if f.val = 16 then 16 else if f.val = 17 then 13 else if f.val = 18 then 16 else if f.val = 19 then 13 else if f.val = 20 then 16 else 0
                      else
                        fun f => if f.val = 13 then 13 else if f.val = 14 then 16 else if f.val = 15 then 17 else if f.val = 16 then 17 else if f.val = 17 then 14 else if f.val = 65 then 13 else if f.val = 66 then 16 else if f.val = 68 then 13 else if f.val = 77 then 13 else if f.val = 79 then 14 else 0
                    else
                      if index < 7 then
                        fun f => if f.val = 0 then 16 else if f.val = 3 then 16 else if f.val = 6 then 13 else if f.val = 18 then 17 else if f.val = 19 then 14 else if f.val = 20 then 17 else 0
                      else
                        fun f => if f.val = 0 then 17 else if f.val = 3 then 17 else if f.val = 6 then 14 else if f.val = 13 then 14 else if f.val = 14 then 17 else if f.val = 66 then 17 else if f.val = 68 then 14 else if f.val = 70 then 14 else if f.val = 74 then 13 else if f.val = 77 then 14 else 0
                else
                  if index < 12 then
                    if index < 10 then
                      if index < 9 then
                        fun f => if f.val = 2 then 16 else if f.val = 4 then 13 else if f.val = 11 then 16 else if f.val = 15 then 22 else if f.val = 20 then 22 else if f.val = 22 then 13 else if f.val = 23 then 13 else if f.val = 25 then 13 else if f.val = 26 then 13 else if f.val = 31 then 13 else 0
                      else
                        fun f => if f.val = 1 then 16 else if f.val = 2 then 17 else if f.val = 4 then 14 else if f.val = 5 then 13 else if f.val = 15 then 23 else if f.val = 78 then 13 else if f.val = 79 then 16 else if f.val = 80 then 16 else if f.val = 81 then 14 else if f.val = 82 then 13 else 0
                    else
                      if index < 11 then
                        fun f => if f.val = 3 then 22 else if f.val = 9 then 13 else if f.val = 11 then 17 else if f.val = 12 then 16 else if f.val = 20 then 23 else if f.val = 22 then 14 else if f.val = 26 then 14 else if f.val = 30 then 13 else if f.val = 31 then 14 else if f.val = 33 then 13 else 0
                      else
                        fun f => if f.val = 1 then 17 else if f.val = 3 then 23 else if f.val = 5 then 14 else if f.val = 9 then 14 else if f.val = 12 then 17 else if f.val = 69 then 14 else if f.val = 70 then 16 else if f.val = 78 then 14 else if f.val = 80 then 17 else if f.val = 82 then 14 else 0
                  else
                    if index < 14 then
                      if index < 13 then
                        fun f => if f.val = 4 then 16 else if f.val = 15 then 25 else if f.val = 17 then 16 else if f.val = 19 then 16 else if f.val = 20 then 25 else if f.val = 25 then 14 else if f.val = 26 then 16 else if f.val = 28 then 13 else if f.val = 35 then 13 else if f.val = 39 then 13 else 0
                      else
                        fun f => if f.val = 4 then 17 else if f.val = 5 then 16 else if f.val = 13 then 16 else if f.val = 15 then 26 else if f.val = 17 then 17 else if f.val = 65 then 14 else if f.val = 68 then 16 else if f.val = 71 then 13 else if f.val = 78 then 16 else if f.val = 79 then 17 else 0
                    else
                      if index < 15 then
                        fun f => if f.val = 3 then 25 else if f.val = 6 then 16 else if f.val = 9 then 16 else if f.val = 19 then 17 else if f.val = 20 then 26 else if f.val = 26 then 17 else if f.val = 27 then 13 else if f.val = 28 then 14 else if f.val = 30 then 14 else if f.val = 35 then 14 else 0
                      else
                        fun f => if f.val = 3 then 26 else if f.val = 5 then 17 else if f.val = 6 then 17 else if f.val = 9 then 17 else if f.val = 13 then 17 else if f.val = 68 then 17 else if f.val = 70 then 17 else if f.val = 71 then 14 else if f.val = 74 then 14 else if f.val = 78 then 17 else 0
              else
                if index < 24 then
                  if index < 20 then
                    if index < 18 then
                      if index < 17 then
                        fun f => if f.val = 2 then 22 else if f.val = 8 then 13 else if f.val = 10 then 13 else if f.val = 11 then 22 else if f.val = 16 then 22 else if f.val = 18 then 22 else 0
                      else
                        fun f => if f.val = 1 then 22 else if f.val = 2 then 23 else if f.val = 8 then 14 else if f.val = 10 then 14 else if f.val = 14 then 22 else if f.val = 16 then 23 else 0
                    else
                      if index < 19 then
                        fun f => if f.val = 0 then 22 else if f.val = 8 then 16 else if f.val = 10 then 16 else if f.val = 11 then 23 else if f.val = 12 then 22 else if f.val = 18 then 23 else 0
                      else
                        fun f => if f.val = 0 then 23 else if f.val = 1 then 23 else if f.val = 8 then 17 else if f.val = 10 then 17 else if f.val = 12 then 23 else if f.val = 14 then 23 else 0
                  else
                    if index < 22 then
                      if index < 21 then
                        fun f => if f.val = 7 then 13 else if f.val = 8 then 22 else if f.val = 16 then 25 else if f.val = 17 then 22 else if f.val = 18 then 25 else if f.val = 19 then 22 else 0
                      else
                        fun f => if f.val = 7 then 14 else if f.val = 8 then 23 else if f.val = 13 then 22 else if f.val = 14 then 25 else if f.val = 16 then 26 else if f.val = 17 then 23 else 0
                    else
                      if index < 23 then
                        fun f => if f.val = 0 then 25 else if f.val = 6 then 22 else if f.val = 7 then 16 else if f.val = 8 then 25 else if f.val = 18 then 26 else if f.val = 19 then 23 else 0
                      else
                        fun f => if f.val = 0 then 26 else if f.val = 6 then 23 else if f.val = 7 then 17 else if f.val = 8 then 26 else if f.val = 13 then 23 else if f.val = 14 then 26 else 0
                else
                  if index < 28 then
                    if index < 26 then
                      if index < 25 then
                        fun f => if f.val = 2 then 25 else if f.val = 4 then 22 else if f.val = 10 then 22 else if f.val = 11 then 25 else if f.val = 23 then 14 else if f.val = 25 then 16 else if f.val = 31 then 16 else if f.val = 32 then 13 else if f.val = 45 then 13 else if f.val = 47 then 13 else if f.val = 53 then 13 else if f.val = 54 then 13 else 0
                      else
                        fun f => if f.val = 1 then 25 else if f.val = 2 then 26 else if f.val = 4 then 23 else if f.val = 5 then 22 else if f.val = 10 then 23 else if f.val = 45 then 14 else if f.val = 47 then 14 else if f.val = 54 then 14 else if f.val = 59 then 13 else if f.val = 64 then 13 else 0
                    else
                      if index < 27 then
                        fun f => if f.val = 9 then 22 else if f.val = 10 then 25 else if f.val = 11 then 26 else if f.val = 12 then 25 else if f.val = 30 then 16 else if f.val = 31 then 17 else if f.val = 32 then 14 else if f.val = 33 then 14 else if f.val = 52 then 13 else if f.val = 53 then 14 else if f.val = 54 then 16 else if f.val = 55 then 13 else 0
                      else
                        fun f => if f.val = 1 then 26 else if f.val = 5 then 23 else if f.val = 9 then 23 else if f.val = 10 then 26 else if f.val = 12 then 26 else if f.val = 46 then 13 else if f.val = 52 then 14 else if f.val = 54 then 17 else if f.val = 55 then 14 else if f.val = 64 then 14 else 0
                  else
                    if index < 30 then
                      if index < 29 then
                        fun f => if f.val = 4 then 25 else if f.val = 7 then 22 else if f.val = 17 then 25 else if f.val = 19 then 25 else if f.val = 25 then 17 else if f.val = 28 then 16 else if f.val = 39 then 14 else if f.val = 41 then 13 else if f.val = 47 then 16 else if f.val = 50 then 13 else if f.val = 61 then 13 else if f.val = 63 then 13 else 0
                      else
                        fun f => if f.val = 4 then 26 else if f.val = 5 then 25 else if f.val = 7 then 23 else if f.val = 13 then 25 else if f.val = 17 then 26 else if f.val = 47 then 17 else if f.val = 59 then 14 else if f.val = 61 then 14 else if f.val = 63 then 14 else if f.val = 64 then 16 else 0
                    else
                      if index < 31 then
                        fun f => if f.val = 6 then 25 else if f.val = 7 then 25 else if f.val = 9 then 25 else if f.val = 19 then 26 else if f.val = 27 then 14 else if f.val = 28 then 17 else if f.val = 30 then 17 else if f.val = 41 then 14 else if f.val = 49 then 13 else if f.val = 50 then 14 else if f.val = 52 then 16 else if f.val = 63 then 16 else 0
                      else
                        if index < 32 then
                          fun f => if f.val = 5 then 26 else if f.val = 6 then 26 else if f.val = 7 then 26 else if f.val = 9 then 26 else if f.val = 13 then 26 else if f.val = 46 then 14 else if f.val = 49 then 14 else if f.val = 52 then 17 else if f.val = 63 then 17 else if f.val = 64 then 17 else 0
                        else
                          fun f => if f.val = 23 then 26 else if f.val = 32 then 25 else if f.val = 37 then 13 else if f.val = 38 then 13 else if f.val = 40 then 13 else if f.val = 42 then 13 else 0
            else
              if index < 49 then
                if index < 41 then
                  if index < 37 then
                    if index < 35 then
                      if index < 34 then
                        fun f => if f.val = 22 then 25 else if f.val = 23 then 25 else if f.val = 34 then 13 else if f.val = 36 then 13 else if f.val = 37 then 14 else if f.val = 38 then 14 else 0
                      else
                        fun f => if f.val = 21 then 13 else if f.val = 24 then 13 else if f.val = 32 then 26 else if f.val = 33 then 26 else if f.val = 40 then 14 else if f.val = 42 then 14 else 0
                    else
                      if index < 36 then
                        fun f => if f.val = 21 then 14 else if f.val = 22 then 26 else if f.val = 24 then 14 else if f.val = 33 then 25 else if f.val = 34 then 14 else if f.val = 36 then 14 else 0
                      else
                        fun f => if f.val = 37 then 16 else if f.val = 38 then 16 else if f.val = 39 then 26 else if f.val = 40 then 16 else if f.val = 41 then 25 else if f.val = 42 then 16 else 0
                  else
                    if index < 39 then
                      if index < 38 then
                        fun f => if f.val = 34 then 16 else if f.val = 35 then 25 else if f.val = 36 then 16 else if f.val = 37 then 17 else if f.val = 38 then 17 else if f.val = 39 then 25 else 0
                      else
                        fun f => if f.val = 21 then 16 else if f.val = 24 then 16 else if f.val = 27 then 26 else if f.val = 40 then 17 else if f.val = 41 then 26 else if f.val = 42 then 17 else 0
                    else
                      if index < 40 then
                        fun f => if f.val = 21 then 17 else if f.val = 24 then 17 else if f.val = 27 then 25 else if f.val = 34 then 17 else if f.val = 35 then 26 else if f.val = 36 then 17 else 0
                      else
                        fun f => if f.val = 23 then 17 else if f.val = 25 then 25 else if f.val = 32 then 16 else if f.val = 37 then 22 else if f.val = 42 then 22 else if f.val = 44 then 13 else if f.val = 45 then 16 else if f.val = 47 then 22 else if f.val = 48 then 13 else if f.val = 53 then 16 else 0
                else
                  if index < 45 then
                    if index < 43 then
                      if index < 42 then
                        fun f => if f.val = 22 then 16 else if f.val = 23 then 16 else if f.val = 25 then 22 else if f.val = 26 then 22 else if f.val = 34 then 22 else if f.val = 37 then 23 else 0
                      else
                        fun f => if f.val = 24 then 22 else if f.val = 30 then 25 else if f.val = 32 then 17 else if f.val = 33 then 17 else if f.val = 42 then 23 else if f.val = 44 then 14 else if f.val = 48 then 14 else if f.val = 52 then 22 else if f.val = 53 then 17 else if f.val = 55 then 16 else 0
                    else
                      if index < 44 then
                        fun f => if f.val = 22 then 17 else if f.val = 24 then 23 else if f.val = 26 then 23 else if f.val = 30 then 22 else if f.val = 33 then 16 else if f.val = 34 then 23 else 0
                      else
                        fun f => if f.val = 25 then 26 else if f.val = 37 then 25 else if f.val = 39 then 17 else if f.val = 41 then 16 else if f.val = 42 then 25 else if f.val = 47 then 25 else if f.val = 48 then 16 else if f.val = 50 then 16 else if f.val = 57 then 13 else if f.val = 61 then 16 else 0
                  else
                    if index < 47 then
                      if index < 46 then
                        fun f => if f.val = 25 then 23 else if f.val = 26 then 25 else if f.val = 34 then 25 else if f.val = 35 then 16 else if f.val = 37 then 26 else if f.val = 39 then 16 else 0
                      else
                        fun f => if f.val = 24 then 25 else if f.val = 27 then 17 else if f.val = 30 then 26 else if f.val = 41 then 17 else if f.val = 42 then 26 else if f.val = 48 then 17 else if f.val = 49 then 16 else if f.val = 50 then 17 else if f.val = 52 then 25 else if f.val = 57 then 14 else 0
                    else
                      if index < 48 then
                        fun f => if f.val = 24 then 26 else if f.val = 26 then 26 else if f.val = 27 then 16 else if f.val = 30 then 23 else if f.val = 34 then 26 else if f.val = 35 then 17 else 0
                      else
                        fun f => if f.val = 23 then 23 else if f.val = 29 then 13 else if f.val = 31 then 25 else if f.val = 32 then 22 else if f.val = 38 then 22 else if f.val = 40 then 22 else 0
              else
                if index < 57 then
                  if index < 53 then
                    if index < 51 then
                      if index < 50 then
                        fun f => if f.val = 22 then 22 else if f.val = 23 then 22 else if f.val = 29 then 14 else if f.val = 31 then 22 else if f.val = 36 then 22 else if f.val = 38 then 23 else 0
                      else
                        fun f => if f.val = 21 then 22 else if f.val = 29 then 16 else if f.val = 31 then 26 else if f.val = 32 then 23 else if f.val = 33 then 23 else if f.val = 40 then 23 else 0
                    else
                      if index < 52 then
                        fun f => if f.val = 21 then 23 else if f.val = 22 then 23 else if f.val = 29 then 17 else if f.val = 31 then 23 else if f.val = 33 then 22 else if f.val = 36 then 23 else 0
                      else
                        fun f => if f.val = 28 then 25 else if f.val = 29 then 22 else if f.val = 38 then 25 else if f.val = 39 then 23 else if f.val = 40 then 25 else if f.val = 41 then 22 else 0
                  else
                    if index < 55 then
                      if index < 54 then
                        fun f => if f.val = 28 then 22 else if f.val = 29 then 23 else if f.val = 35 then 22 else if f.val = 36 then 25 else if f.val = 38 then 26 else if f.val = 39 then 22 else 0
                      else
                        fun f => if f.val = 21 then 25 else if f.val = 27 then 23 else if f.val = 28 then 26 else if f.val = 29 then 25 else if f.val = 40 then 26 else if f.val = 41 then 23 else 0
                    else
                      if index < 56 then
                        fun f => if f.val = 21 then 26 else if f.val = 27 then 22 else if f.val = 28 then 23 else if f.val = 29 then 26 else if f.val = 35 then 23 else if f.val = 36 then 26 else 0
                      else
                        fun f => if f.val = 45 then 23 else if f.val = 54 then 23 else if f.val = 59 then 16 else if f.val = 60 then 13 else if f.val = 62 then 13 else if f.val = 64 then 22 else 0
                else
                  if index < 61 then
                    if index < 59 then
                      if index < 58 then
                        fun f => if f.val = 44 then 25 else if f.val = 45 then 26 else if f.val = 56 then 13 else if f.val = 58 then 13 else if f.val = 59 then 25 else if f.val = 60 then 14 else 0
                      else
                        fun f => if f.val = 43 then 13 else if f.val = 46 then 16 else if f.val = 54 then 26 else if f.val = 55 then 23 else if f.val = 62 then 14 else if f.val = 64 then 23 else 0
                    else
                      if index < 60 then
                        fun f => if f.val = 43 then 14 else if f.val = 44 then 26 else if f.val = 46 then 25 else if f.val = 55 then 26 else if f.val = 56 then 14 else if f.val = 58 then 14 else 0
                      else
                        fun f => if f.val = 59 then 17 else if f.val = 60 then 16 else if f.val = 61 then 23 else if f.val = 62 then 16 else if f.val = 63 then 23 else if f.val = 64 then 25 else 0
                  else
                    if index < 63 then
                      if index < 62 then
                        fun f => if f.val = 56 then 16 else if f.val = 57 then 25 else if f.val = 58 then 16 else if f.val = 59 then 26 else if f.val = 60 then 17 else if f.val = 61 then 26 else 0
                      else
                        fun f => if f.val = 43 then 16 else if f.val = 46 then 17 else if f.val = 49 then 23 else if f.val = 62 then 17 else if f.val = 63 then 26 else if f.val = 64 then 26 else 0
                    else
                      if index < 64 then
                        fun f => if f.val = 43 then 17 else if f.val = 46 then 26 else if f.val = 49 then 26 else if f.val = 56 then 17 else if f.val = 57 then 26 else if f.val = 58 then 17 else 0
                      else
                        if index < 65 then
                          fun f => if f.val = 44 then 16 else if f.val = 45 then 17 else if f.val = 47 then 23 else if f.val = 48 then 22 else if f.val = 56 then 22 else if f.val = 59 then 22 else 0
                        else
                          fun f => if f.val = 44 then 17 else if f.val = 46 then 22 else if f.val = 48 then 23 else if f.val = 52 then 23 else if f.val = 55 then 17 else if f.val = 56 then 23 else 0
          else
            if index < 99 then
              if index < 82 then
                if index < 74 then
                  if index < 70 then
                    if index < 68 then
                      if index < 67 then
                        fun f => if f.val = 47 then 26 else if f.val = 48 then 25 else if f.val = 56 then 25 else if f.val = 57 then 16 else if f.val = 59 then 23 else if f.val = 61 then 17 else 0
                      else
                        fun f => if f.val = 46 then 23 else if f.val = 48 then 26 else if f.val = 49 then 17 else if f.val = 52 then 26 else if f.val = 56 then 26 else if f.val = 57 then 17 else 0
                    else
                      if index < 69 then
                        fun f => if f.val = 45 then 22 else if f.val = 51 then 13 else if f.val = 53 then 22 else if f.val = 54 then 22 else if f.val = 60 then 22 else if f.val = 62 then 22 else 0
                      else
                        fun f => if f.val = 44 then 22 else if f.val = 45 then 25 else if f.val = 51 then 14 else if f.val = 53 then 25 else if f.val = 58 then 22 else if f.val = 60 then 23 else 0
                  else
                    if index < 72 then
                      if index < 71 then
                        fun f => if f.val = 43 then 22 else if f.val = 51 then 16 else if f.val = 53 then 23 else if f.val = 54 then 25 else if f.val = 55 then 22 else if f.val = 62 then 23 else 0
                      else
                        fun f => if f.val = 43 then 23 else if f.val = 44 then 23 else if f.val = 51 then 17 else if f.val = 53 then 26 else if f.val = 55 then 25 else if f.val = 58 then 23 else 0
                    else
                      if index < 73 then
                        fun f => if f.val = 50 then 22 else if f.val = 51 then 22 else if f.val = 60 then 25 else if f.val = 61 then 22 else if f.val = 62 then 25 else if f.val = 63 then 22 else 0
                      else
                        fun f => if f.val = 50 then 25 else if f.val = 51 then 23 else if f.val = 57 then 22 else if f.val = 58 then 25 else if f.val = 60 then 26 else if f.val = 61 then 25 else 0
                else
                  if index < 78 then
                    if index < 76 then
                      if index < 75 then
                        fun f => if f.val = 43 then 25 else if f.val = 49 then 22 else if f.val = 50 then 23 else if f.val = 51 then 25 else if f.val = 62 then 26 else if f.val = 63 then 25 else 0
                      else
                        fun f => if f.val = 43 then 26 else if f.val = 49 then 25 else if f.val = 50 then 26 else if f.val = 51 then 26 else if f.val = 57 then 23 else if f.val = 58 then 26 else 0
                    else
                      if index < 77 then
                        fun f => if f.val = 67 then 16 else if f.val = 76 then 13 else if f.val = 80 then 22 else if f.val = 81 then 16 else if f.val = 83 then 13 else if f.val = 85 then 13 else 0
                      else
                        fun f => if f.val = 65 then 16 else if f.val = 68 then 22 else if f.val = 76 then 14 else if f.val = 77 then 16 else if f.val = 83 then 14 else if f.val = 85 then 14 else 0
                  else
                    if index < 80 then
                      if index < 79 then
                        fun f => if f.val = 80 then 25 else if f.val = 81 then 17 else if f.val = 82 then 16 else if f.val = 83 then 16 else if f.val = 84 then 13 else if f.val = 85 then 16 else 0
                      else
                        fun f => if f.val = 65 then 17 else if f.val = 68 then 25 else if f.val = 71 then 16 else if f.val = 83 then 17 else if f.val = 84 then 14 else if f.val = 85 then 17 else 0
                    else
                      if index < 81 then
                        fun f => if f.val = 67 then 17 else if f.val = 69 then 16 else if f.val = 76 then 16 else if f.val = 80 then 23 else if f.val = 85 then 22 else if f.val = 87 then 13 else if f.val = 88 then 13 else if f.val = 90 then 13 else if f.val = 91 then 13 else if f.val = 96 then 13 else 0
                      else
                        fun f => if f.val = 68 then 23 else if f.val = 74 then 16 else if f.val = 76 then 17 else if f.val = 77 then 17 else if f.val = 85 then 23 else if f.val = 87 then 14 else if f.val = 91 then 14 else if f.val = 95 then 13 else if f.val = 96 then 14 else if f.val = 98 then 13 else 0
              else
                if index < 90 then
                  if index < 86 then
                    if index < 84 then
                      if index < 83 then
                        fun f => if f.val = 69 then 17 else if f.val = 80 then 26 else if f.val = 82 then 17 else if f.val = 84 then 16 else if f.val = 85 then 25 else if f.val = 90 then 14 else if f.val = 91 then 16 else if f.val = 93 then 13 else if f.val = 100 then 13 else if f.val = 104 then 13 else 0
                      else
                        fun f => if f.val = 68 then 26 else if f.val = 71 then 17 else if f.val = 74 then 17 else if f.val = 84 then 17 else if f.val = 85 then 26 else if f.val = 91 then 17 else if f.val = 92 then 13 else if f.val = 93 then 14 else if f.val = 95 then 14 else if f.val = 100 then 14 else 0
                    else
                      if index < 85 then
                        fun f => if f.val = 67 then 25 else if f.val = 73 then 13 else if f.val = 75 then 13 else if f.val = 76 then 22 else if f.val = 81 then 25 else if f.val = 83 then 22 else 0
                      else
                        fun f => if f.val = 66 then 22 else if f.val = 67 then 22 else if f.val = 73 then 14 else if f.val = 75 then 14 else if f.val = 79 then 22 else if f.val = 81 then 22 else 0
                  else
                    if index < 88 then
                      if index < 87 then
                        fun f => if f.val = 65 then 25 else if f.val = 73 then 16 else if f.val = 75 then 16 else if f.val = 76 then 23 else if f.val = 77 then 25 else if f.val = 83 then 23 else 0
                      else
                        fun f => if f.val = 65 then 22 else if f.val = 66 then 25 else if f.val = 73 then 17 else if f.val = 75 then 17 else if f.val = 77 then 22 else if f.val = 79 then 23 else 0
                    else
                      if index < 89 then
                        fun f => if f.val = 72 then 13 else if f.val = 73 then 22 else if f.val = 81 then 26 else if f.val = 82 then 25 else if f.val = 83 then 25 else if f.val = 84 then 22 else 0
                      else
                        fun f => if f.val = 72 then 14 else if f.val = 73 then 23 else if f.val = 78 then 22 else if f.val = 79 then 25 else if f.val = 81 then 23 else if f.val = 82 then 22 else 0
                else
                  if index < 94 then
                    if index < 92 then
                      if index < 91 then
                        fun f => if f.val = 65 then 26 else if f.val = 71 then 25 else if f.val = 72 then 16 else if f.val = 73 then 25 else if f.val = 83 then 26 else if f.val = 84 then 23 else 0
                      else
                        fun f => if f.val = 65 then 23 else if f.val = 71 then 22 else if f.val = 72 then 17 else if f.val = 73 then 26 else if f.val = 78 then 25 else if f.val = 79 then 26 else 0
                    else
                      if index < 93 then
                        fun f => if f.val = 67 then 26 else if f.val = 69 then 25 else if f.val = 75 then 22 else if f.val = 76 then 25 else if f.val = 88 then 14 else if f.val = 90 then 16 else if f.val = 96 then 16 else if f.val = 97 then 13 else if f.val = 110 then 13 else if f.val = 112 then 13 else if f.val = 118 then 13 else if f.val = 119 then 13 else 0
                      else
                        fun f => if f.val = 66 then 23 else if f.val = 67 then 23 else if f.val = 69 then 22 else if f.val = 70 then 22 else if f.val = 75 then 23 else if f.val = 110 then 14 else if f.val = 112 then 14 else if f.val = 119 then 14 else if f.val = 124 then 13 else if f.val = 129 then 13 else 0
                  else
                    if index < 96 then
                      if index < 95 then
                        fun f => if f.val = 74 then 25 else if f.val = 75 then 25 else if f.val = 76 then 26 else if f.val = 77 then 26 else if f.val = 95 then 16 else if f.val = 96 then 17 else if f.val = 97 then 14 else if f.val = 98 then 14 else if f.val = 117 then 13 else if f.val = 118 then 14 else if f.val = 119 then 16 else if f.val = 120 then 13 else 0
                      else
                        fun f => if f.val = 66 then 26 else if f.val = 70 then 23 else if f.val = 74 then 22 else if f.val = 75 then 26 else if f.val = 77 then 23 else if f.val = 111 then 13 else if f.val = 117 then 14 else if f.val = 119 then 17 else if f.val = 120 then 14 else if f.val = 129 then 14 else 0
                    else
                      if index < 97 then
                        fun f => if f.val = 69 then 26 else if f.val = 72 then 22 else if f.val = 82 then 26 else if f.val = 84 then 25 else if f.val = 90 then 17 else if f.val = 93 then 16 else if f.val = 104 then 14 else if f.val = 106 then 13 else if f.val = 112 then 16 else if f.val = 115 then 13 else if f.val = 126 then 13 else if f.val = 128 then 13 else 0
                      else
                        if index < 98 then
                          fun f => if f.val = 69 then 23 else if f.val = 70 then 25 else if f.val = 72 then 23 else if f.val = 78 then 23 else if f.val = 82 then 23 else if f.val = 112 then 17 else if f.val = 124 then 14 else if f.val = 126 then 14 else if f.val = 128 then 14 else if f.val = 129 then 16 else 0
                        else
                          fun f => if f.val = 71 then 26 else if f.val = 72 then 25 else if f.val = 74 then 26 else if f.val = 84 then 26 else if f.val = 92 then 14 else if f.val = 93 then 17 else if f.val = 95 then 17 else if f.val = 106 then 14 else if f.val = 114 then 13 else if f.val = 115 then 14 else if f.val = 117 then 16 else if f.val = 128 then 16 else 0
            else
              if index < 116 then
                if index < 107 then
                  if index < 103 then
                    if index < 101 then
                      if index < 100 then
                        fun f => if f.val = 70 then 26 else if f.val = 71 then 23 else if f.val = 72 then 26 else if f.val = 74 then 23 else if f.val = 78 then 26 else if f.val = 111 then 14 else if f.val = 114 then 14 else if f.val = 117 then 17 else if f.val = 128 then 17 else if f.val = 129 then 17 else 0
                      else
                        fun f => if f.val = 88 then 26 else if f.val = 97 then 25 else if f.val = 102 then 13 else if f.val = 103 then 13 else if f.val = 105 then 13 else if f.val = 107 then 13 else 0
                    else
                      if index < 102 then
                        fun f => if f.val = 87 then 25 else if f.val = 88 then 25 else if f.val = 99 then 13 else if f.val = 101 then 13 else if f.val = 102 then 14 else if f.val = 103 then 14 else 0
                      else
                        fun f => if f.val = 86 then 13 else if f.val = 89 then 13 else if f.val = 97 then 26 else if f.val = 98 then 26 else if f.val = 105 then 14 else if f.val = 107 then 14 else 0
                  else
                    if index < 105 then
                      if index < 104 then
                        fun f => if f.val = 86 then 14 else if f.val = 87 then 26 else if f.val = 89 then 14 else if f.val = 98 then 25 else if f.val = 99 then 14 else if f.val = 101 then 14 else 0
                      else
                        fun f => if f.val = 102 then 16 else if f.val = 103 then 16 else if f.val = 104 then 26 else if f.val = 105 then 16 else if f.val = 106 then 25 else if f.val = 107 then 16 else 0
                    else
                      if index < 106 then
                        fun f => if f.val = 99 then 16 else if f.val = 100 then 25 else if f.val = 101 then 16 else if f.val = 102 then 17 else if f.val = 103 then 17 else if f.val = 104 then 25 else 0
                      else
                        fun f => if f.val = 86 then 16 else if f.val = 89 then 16 else if f.val = 92 then 26 else if f.val = 105 then 17 else if f.val = 106 then 26 else if f.val = 107 then 17 else 0
                else
                  if index < 111 then
                    if index < 109 then
                      if index < 108 then
                        fun f => if f.val = 86 then 17 else if f.val = 89 then 17 else if f.val = 92 then 25 else if f.val = 99 then 17 else if f.val = 100 then 26 else if f.val = 101 then 17 else 0
                      else
                        fun f => if f.val = 88 then 17 else if f.val = 90 then 25 else if f.val = 97 then 16 else if f.val = 102 then 22 else if f.val = 107 then 22 else if f.val = 109 then 13 else if f.val = 110 then 16 else if f.val = 112 then 22 else if f.val = 113 then 13 else if f.val = 118 then 16 else 0
                    else
                      if index < 110 then
                        fun f => if f.val = 87 then 16 else if f.val = 88 then 16 else if f.val = 90 then 22 else if f.val = 91 then 22 else if f.val = 99 then 22 else if f.val = 102 then 23 else 0
                      else
                        fun f => if f.val = 89 then 22 else if f.val = 95 then 25 else if f.val = 97 then 17 else if f.val = 98 then 17 else if f.val = 107 then 23 else if f.val = 109 then 14 else if f.val = 113 then 14 else if f.val = 117 then 22 else if f.val = 118 then 17 else if f.val = 120 then 16 else 0
                  else
                    if index < 113 then
                      if index < 112 then
                        fun f => if f.val = 87 then 17 else if f.val = 89 then 23 else if f.val = 91 then 23 else if f.val = 95 then 22 else if f.val = 98 then 16 else if f.val = 99 then 23 else 0
                      else
                        fun f => if f.val = 90 then 26 else if f.val = 102 then 25 else if f.val = 104 then 17 else if f.val = 106 then 16 else if f.val = 107 then 25 else if f.val = 112 then 25 else if f.val = 113 then 16 else if f.val = 115 then 16 else if f.val = 122 then 13 else if f.val = 126 then 16 else 0
                    else
                      if index < 114 then
                        fun f => if f.val = 90 then 23 else if f.val = 91 then 25 else if f.val = 99 then 25 else if f.val = 100 then 16 else if f.val = 102 then 26 else if f.val = 104 then 16 else 0
                      else
                        if index < 115 then
                          fun f => if f.val = 89 then 25 else if f.val = 92 then 17 else if f.val = 95 then 26 else if f.val = 106 then 17 else if f.val = 107 then 26 else if f.val = 113 then 17 else if f.val = 114 then 16 else if f.val = 115 then 17 else if f.val = 117 then 25 else if f.val = 122 then 14 else 0
                        else
                          fun f => if f.val = 89 then 26 else if f.val = 91 then 26 else if f.val = 92 then 16 else if f.val = 95 then 23 else if f.val = 99 then 26 else if f.val = 100 then 17 else 0
              else
                if index < 124 then
                  if index < 120 then
                    if index < 118 then
                      if index < 117 then
                        fun f => if f.val = 88 then 23 else if f.val = 94 then 13 else if f.val = 96 then 25 else if f.val = 97 then 22 else if f.val = 103 then 22 else if f.val = 105 then 22 else 0
                      else
                        fun f => if f.val = 87 then 22 else if f.val = 88 then 22 else if f.val = 94 then 14 else if f.val = 96 then 22 else if f.val = 101 then 22 else if f.val = 103 then 23 else 0
                    else
                      if index < 119 then
                        fun f => if f.val = 86 then 22 else if f.val = 94 then 16 else if f.val = 96 then 26 else if f.val = 97 then 23 else if f.val = 98 then 23 else if f.val = 105 then 23 else 0
                      else
                        fun f => if f.val = 86 then 23 else if f.val = 87 then 23 else if f.val = 94 then 17 else if f.val = 96 then 23 else if f.val = 98 then 22 else if f.val = 101 then 23 else 0
                  else
                    if index < 122 then
                      if index < 121 then
                        fun f => if f.val = 93 then 25 else if f.val = 94 then 22 else if f.val = 103 then 25 else if f.val = 104 then 23 else if f.val = 105 then 25 else if f.val = 106 then 22 else 0
                      else
                        fun f => if f.val = 93 then 22 else if f.val = 94 then 23 else if f.val = 100 then 22 else if f.val = 101 then 25 else if f.val = 103 then 26 else if f.val = 104 then 22 else 0
                    else
                      if index < 123 then
                        fun f => if f.val = 86 then 25 else if f.val = 92 then 23 else if f.val = 93 then 26 else if f.val = 94 then 25 else if f.val = 105 then 26 else if f.val = 106 then 23 else 0
                      else
                        fun f => if f.val = 86 then 26 else if f.val = 92 then 22 else if f.val = 93 then 23 else if f.val = 94 then 26 else if f.val = 100 then 23 else if f.val = 101 then 26 else 0
                else
                  if index < 128 then
                    if index < 126 then
                      if index < 125 then
                        fun f => if f.val = 110 then 23 else if f.val = 119 then 23 else if f.val = 124 then 16 else if f.val = 125 then 13 else if f.val = 127 then 13 else if f.val = 129 then 22 else 0
                      else
                        fun f => if f.val = 109 then 25 else if f.val = 110 then 26 else if f.val = 121 then 13 else if f.val = 123 then 13 else if f.val = 124 then 25 else if f.val = 125 then 14 else 0
                    else
                      if index < 127 then
                        fun f => if f.val = 108 then 13 else if f.val = 111 then 16 else if f.val = 119 then 26 else if f.val = 120 then 23 else if f.val = 127 then 14 else if f.val = 129 then 23 else 0
                      else
                        fun f => if f.val = 108 then 14 else if f.val = 109 then 26 else if f.val = 111 then 25 else if f.val = 120 then 26 else if f.val = 121 then 14 else if f.val = 123 then 14 else 0
                  else
                    if index < 130 then
                      if index < 129 then
                        fun f => if f.val = 124 then 17 else if f.val = 125 then 16 else if f.val = 126 then 23 else if f.val = 127 then 16 else if f.val = 128 then 23 else if f.val = 129 then 25 else 0
                      else
                        fun f => if f.val = 121 then 16 else if f.val = 122 then 25 else if f.val = 123 then 16 else if f.val = 124 then 26 else if f.val = 125 then 17 else if f.val = 126 then 26 else 0
                    else
                      if index < 131 then
                        fun f => if f.val = 108 then 16 else if f.val = 111 then 17 else if f.val = 114 then 23 else if f.val = 127 then 17 else if f.val = 128 then 26 else if f.val = 129 then 26 else 0
                      else
                        if index < 132 then
                          fun f => if f.val = 108 then 17 else if f.val = 111 then 26 else if f.val = 114 then 26 else if f.val = 121 then 17 else if f.val = 122 then 26 else if f.val = 123 then 17 else 0
                        else
                          fun f => if f.val = 109 then 16 else if f.val = 110 then 17 else if f.val = 112 then 23 else if f.val = 113 then 22 else if f.val = 121 then 22 else if f.val = 124 then 22 else 0
        else
          if index < 200 then
            if index < 166 then
              if index < 149 then
                if index < 141 then
                  if index < 137 then
                    if index < 135 then
                      if index < 134 then
                        fun f => if f.val = 109 then 17 else if f.val = 111 then 22 else if f.val = 113 then 23 else if f.val = 117 then 23 else if f.val = 120 then 17 else if f.val = 121 then 23 else 0
                      else
                        fun f => if f.val = 112 then 26 else if f.val = 113 then 25 else if f.val = 121 then 25 else if f.val = 122 then 16 else if f.val = 124 then 23 else if f.val = 126 then 17 else 0
                    else
                      if index < 136 then
                        fun f => if f.val = 111 then 23 else if f.val = 113 then 26 else if f.val = 114 then 17 else if f.val = 117 then 26 else if f.val = 121 then 26 else if f.val = 122 then 17 else 0
                      else
                        fun f => if f.val = 110 then 22 else if f.val = 116 then 13 else if f.val = 118 then 22 else if f.val = 119 then 22 else if f.val = 125 then 22 else if f.val = 127 then 22 else 0
                  else
                    if index < 139 then
                      if index < 138 then
                        fun f => if f.val = 109 then 22 else if f.val = 110 then 25 else if f.val = 116 then 14 else if f.val = 118 then 25 else if f.val = 123 then 22 else if f.val = 125 then 23 else 0
                      else
                        fun f => if f.val = 108 then 22 else if f.val = 116 then 16 else if f.val = 118 then 23 else if f.val = 119 then 25 else if f.val = 120 then 22 else if f.val = 127 then 23 else 0
                    else
                      if index < 140 then
                        fun f => if f.val = 108 then 23 else if f.val = 109 then 23 else if f.val = 116 then 17 else if f.val = 118 then 26 else if f.val = 120 then 25 else if f.val = 123 then 23 else 0
                      else
                        fun f => if f.val = 115 then 22 else if f.val = 116 then 22 else if f.val = 125 then 25 else if f.val = 126 then 22 else if f.val = 127 then 25 else if f.val = 128 then 22 else 0
                else
                  if index < 145 then
                    if index < 143 then
                      if index < 142 then
                        fun f => if f.val = 115 then 25 else if f.val = 116 then 23 else if f.val = 122 then 22 else if f.val = 123 then 25 else if f.val = 125 then 26 else if f.val = 126 then 25 else 0
                      else
                        fun f => if f.val = 108 then 25 else if f.val = 114 then 22 else if f.val = 115 then 23 else if f.val = 116 then 25 else if f.val = 127 then 26 else if f.val = 128 then 25 else 0
                    else
                      if index < 144 then
                        fun f => if f.val = 108 then 26 else if f.val = 114 then 25 else if f.val = 115 then 26 else if f.val = 116 then 26 else if f.val = 122 then 23 else if f.val = 123 then 26 else 0
                      else
                        fun f => if f.val = 2 then 12 else if f.val = 15 then 12 else if f.val = 16 then 12 else 0
                  else
                    if index < 147 then
                      if index < 146 then
                        fun f => if f.val = 11 then 12 else if f.val = 18 then 12 else if f.val = 20 then 12 else 0
                      else
                        fun f => if f.val = 15 then 10 else if f.val = 16 then 10 else if f.val = 18 then 10 else if f.val = 20 then 10 else 0
                    else
                      if index < 148 then
                        fun f => if f.val = 2 then 10 else if f.val = 11 then 10 else if f.val = 15 then 4 else if f.val = 20 then 4 else 0
                      else
                        fun f => if f.val = 2 then 4 else if f.val = 11 then 4 else if f.val = 16 then 4 else if f.val = 18 then 4 else 0
              else
                if index < 157 then
                  if index < 153 then
                    if index < 151 then
                      if index < 150 then
                        fun f => if f.val = 1 then 12 else if f.val = 14 then 12 else if f.val = 66 then 12 else if f.val = 67 then 12 else if f.val = 80 then 12 else 0
                      else
                        fun f => if f.val = 14 then 10 else if f.val = 15 then 11 else if f.val = 16 then 11 else if f.val = 66 then 10 else if f.val = 79 then 12 else 0
                    else
                      if index < 152 then
                        fun f => if f.val = 1 then 10 else if f.val = 2 then 11 else if f.val = 15 then 5 else if f.val = 79 then 10 else if f.val = 80 then 10 else if f.val = 81 then 12 else 0
                      else
                        fun f => if f.val = 1 then 4 else if f.val = 2 then 5 else if f.val = 14 then 4 else if f.val = 16 then 5 else 0
                  else
                    if index < 155 then
                      if index < 154 then
                        fun f => if f.val = 67 then 10 else if f.val = 80 then 4 else if f.val = 81 then 10 else 0
                      else
                        fun f => if f.val = 66 then 4 else if f.val = 67 then 4 else if f.val = 79 then 4 else if f.val = 81 then 4 else 0
                    else
                      if index < 156 then
                        fun f => if f.val = 0 then 12 else if f.val = 3 then 12 else if f.val = 12 then 12 else 0
                      else
                        fun f => if f.val = 0 then 10 else if f.val = 3 then 10 else if f.val = 18 then 11 else if f.val = 20 then 11 else 0
                else
                  if index < 161 then
                    if index < 159 then
                      if index < 158 then
                        fun f => if f.val = 3 then 4 else if f.val = 11 then 11 else if f.val = 12 then 10 else if f.val = 20 then 5 else 0
                      else
                        fun f => if f.val = 0 then 4 else if f.val = 11 then 5 else if f.val = 12 then 4 else if f.val = 18 then 5 else 0
                    else
                      if index < 160 then
                        fun f => if f.val = 0 then 11 else if f.val = 3 then 11 else if f.val = 14 then 11 else if f.val = 66 then 11 else if f.val = 70 then 12 else 0
                      else
                        fun f => if f.val = 1 then 11 else if f.val = 3 then 5 else if f.val = 12 then 11 else if f.val = 69 then 12 else if f.val = 70 then 10 else if f.val = 80 then 11 else 0
                  else
                    if index < 163 then
                      if index < 162 then
                        fun f => if f.val = 0 then 5 else if f.val = 1 then 5 else if f.val = 12 then 5 else if f.val = 14 then 5 else 0
                      else
                        fun f => if f.val = 67 then 11 else if f.val = 69 then 10 else if f.val = 80 then 5 else 0
                    else
                      if index < 164 then
                        fun f => if f.val = 66 then 5 else if f.val = 67 then 5 else if f.val = 69 then 4 else if f.val = 70 then 4 else 0
                      else
                        if index < 165 then
                          fun f => if f.val = 15 then 15 else if f.val = 16 then 15 else if f.val = 17 then 12 else 0
                        else
                          fun f => if f.val = 18 then 15 else if f.val = 19 then 12 else if f.val = 20 then 15 else 0
            else
              if index < 183 then
                if index < 174 then
                  if index < 170 then
                    if index < 168 then
                      if index < 167 then
                        fun f => if f.val = 15 then 7 else if f.val = 17 then 10 else if f.val = 19 then 10 else if f.val = 20 then 7 else 0
                      else
                        fun f => if f.val = 16 then 7 else if f.val = 17 then 4 else if f.val = 18 then 7 else if f.val = 19 then 4 else 0
                    else
                      if index < 169 then
                        fun f => if f.val = 13 then 12 else if f.val = 14 then 15 else if f.val = 66 then 15 else if f.val = 68 then 12 else if f.val = 77 then 12 else 0
                      else
                        fun f => if f.val = 13 then 10 else if f.val = 15 then 8 else if f.val = 17 then 11 else if f.val = 65 then 12 else if f.val = 68 then 10 else if f.val = 79 then 11 else 0
                  else
                    if index < 172 then
                      if index < 171 then
                        fun f => if f.val = 13 then 4 else if f.val = 14 then 7 else if f.val = 16 then 8 else if f.val = 17 then 5 else 0
                      else
                        fun f => if f.val = 65 then 10 else if f.val = 68 then 4 else if f.val = 77 then 10 else 0
                    else
                      if index < 173 then
                        fun f => if f.val = 65 then 4 else if f.val = 66 then 7 else if f.val = 77 then 4 else if f.val = 79 then 5 else 0
                      else
                        fun f => if f.val = 0 then 15 else if f.val = 3 then 15 else if f.val = 6 then 12 else 0
                else
                  if index < 178 then
                    if index < 176 then
                      if index < 175 then
                        fun f => if f.val = 3 then 7 else if f.val = 6 then 10 else if f.val = 19 then 11 else if f.val = 20 then 8 else 0
                      else
                        fun f => if f.val = 0 then 7 else if f.val = 6 then 4 else if f.val = 18 then 8 else if f.val = 19 then 5 else 0
                    else
                      if index < 177 then
                        fun f => if f.val = 3 then 8 else if f.val = 6 then 11 else if f.val = 13 then 11 else if f.val = 68 then 11 else if f.val = 70 then 11 else if f.val = 74 then 12 else 0
                      else
                        fun f => if f.val = 0 then 8 else if f.val = 6 then 5 else if f.val = 13 then 5 else if f.val = 14 then 8 else 0
                  else
                    if index < 180 then
                      if index < 179 then
                        fun f => if f.val = 68 then 5 else if f.val = 74 then 10 else if f.val = 77 then 11 else 0
                      else
                        fun f => if f.val = 66 then 8 else if f.val = 70 then 5 else if f.val = 74 then 4 else if f.val = 77 then 5 else 0
                    else
                      if index < 181 then
                        fun f => if f.val = 2 then 15 else if f.val = 4 then 12 else if f.val = 15 then 21 else 0
                      else
                        if index < 182 then
                          fun f => if f.val = 11 then 15 else if f.val = 20 then 21 else if f.val = 22 then 12 else if f.val = 26 then 12 else if f.val = 31 then 12 else 0
                        else
                          fun f => if f.val = 4 then 10 else if f.val = 15 then 19 else if f.val = 20 then 19 else if f.val = 25 then 12 else if f.val = 26 then 10 else 0
              else
                if index < 191 then
                  if index < 187 then
                    if index < 185 then
                      if index < 184 then
                        fun f => if f.val = 2 then 7 else if f.val = 4 then 4 else if f.val = 11 then 7 else if f.val = 23 then 12 else if f.val = 25 then 10 else if f.val = 31 then 10 else 0
                      else
                        fun f => if f.val = 22 then 10 else if f.val = 23 then 10 else if f.val = 25 then 4 else if f.val = 26 then 4 else 0
                    else
                      if index < 186 then
                        fun f => if f.val = 22 then 4 else if f.val = 23 then 4 else if f.val = 31 then 4 else 0
                      else
                        fun f => if f.val = 1 then 15 else if f.val = 5 then 12 else if f.val = 78 then 12 else if f.val = 80 then 15 else if f.val = 82 then 12 else 0
                  else
                    if index < 189 then
                      if index < 188 then
                        fun f => if f.val = 4 then 11 else if f.val = 5 then 10 else if f.val = 15 then 20 else if f.val = 78 then 10 else if f.val = 79 then 15 else 0
                      else
                        fun f => if f.val = 1 then 7 else if f.val = 2 then 8 else if f.val = 4 then 5 else if f.val = 5 then 4 else 0
                    else
                      if index < 190 then
                        fun f => if f.val = 80 then 7 else if f.val = 81 then 11 else if f.val = 82 then 10 else 0
                      else
                        fun f => if f.val = 78 then 4 else if f.val = 79 then 7 else if f.val = 81 then 5 else if f.val = 82 then 4 else 0
                else
                  if index < 195 then
                    if index < 193 then
                      if index < 192 then
                        fun f => if f.val = 3 then 21 else if f.val = 9 then 12 else if f.val = 12 then 15 else 0
                      else
                        fun f => if f.val = 3 then 19 else if f.val = 9 then 10 else if f.val = 20 then 20 else if f.val = 26 then 11 else if f.val = 30 then 12 else 0
                    else
                      if index < 194 then
                        fun f => if f.val = 9 then 4 else if f.val = 11 then 8 else if f.val = 12 then 7 else if f.val = 30 then 10 else if f.val = 31 then 11 else if f.val = 33 then 12 else 0
                      else
                        fun f => if f.val = 22 then 11 else if f.val = 26 then 5 else if f.val = 30 then 4 else if f.val = 33 then 10 else 0
                  else
                    if index < 197 then
                      if index < 196 then
                        fun f => if f.val = 22 then 5 else if f.val = 31 then 5 else if f.val = 33 then 4 else 0
                      else
                        fun f => if f.val = 3 then 20 else if f.val = 5 then 11 else if f.val = 9 then 11 else if f.val = 70 then 15 else if f.val = 78 then 11 else 0
                    else
                      if index < 198 then
                        fun f => if f.val = 1 then 8 else if f.val = 5 then 5 else if f.val = 9 then 5 else if f.val = 12 then 8 else 0
                      else
                        if index < 199 then
                          fun f => if f.val = 69 then 11 else if f.val = 80 then 8 else if f.val = 82 then 11 else 0
                        else
                          fun f => if f.val = 69 then 5 else if f.val = 70 then 7 else if f.val = 78 then 5 else if f.val = 82 then 5 else 0
          else
            if index < 233 then
              if index < 216 then
                if index < 208 then
                  if index < 204 then
                    if index < 202 then
                      if index < 201 then
                        fun f => if f.val = 4 then 15 else if f.val = 15 then 24 else if f.val = 17 then 15 else 0
                      else
                        fun f => if f.val = 19 then 15 else if f.val = 20 then 24 else if f.val = 26 then 15 else if f.val = 28 then 12 else if f.val = 35 then 12 else 0
                    else
                      if index < 203 then
                        fun f => if f.val = 4 then 7 else if f.val = 17 then 7 else if f.val = 19 then 7 else if f.val = 25 then 11 else if f.val = 28 then 10 else if f.val = 39 then 12 else 0
                      else
                        fun f => if f.val = 25 then 5 else if f.val = 26 then 7 else if f.val = 35 then 10 else if f.val = 39 then 10 else 0
                  else
                    if index < 206 then
                      if index < 205 then
                        fun f => if f.val = 28 then 4 else if f.val = 35 then 4 else if f.val = 39 then 4 else 0
                      else
                        fun f => if f.val = 5 then 15 else if f.val = 13 then 15 else if f.val = 68 then 15 else if f.val = 71 then 12 else if f.val = 78 then 15 else 0
                    else
                      if index < 207 then
                        fun f => if f.val = 4 then 8 else if f.val = 5 then 7 else if f.val = 13 then 7 else if f.val = 17 then 8 else 0
                      else
                        fun f => if f.val = 65 then 11 else if f.val = 68 then 7 else if f.val = 71 then 10 else 0
                else
                  if index < 212 then
                    if index < 210 then
                      if index < 209 then
                        fun f => if f.val = 65 then 5 else if f.val = 71 then 4 else if f.val = 78 then 7 else if f.val = 79 then 8 else 0
                      else
                        fun f => if f.val = 3 then 24 else if f.val = 6 then 15 else if f.val = 9 then 15 else 0
                    else
                      if index < 211 then
                        fun f => if f.val = 6 then 7 else if f.val = 9 then 7 else if f.val = 19 then 8 else if f.val = 27 then 12 else if f.val = 28 then 11 else if f.val = 30 then 11 else 0
                      else
                        fun f => if f.val = 26 then 8 else if f.val = 27 then 10 else if f.val = 30 then 5 else if f.val = 35 then 11 else 0
                  else
                    if index < 214 then
                      if index < 213 then
                        fun f => if f.val = 27 then 4 else if f.val = 28 then 5 else if f.val = 35 then 5 else 0
                      else
                        fun f => if f.val = 5 then 8 else if f.val = 6 then 8 else if f.val = 9 then 8 else if f.val = 13 then 8 else 0
                    else
                      if index < 215 then
                        fun f => if f.val = 68 then 8 else if f.val = 71 then 11 else if f.val = 74 then 11 else 0
                      else
                        fun f => if f.val = 70 then 8 else if f.val = 71 then 5 else if f.val = 74 then 5 else if f.val = 78 then 8 else 0
              else
                if index < 224 then
                  if index < 220 then
                    if index < 218 then
                      if index < 217 then
                        fun f => if f.val = 2 then 21 else if f.val = 8 then 12 else if f.val = 10 then 12 else if f.val = 16 then 21 else 0
                      else
                        fun f => if f.val = 8 then 10 else if f.val = 10 then 10 else if f.val = 11 then 21 else if f.val = 18 then 21 else 0
                    else
                      if index < 219 then
                        fun f => if f.val = 8 then 4 else if f.val = 16 then 19 else if f.val = 18 then 19 else 0
                      else
                        fun f => if f.val = 2 then 19 else if f.val = 10 then 4 else if f.val = 11 then 19 else 0
                  else
                    if index < 222 then
                      if index < 221 then
                        fun f => if f.val = 1 then 21 else if f.val = 8 then 11 else if f.val = 10 then 11 else if f.val = 14 then 21 else 0
                      else
                        fun f => if f.val = 8 then 5 else if f.val = 14 then 19 else if f.val = 16 then 20 else 0
                    else
                      if index < 223 then
                        fun f => if f.val = 1 then 19 else if f.val = 2 then 20 else if f.val = 10 then 5 else 0
                      else
                        fun f => if f.val = 0 then 21 else if f.val = 8 then 15 else if f.val = 10 then 15 else if f.val = 12 then 21 else 0
                else
                  if index < 228 then
                    if index < 226 then
                      if index < 225 then
                        fun f => if f.val = 0 then 19 else if f.val = 8 then 7 else if f.val = 18 then 20 else 0
                      else
                        fun f => if f.val = 10 then 7 else if f.val = 11 then 20 else if f.val = 12 then 19 else 0
                    else
                      if index < 227 then
                        fun f => if f.val = 0 then 20 else if f.val = 8 then 8 else if f.val = 14 then 20 else 0
                      else
                        fun f => if f.val = 1 then 20 else if f.val = 10 then 8 else if f.val = 12 then 20 else 0
                  else
                    if index < 230 then
                      if index < 229 then
                        fun f => if f.val = 7 then 12 else if f.val = 8 then 21 else if f.val = 16 then 24 else if f.val = 17 then 21 else 0
                      else
                        fun f => if f.val = 7 then 10 else if f.val = 8 then 19 else if f.val = 18 then 24 else if f.val = 19 then 21 else 0
                    else
                      if index < 231 then
                        fun f => if f.val = 7 then 4 else if f.val = 17 then 19 else if f.val = 19 then 19 else 0
                      else
                        if index < 232 then
                          fun f => if f.val = 7 then 11 else if f.val = 8 then 20 else if f.val = 13 then 21 else if f.val = 14 then 24 else 0
                        else
                          fun f => if f.val = 7 then 5 else if f.val = 13 then 19 else if f.val = 17 then 20 else 0
            else
              if index < 250 then
                if index < 241 then
                  if index < 237 then
                    if index < 235 then
                      if index < 234 then
                        fun f => if f.val = 0 then 24 else if f.val = 6 then 21 else if f.val = 7 then 15 else if f.val = 8 then 24 else 0
                      else
                        fun f => if f.val = 6 then 19 else if f.val = 7 then 7 else if f.val = 19 then 20 else 0
                    else
                      if index < 236 then
                        fun f => if f.val = 6 then 20 else if f.val = 7 then 8 else if f.val = 13 then 20 else 0
                      else
                        fun f => if f.val = 2 then 24 else if f.val = 4 then 21 else if f.val = 10 then 21 else if f.val = 45 then 12 else if f.val = 47 then 12 else if f.val = 54 then 12 else 0
                  else
                    if index < 239 then
                      if index < 238 then
                        fun f => if f.val = 10 then 19 else if f.val = 11 then 24 else if f.val = 31 then 15 else if f.val = 32 then 12 else if f.val = 53 then 12 else if f.val = 54 then 10 else 0
                      else
                        fun f => if f.val = 4 then 19 else if f.val = 25 then 15 else if f.val = 47 then 10 else 0
                    else
                      if index < 240 then
                        fun f => if f.val = 23 then 11 else if f.val = 25 then 7 else if f.val = 32 then 10 else if f.val = 45 then 10 else if f.val = 47 then 4 else if f.val = 53 then 10 else 0
                      else
                        fun f => if f.val = 23 then 5 else if f.val = 31 then 7 else if f.val = 32 then 4 else 0
                else
                  if index < 245 then
                    if index < 243 then
                      if index < 242 then
                        fun f => if f.val = 45 then 4 else if f.val = 53 then 4 else if f.val = 54 then 4 else 0
                      else
                        fun f => if f.val = 1 then 24 else if f.val = 5 then 21 else if f.val = 10 then 20 else if f.val = 54 then 11 else if f.val = 64 then 12 else 0
                    else
                      if index < 244 then
                        fun f => if f.val = 4 then 20 else if f.val = 5 then 19 else if f.val = 47 then 11 else if f.val = 59 then 12 else if f.val = 64 then 10 else 0
                      else
                        fun f => if f.val = 45 then 5 else if f.val = 54 then 5 else if f.val = 59 then 10 else if f.val = 64 then 4 else 0
                  else
                    if index < 247 then
                      if index < 246 then
                        fun f => if f.val = 45 then 11 else if f.val = 47 then 5 else if f.val = 59 then 4 else 0
                      else
                        fun f => if f.val = 9 then 21 else if f.val = 10 then 24 else if f.val = 12 then 24 else if f.val = 52 then 12 else if f.val = 54 then 15 else if f.val = 55 then 12 else 0
                    else
                      if index < 248 then
                        fun f => if f.val = 9 then 19 else if f.val = 30 then 15 else if f.val = 52 then 10 else 0
                      else
                        if index < 249 then
                          fun f => if f.val = 30 then 7 else if f.val = 32 then 11 else if f.val = 33 then 11 else if f.val = 52 then 4 else if f.val = 53 then 11 else if f.val = 55 then 10 else 0
                        else
                          fun f => if f.val = 31 then 8 else if f.val = 32 then 5 else if f.val = 33 then 5 else 0
              else
                if index < 258 then
                  if index < 254 then
                    if index < 252 then
                      if index < 251 then
                        fun f => if f.val = 53 then 5 else if f.val = 54 then 7 else if f.val = 55 then 4 else 0
                      else
                        fun f => if f.val = 5 then 20 else if f.val = 9 then 20 else if f.val = 46 then 12 else if f.val = 52 then 11 else if f.val = 64 then 11 else 0
                    else
                      if index < 253 then
                        fun f => if f.val = 46 then 10 else if f.val = 54 then 8 else if f.val = 55 then 5 else if f.val = 64 then 5 else 0
                      else
                        fun f => if f.val = 46 then 4 else if f.val = 52 then 5 else if f.val = 55 then 11 else 0
                  else
                    if index < 256 then
                      if index < 255 then
                        fun f => if f.val = 4 then 24 else if f.val = 7 then 21 else if f.val = 17 then 24 else if f.val = 47 then 15 else if f.val = 61 then 12 else if f.val = 63 then 12 else 0
                      else
                        fun f => if f.val = 7 then 19 else if f.val = 19 then 24 else if f.val = 28 then 15 else if f.val = 41 then 12 else if f.val = 50 then 12 else if f.val = 63 then 10 else 0
                    else
                      if index < 257 then
                        fun f => if f.val = 25 then 8 else if f.val = 39 then 11 else if f.val = 41 then 10 else if f.val = 47 then 7 else if f.val = 50 then 10 else if f.val = 61 then 10 else 0
                      else
                        fun f => if f.val = 28 then 7 else if f.val = 39 then 5 else if f.val = 41 then 4 else 0
                else
                  if index < 262 then
                    if index < 260 then
                      if index < 259 then
                        fun f => if f.val = 50 then 4 else if f.val = 61 then 4 else if f.val = 63 then 4 else 0
                      else
                        fun f => if f.val = 5 then 24 else if f.val = 7 then 20 else if f.val = 13 then 24 else if f.val = 63 then 11 else if f.val = 64 then 15 else 0
                    else
                      if index < 261 then
                        fun f => if f.val = 59 then 11 else if f.val = 61 then 5 else if f.val = 63 then 5 else if f.val = 64 then 7 else 0
                      else
                        fun f => if f.val = 47 then 8 else if f.val = 59 then 5 else if f.val = 61 then 11 else 0
                  else
                    if index < 264 then
                      if index < 263 then
                        fun f => if f.val = 6 then 24 else if f.val = 7 then 24 else if f.val = 9 then 24 else if f.val = 49 then 12 else if f.val = 52 then 15 else if f.val = 63 then 15 else 0
                      else
                        fun f => if f.val = 27 then 11 else if f.val = 30 then 8 else if f.val = 41 then 11 else if f.val = 49 then 10 else if f.val = 50 then 11 else if f.val = 52 then 7 else 0
                    else
                      if index < 265 then
                        fun f => if f.val = 27 then 5 else if f.val = 28 then 8 else if f.val = 41 then 5 else 0
                      else
                        if index < 266 then
                          fun f => if f.val = 49 then 4 else if f.val = 50 then 5 else if f.val = 63 then 7 else 0
                        else
                          fun f => if f.val = 46 then 11 else if f.val = 49 then 5 else if f.val = 63 then 8 else if f.val = 64 then 8 else 0
      else
        if index < 400 then
          if index < 333 then
            if index < 300 then
              if index < 283 then
                if index < 275 then
                  if index < 271 then
                    if index < 269 then
                      if index < 268 then
                        fun f => if f.val = 46 then 5 else if f.val = 49 then 11 else if f.val = 52 then 8 else 0
                      else
                        fun f => if f.val = 23 then 24 else if f.val = 37 then 12 else if f.val = 38 then 12 else 0
                    else
                      if index < 270 then
                        fun f => if f.val = 32 then 24 else if f.val = 40 then 12 else if f.val = 42 then 12 else 0
                      else
                        fun f => if f.val = 37 then 10 else if f.val = 38 then 10 else if f.val = 40 then 10 else if f.val = 42 then 10 else 0
                  else
                    if index < 273 then
                      if index < 272 then
                        fun f => if f.val = 23 then 8 else if f.val = 32 then 7 else if f.val = 37 then 4 else if f.val = 42 then 4 else 0
                      else
                        fun f => if f.val = 23 then 20 else if f.val = 32 then 19 else if f.val = 38 then 4 else if f.val = 40 then 4 else 0
                    else
                      if index < 274 then
                        fun f => if f.val = 22 then 24 else if f.val = 34 then 12 else if f.val = 36 then 12 else 0
                      else
                        fun f => if f.val = 34 then 10 else if f.val = 36 then 10 else if f.val = 37 then 11 else if f.val = 38 then 11 else 0
                else
                  if index < 279 then
                    if index < 277 then
                      if index < 276 then
                        fun f => if f.val = 22 then 7 else if f.val = 23 then 7 else if f.val = 34 then 4 else if f.val = 37 then 5 else 0
                      else
                        fun f => if f.val = 22 then 19 else if f.val = 23 then 19 else if f.val = 36 then 4 else if f.val = 38 then 5 else 0
                    else
                      if index < 278 then
                        fun f => if f.val = 21 then 12 else if f.val = 24 then 12 else if f.val = 33 then 24 else 0
                      else
                        fun f => if f.val = 21 then 10 else if f.val = 24 then 10 else if f.val = 40 then 11 else if f.val = 42 then 11 else 0
                  else
                    if index < 281 then
                      if index < 280 then
                        fun f => if f.val = 24 then 4 else if f.val = 32 then 8 else if f.val = 33 then 8 else if f.val = 42 then 5 else 0
                      else
                        fun f => if f.val = 21 then 4 else if f.val = 32 then 20 else if f.val = 33 then 20 else if f.val = 40 then 5 else 0
                    else
                      if index < 282 then
                        fun f => if f.val = 21 then 11 else if f.val = 24 then 11 else if f.val = 34 then 11 else if f.val = 36 then 11 else 0
                      else
                        fun f => if f.val = 22 then 8 else if f.val = 24 then 5 else if f.val = 33 then 7 else if f.val = 34 then 5 else 0
              else
                if index < 291 then
                  if index < 287 then
                    if index < 285 then
                      if index < 284 then
                        fun f => if f.val = 21 then 5 else if f.val = 22 then 20 else if f.val = 33 then 19 else if f.val = 36 then 5 else 0
                      else
                        fun f => if f.val = 37 then 15 else if f.val = 38 then 15 else if f.val = 39 then 24 else 0
                    else
                      if index < 286 then
                        fun f => if f.val = 40 then 15 else if f.val = 41 then 24 else if f.val = 42 then 15 else 0
                      else
                        fun f => if f.val = 37 then 7 else if f.val = 39 then 8 else if f.val = 41 then 7 else if f.val = 42 then 7 else 0
                  else
                    if index < 289 then
                      if index < 288 then
                        fun f => if f.val = 38 then 7 else if f.val = 39 then 20 else if f.val = 40 then 7 else if f.val = 41 then 19 else 0
                      else
                        fun f => if f.val = 34 then 15 else if f.val = 35 then 24 else if f.val = 36 then 15 else 0
                    else
                      if index < 290 then
                        fun f => if f.val = 34 then 7 else if f.val = 35 then 7 else if f.val = 37 then 8 else if f.val = 39 then 7 else 0
                      else
                        fun f => if f.val = 35 then 19 else if f.val = 36 then 7 else if f.val = 38 then 8 else if f.val = 39 then 19 else 0
                else
                  if index < 295 then
                    if index < 293 then
                      if index < 292 then
                        fun f => if f.val = 21 then 15 else if f.val = 24 then 15 else if f.val = 27 then 24 else 0
                      else
                        fun f => if f.val = 24 then 7 else if f.val = 27 then 8 else if f.val = 41 then 8 else if f.val = 42 then 8 else 0
                    else
                      if index < 294 then
                        fun f => if f.val = 21 then 7 else if f.val = 27 then 20 else if f.val = 40 then 8 else if f.val = 41 then 20 else 0
                      else
                        fun f => if f.val = 24 then 8 else if f.val = 27 then 7 else if f.val = 34 then 8 else if f.val = 35 then 8 else 0
                  else
                    if index < 297 then
                      if index < 296 then
                        fun f => if f.val = 21 then 8 else if f.val = 27 then 19 else if f.val = 35 then 20 else if f.val = 36 then 8 else 0
                      else
                        fun f => if f.val = 23 then 15 else if f.val = 25 then 19 else if f.val = 37 then 21 else 0
                    else
                      if index < 298 then
                        fun f => if f.val = 32 then 15 else if f.val = 42 then 21 else if f.val = 44 then 12 else if f.val = 48 then 12 else if f.val = 53 then 15 else 0
                      else
                        if index < 299 then
                          fun f => if f.val = 25 then 24 else if f.val = 37 then 19 else if f.val = 42 then 19 else if f.val = 47 then 19 else if f.val = 48 then 10 else 0
                        else
                          fun f => if f.val = 44 then 10 else if f.val = 45 then 15 else if f.val = 47 then 21 else if f.val = 48 then 4 else 0
            else
              if index < 316 then
                if index < 308 then
                  if index < 304 then
                    if index < 302 then
                      if index < 301 then
                        fun f => if f.val = 44 then 4 else if f.val = 45 then 7 else if f.val = 53 then 7 else 0
                      else
                        fun f => if f.val = 22 then 15 else if f.val = 26 then 21 else if f.val = 34 then 21 else 0
                    else
                      if index < 303 then
                        fun f => if f.val = 25 then 21 else if f.val = 26 then 19 else if f.val = 34 then 19 else if f.val = 37 then 20 else 0
                      else
                        fun f => if f.val = 24 then 21 else if f.val = 30 then 19 else if f.val = 33 then 15 else 0
                  else
                    if index < 306 then
                      if index < 305 then
                        fun f => if f.val = 24 then 19 else if f.val = 30 then 24 else if f.val = 42 then 20 else if f.val = 48 then 11 else if f.val = 52 then 19 else 0
                      else
                        fun f => if f.val = 44 then 11 else if f.val = 48 then 5 else if f.val = 52 then 21 else if f.val = 55 then 15 else 0
                    else
                      if index < 307 then
                        fun f => if f.val = 44 then 5 else if f.val = 53 then 8 else if f.val = 55 then 7 else 0
                      else
                        fun f => if f.val = 24 then 20 else if f.val = 26 then 20 else if f.val = 30 then 21 else if f.val = 34 then 20 else 0
                else
                  if index < 312 then
                    if index < 310 then
                      if index < 309 then
                        fun f => if f.val = 25 then 20 else if f.val = 37 then 24 else if f.val = 39 then 15 else 0
                      else
                        fun f => if f.val = 41 then 15 else if f.val = 42 then 24 else if f.val = 48 then 15 else if f.val = 50 then 15 else if f.val = 57 then 12 else 0
                    else
                      if index < 311 then
                        fun f => if f.val = 47 then 24 else if f.val = 48 then 7 else if f.val = 57 then 10 else if f.val = 61 then 15 else 0
                      else
                        fun f => if f.val = 50 then 7 else if f.val = 57 then 4 else if f.val = 61 then 7 else 0
                  else
                    if index < 314 then
                      if index < 313 then
                        fun f => if f.val = 26 then 24 else if f.val = 34 then 24 else if f.val = 35 then 15 else 0
                      else
                        fun f => if f.val = 24 then 24 else if f.val = 27 then 15 else if f.val = 30 then 20 else 0
                    else
                      if index < 315 then
                        fun f => if f.val = 48 then 8 else if f.val = 49 then 15 else if f.val = 52 then 24 else if f.val = 57 then 11 else 0
                      else
                        fun f => if f.val = 49 then 7 else if f.val = 50 then 8 else if f.val = 57 then 5 else 0
              else
                if index < 324 then
                  if index < 320 then
                    if index < 318 then
                      if index < 317 then
                        fun f => if f.val = 23 then 21 else if f.val = 29 then 12 else if f.val = 31 then 19 else if f.val = 38 then 21 else 0
                      else
                        fun f => if f.val = 29 then 10 else if f.val = 31 then 24 else if f.val = 32 then 21 else if f.val = 40 then 21 else 0
                    else
                      if index < 319 then
                        fun f => if f.val = 29 then 4 else if f.val = 38 then 19 else if f.val = 40 then 19 else 0
                      else
                        fun f => if f.val = 22 then 21 else if f.val = 29 then 11 else if f.val = 31 then 21 else if f.val = 36 then 21 else 0
                  else
                    if index < 322 then
                      if index < 321 then
                        fun f => if f.val = 29 then 5 else if f.val = 36 then 19 else if f.val = 38 then 20 else 0
                      else
                        fun f => if f.val = 21 then 21 else if f.val = 29 then 15 else if f.val = 31 then 20 else if f.val = 33 then 21 else 0
                    else
                      if index < 323 then
                        fun f => if f.val = 21 then 19 else if f.val = 29 then 7 else if f.val = 40 then 20 else 0
                      else
                        fun f => if f.val = 21 then 20 else if f.val = 29 then 8 else if f.val = 36 then 20 else 0
                else
                  if index < 328 then
                    if index < 326 then
                      if index < 325 then
                        fun f => if f.val = 28 then 19 else if f.val = 29 then 21 else if f.val = 38 then 24 else if f.val = 39 then 21 else 0
                      else
                        fun f => if f.val = 28 then 24 else if f.val = 29 then 19 else if f.val = 40 then 24 else if f.val = 41 then 21 else 0
                    else
                      if index < 327 then
                        fun f => if f.val = 28 then 21 else if f.val = 29 then 20 else if f.val = 35 then 21 else if f.val = 36 then 24 else 0
                      else
                        fun f => if f.val = 21 then 24 else if f.val = 27 then 21 else if f.val = 28 then 20 else if f.val = 29 then 24 else 0
                  else
                    if index < 330 then
                      if index < 329 then
                        fun f => if f.val = 45 then 20 else if f.val = 59 then 7 else if f.val = 60 then 12 else 0
                      else
                        fun f => if f.val = 54 then 20 else if f.val = 62 then 12 else if f.val = 64 then 21 else 0
                    else
                      if index < 331 then
                        fun f => if f.val = 59 then 15 else if f.val = 60 then 10 else if f.val = 62 then 10 else if f.val = 64 then 19 else 0
                      else
                        if index < 332 then
                          fun f => if f.val = 45 then 21 else if f.val = 54 then 21 else if f.val = 60 then 4 else if f.val = 62 then 4 else 0
                        else
                          fun f => if f.val = 44 then 24 else if f.val = 56 then 12 else if f.val = 58 then 12 else 0
          else
            if index < 366 then
              if index < 349 then
                if index < 341 then
                  if index < 337 then
                    if index < 335 then
                      if index < 334 then
                        fun f => if f.val = 56 then 10 else if f.val = 58 then 10 else if f.val = 59 then 24 else if f.val = 60 then 11 else 0
                      else
                        fun f => if f.val = 44 then 7 else if f.val = 45 then 8 else if f.val = 56 then 4 else if f.val = 59 then 19 else 0
                    else
                      if index < 336 then
                        fun f => if f.val = 44 then 19 else if f.val = 45 then 24 else if f.val = 58 then 4 else if f.val = 60 then 5 else 0
                      else
                        fun f => if f.val = 43 then 12 else if f.val = 46 then 7 else if f.val = 55 then 20 else 0
                  else
                    if index < 339 then
                      if index < 338 then
                        fun f => if f.val = 43 then 10 else if f.val = 46 then 15 else if f.val = 62 then 11 else if f.val = 64 then 20 else 0
                      else
                        fun f => if f.val = 43 then 4 else if f.val = 54 then 24 else if f.val = 55 then 21 else if f.val = 62 then 5 else 0
                    else
                      if index < 340 then
                        fun f => if f.val = 43 then 11 else if f.val = 46 then 24 else if f.val = 56 then 11 else if f.val = 58 then 11 else 0
                      else
                        fun f => if f.val = 44 then 8 else if f.val = 46 then 19 else if f.val = 55 then 8 else if f.val = 56 then 5 else 0
                else
                  if index < 345 then
                    if index < 343 then
                      if index < 342 then
                        fun f => if f.val = 43 then 5 else if f.val = 44 then 20 else if f.val = 55 then 24 else if f.val = 58 then 5 else 0
                      else
                        fun f => if f.val = 59 then 8 else if f.val = 60 then 15 else if f.val = 61 then 20 else 0
                    else
                      if index < 344 then
                        fun f => if f.val = 62 then 15 else if f.val = 63 then 20 else if f.val = 64 then 24 else 0
                      else
                        fun f => if f.val = 60 then 7 else if f.val = 61 then 21 else if f.val = 62 then 7 else if f.val = 63 then 21 else 0
                  else
                    if index < 347 then
                      if index < 346 then
                        fun f => if f.val = 56 then 15 else if f.val = 57 then 24 else if f.val = 58 then 15 else 0
                      else
                        fun f => if f.val = 56 then 7 else if f.val = 57 then 7 else if f.val = 59 then 20 else if f.val = 61 then 8 else 0
                    else
                      if index < 348 then
                        fun f => if f.val = 57 then 19 else if f.val = 58 then 7 else if f.val = 60 then 8 else if f.val = 61 then 24 else 0
                      else
                        fun f => if f.val = 43 then 15 else if f.val = 46 then 8 else if f.val = 49 then 20 else 0
              else
                if index < 357 then
                  if index < 353 then
                    if index < 351 then
                      if index < 350 then
                        fun f => if f.val = 43 then 7 else if f.val = 49 then 21 else if f.val = 62 then 8 else if f.val = 63 then 24 else 0
                      else
                        fun f => if f.val = 46 then 20 else if f.val = 49 then 8 else if f.val = 56 then 8 else if f.val = 57 then 8 else 0
                    else
                      if index < 352 then
                        fun f => if f.val = 43 then 8 else if f.val = 49 then 24 else if f.val = 57 then 20 else if f.val = 58 then 8 else 0
                      else
                        fun f => if f.val = 44 then 15 else if f.val = 48 then 21 else if f.val = 56 then 21 else 0
                  else
                    if index < 355 then
                      if index < 354 then
                        fun f => if f.val = 47 then 20 else if f.val = 48 then 19 else if f.val = 56 then 19 else if f.val = 59 then 21 else 0
                      else
                        fun f => if f.val = 46 then 21 else if f.val = 48 then 20 else if f.val = 52 then 20 else if f.val = 56 then 20 else 0
                    else
                      if index < 356 then
                        fun f => if f.val = 48 then 24 else if f.val = 56 then 24 else if f.val = 57 then 15 else 0
                      else
                        fun f => if f.val = 45 then 19 else if f.val = 51 then 12 else if f.val = 53 then 19 else if f.val = 60 then 21 else 0
                else
                  if index < 361 then
                    if index < 359 then
                      if index < 358 then
                        fun f => if f.val = 51 then 10 else if f.val = 53 then 21 else if f.val = 54 then 19 else if f.val = 62 then 21 else 0
                      else
                        fun f => if f.val = 51 then 4 else if f.val = 60 then 19 else if f.val = 62 then 19 else 0
                    else
                      if index < 360 then
                        fun f => if f.val = 44 then 21 else if f.val = 51 then 11 else if f.val = 53 then 24 else if f.val = 58 then 21 else 0
                      else
                        fun f => if f.val = 51 then 5 else if f.val = 58 then 19 else if f.val = 60 then 20 else 0
                  else
                    if index < 363 then
                      if index < 362 then
                        fun f => if f.val = 43 then 21 else if f.val = 51 then 15 else if f.val = 53 then 20 else if f.val = 55 then 19 else 0
                      else
                        fun f => if f.val = 43 then 19 else if f.val = 51 then 7 else if f.val = 62 then 20 else 0
                    else
                      if index < 364 then
                        fun f => if f.val = 43 then 20 else if f.val = 51 then 8 else if f.val = 58 then 20 else 0
                      else
                        if index < 365 then
                          fun f => if f.val = 50 then 19 else if f.val = 51 then 21 else if f.val = 60 then 24 else if f.val = 61 then 19 else 0
                        else
                          fun f => if f.val = 50 then 21 else if f.val = 51 then 19 else if f.val = 62 then 24 else if f.val = 63 then 19 else 0
            else
              if index < 383 then
                if index < 374 then
                  if index < 370 then
                    if index < 368 then
                      if index < 367 then
                        fun f => if f.val = 50 then 24 else if f.val = 51 then 20 else if f.val = 57 then 21 else if f.val = 58 then 24 else 0
                      else
                        fun f => if f.val = 43 then 24 else if f.val = 49 then 19 else if f.val = 50 then 20 else if f.val = 51 then 24 else 0
                    else
                      if index < 369 then
                        fun f => if f.val = 76 then 12 else if f.val = 83 then 12 else if f.val = 85 then 12 else 0
                      else
                        fun f => if f.val = 80 then 19 else if f.val = 81 then 15 else if f.val = 83 then 10 else if f.val = 85 then 10 else 0
                  else
                    if index < 372 then
                      if index < 371 then
                        fun f => if f.val = 67 then 15 else if f.val = 76 then 10 else if f.val = 80 then 21 else if f.val = 85 then 4 else 0
                      else
                        fun f => if f.val = 67 then 7 else if f.val = 76 then 4 else if f.val = 81 then 7 else if f.val = 83 then 4 else 0
                    else
                      if index < 373 then
                        fun f => if f.val = 65 then 15 else if f.val = 68 then 19 else if f.val = 83 then 11 else if f.val = 85 then 11 else 0
                      else
                        fun f => if f.val = 68 then 21 else if f.val = 76 then 11 else if f.val = 77 then 15 else if f.val = 85 then 5 else 0
                else
                  if index < 378 then
                    if index < 376 then
                      if index < 375 then
                        fun f => if f.val = 65 then 7 else if f.val = 76 then 5 else if f.val = 77 then 7 else if f.val = 83 then 5 else 0
                      else
                        fun f => if f.val = 83 then 15 else if f.val = 84 then 12 else if f.val = 85 then 15 else 0
                    else
                      if index < 377 then
                        fun f => if f.val = 80 then 24 else if f.val = 82 then 15 else if f.val = 84 then 10 else if f.val = 85 then 7 else 0
                      else
                        fun f => if f.val = 81 then 8 else if f.val = 82 then 7 else if f.val = 83 then 7 else if f.val = 84 then 4 else 0
                  else
                    if index < 380 then
                      if index < 379 then
                        fun f => if f.val = 68 then 24 else if f.val = 71 then 15 else if f.val = 84 then 11 else if f.val = 85 then 8 else 0
                      else
                        fun f => if f.val = 65 then 8 else if f.val = 71 then 7 else if f.val = 83 then 8 else if f.val = 84 then 5 else 0
                    else
                      if index < 381 then
                        fun f => if f.val = 76 then 15 else if f.val = 85 then 21 else if f.val = 87 then 12 else if f.val = 91 then 12 else if f.val = 96 then 12 else 0
                      else
                        if index < 382 then
                          fun f => if f.val = 69 then 15 else if f.val = 80 then 20 else if f.val = 85 then 19 else if f.val = 90 then 12 else if f.val = 91 then 10 else 0
                        else
                          fun f => if f.val = 67 then 8 else if f.val = 69 then 7 else if f.val = 76 then 7 else if f.val = 88 then 12 else if f.val = 90 then 10 else if f.val = 96 then 10 else 0
              else
                if index < 391 then
                  if index < 387 then
                    if index < 385 then
                      if index < 384 then
                        fun f => if f.val = 87 then 10 else if f.val = 88 then 10 else if f.val = 90 then 4 else if f.val = 91 then 4 else 0
                      else
                        fun f => if f.val = 87 then 4 else if f.val = 88 then 4 else if f.val = 96 then 4 else 0
                    else
                      if index < 386 then
                        fun f => if f.val = 68 then 20 else if f.val = 74 then 15 else if f.val = 85 then 20 else if f.val = 91 then 11 else if f.val = 95 then 12 else 0
                      else
                        fun f => if f.val = 74 then 7 else if f.val = 76 then 8 else if f.val = 77 then 8 else if f.val = 95 then 10 else if f.val = 96 then 11 else if f.val = 98 then 12 else 0
                  else
                    if index < 389 then
                      if index < 388 then
                        fun f => if f.val = 87 then 11 else if f.val = 91 then 5 else if f.val = 95 then 4 else if f.val = 98 then 10 else 0
                      else
                        fun f => if f.val = 87 then 5 else if f.val = 96 then 5 else if f.val = 98 then 4 else 0
                    else
                      if index < 390 then
                        fun f => if f.val = 84 then 15 else if f.val = 85 then 24 else if f.val = 91 then 15 else if f.val = 93 then 12 else if f.val = 100 then 12 else 0
                      else
                        fun f => if f.val = 69 then 8 else if f.val = 82 then 8 else if f.val = 84 then 7 else if f.val = 90 then 11 else if f.val = 93 then 10 else if f.val = 104 then 12 else 0
                else
                  if index < 395 then
                    if index < 393 then
                      if index < 392 then
                        fun f => if f.val = 90 then 5 else if f.val = 91 then 7 else if f.val = 100 then 10 else if f.val = 104 then 10 else 0
                      else
                        fun f => if f.val = 93 then 4 else if f.val = 100 then 4 else if f.val = 104 then 4 else 0
                    else
                      if index < 394 then
                        fun f => if f.val = 71 then 8 else if f.val = 74 then 8 else if f.val = 84 then 8 else if f.val = 92 then 12 else if f.val = 93 then 11 else if f.val = 95 then 11 else 0
                      else
                        fun f => if f.val = 91 then 8 else if f.val = 92 then 10 else if f.val = 95 then 5 else if f.val = 100 then 11 else 0
                  else
                    if index < 397 then
                      if index < 396 then
                        fun f => if f.val = 92 then 4 else if f.val = 93 then 5 else if f.val = 100 then 5 else 0
                      else
                        fun f => if f.val = 67 then 19 else if f.val = 73 then 12 else if f.val = 75 then 12 else if f.val = 81 then 19 else 0
                    else
                      if index < 398 then
                        fun f => if f.val = 73 then 10 else if f.val = 75 then 10 else if f.val = 76 then 21 else if f.val = 83 then 21 else 0
                      else
                        if index < 399 then
                          fun f => if f.val = 73 then 4 else if f.val = 81 then 24 else if f.val = 83 then 19 else 0
                        else
                          fun f => if f.val = 67 then 24 else if f.val = 75 then 4 else if f.val = 76 then 19 else 0
        else
          if index < 467 then
            if index < 433 then
              if index < 416 then
                if index < 408 then
                  if index < 404 then
                    if index < 402 then
                      if index < 401 then
                        fun f => if f.val = 66 then 19 else if f.val = 73 then 11 else if f.val = 75 then 11 else if f.val = 79 then 21 else 0
                      else
                        fun f => if f.val = 73 then 5 else if f.val = 79 then 19 else if f.val = 81 then 21 else 0
                    else
                      if index < 403 then
                        fun f => if f.val = 66 then 21 else if f.val = 67 then 21 else if f.val = 75 then 5 else 0
                      else
                        fun f => if f.val = 65 then 19 else if f.val = 73 then 15 else if f.val = 75 then 15 else if f.val = 77 then 19 else 0
                  else
                    if index < 406 then
                      if index < 405 then
                        fun f => if f.val = 65 then 24 else if f.val = 73 then 7 else if f.val = 83 then 20 else 0
                      else
                        fun f => if f.val = 75 then 7 else if f.val = 76 then 20 else if f.val = 77 then 24 else 0
                    else
                      if index < 407 then
                        fun f => if f.val = 65 then 21 else if f.val = 73 then 8 else if f.val = 79 then 20 else 0
                      else
                        fun f => if f.val = 66 then 24 else if f.val = 75 then 8 else if f.val = 77 then 21 else 0
                else
                  if index < 412 then
                    if index < 410 then
                      if index < 409 then
                        fun f => if f.val = 72 then 12 else if f.val = 73 then 21 else if f.val = 81 then 20 else if f.val = 82 then 19 else 0
                      else
                        fun f => if f.val = 72 then 10 else if f.val = 73 then 19 else if f.val = 83 then 24 else if f.val = 84 then 21 else 0
                    else
                      if index < 411 then
                        fun f => if f.val = 72 then 4 else if f.val = 82 then 24 else if f.val = 84 then 19 else 0
                      else
                        fun f => if f.val = 72 then 11 else if f.val = 73 then 20 else if f.val = 78 then 19 else if f.val = 79 then 24 else 0
                  else
                    if index < 414 then
                      if index < 413 then
                        fun f => if f.val = 72 then 5 else if f.val = 78 then 21 else if f.val = 82 then 21 else 0
                      else
                        fun f => if f.val = 65 then 20 else if f.val = 71 then 19 else if f.val = 72 then 15 else if f.val = 73 then 24 else 0
                    else
                      if index < 415 then
                        fun f => if f.val = 71 then 24 else if f.val = 72 then 7 else if f.val = 84 then 20 else 0
                      else
                        fun f => if f.val = 71 then 21 else if f.val = 72 then 8 else if f.val = 78 then 24 else 0
              else
                if index < 424 then
                  if index < 420 then
                    if index < 418 then
                      if index < 417 then
                        fun f => if f.val = 67 then 20 else if f.val = 69 then 19 else if f.val = 75 then 21 else if f.val = 110 then 12 else if f.val = 112 then 12 else if f.val = 119 then 12 else 0
                      else
                        fun f => if f.val = 75 then 19 else if f.val = 76 then 24 else if f.val = 96 then 15 else if f.val = 97 then 12 else if f.val = 118 then 12 else if f.val = 119 then 10 else 0
                    else
                      if index < 419 then
                        fun f => if f.val = 69 then 24 else if f.val = 90 then 15 else if f.val = 112 then 10 else 0
                      else
                        fun f => if f.val = 88 then 11 else if f.val = 90 then 7 else if f.val = 97 then 10 else if f.val = 110 then 10 else if f.val = 112 then 4 else if f.val = 118 then 10 else 0
                  else
                    if index < 422 then
                      if index < 421 then
                        fun f => if f.val = 88 then 5 else if f.val = 96 then 7 else if f.val = 97 then 4 else 0
                      else
                        fun f => if f.val = 110 then 4 else if f.val = 118 then 4 else if f.val = 119 then 4 else 0
                    else
                      if index < 423 then
                        fun f => if f.val = 66 then 20 else if f.val = 70 then 21 else if f.val = 75 then 20 else if f.val = 119 then 11 else if f.val = 129 then 12 else 0
                      else
                        fun f => if f.val = 69 then 21 else if f.val = 70 then 19 else if f.val = 112 then 11 else if f.val = 124 then 12 else if f.val = 129 then 10 else 0
                else
                  if index < 428 then
                    if index < 426 then
                      if index < 425 then
                        fun f => if f.val = 110 then 5 else if f.val = 119 then 5 else if f.val = 124 then 10 else if f.val = 129 then 4 else 0
                      else
                        fun f => if f.val = 110 then 11 else if f.val = 112 then 5 else if f.val = 124 then 4 else 0
                    else
                      if index < 427 then
                        fun f => if f.val = 74 then 19 else if f.val = 75 then 24 else if f.val = 77 then 20 else if f.val = 117 then 12 else if f.val = 119 then 15 else if f.val = 120 then 12 else 0
                      else
                        fun f => if f.val = 74 then 24 else if f.val = 95 then 15 else if f.val = 117 then 10 else 0
                  else
                    if index < 430 then
                      if index < 429 then
                        fun f => if f.val = 95 then 7 else if f.val = 97 then 11 else if f.val = 98 then 11 else if f.val = 117 then 4 else if f.val = 118 then 11 else if f.val = 120 then 10 else 0
                      else
                        fun f => if f.val = 96 then 8 else if f.val = 97 then 5 else if f.val = 98 then 5 else 0
                    else
                      if index < 431 then
                        fun f => if f.val = 118 then 5 else if f.val = 119 then 7 else if f.val = 120 then 4 else 0
                      else
                        if index < 432 then
                          fun f => if f.val = 70 then 20 else if f.val = 74 then 21 else if f.val = 111 then 12 else if f.val = 117 then 11 else if f.val = 129 then 11 else 0
                        else
                          fun f => if f.val = 111 then 10 else if f.val = 119 then 8 else if f.val = 120 then 5 else if f.val = 129 then 5 else 0
            else
              if index < 450 then
                if index < 441 then
                  if index < 437 then
                    if index < 435 then
                      if index < 434 then
                        fun f => if f.val = 111 then 4 else if f.val = 117 then 5 else if f.val = 120 then 11 else 0
                      else
                        fun f => if f.val = 69 then 20 else if f.val = 72 then 21 else if f.val = 82 then 20 else if f.val = 112 then 15 else if f.val = 126 then 12 else if f.val = 128 then 12 else 0
                    else
                      if index < 436 then
                        fun f => if f.val = 72 then 19 else if f.val = 84 then 24 else if f.val = 93 then 15 else if f.val = 106 then 12 else if f.val = 115 then 12 else if f.val = 128 then 10 else 0
                      else
                        fun f => if f.val = 90 then 8 else if f.val = 104 then 11 else if f.val = 106 then 10 else if f.val = 112 then 7 else if f.val = 115 then 10 else if f.val = 126 then 10 else 0
                  else
                    if index < 439 then
                      if index < 438 then
                        fun f => if f.val = 93 then 7 else if f.val = 104 then 5 else if f.val = 106 then 4 else 0
                      else
                        fun f => if f.val = 115 then 4 else if f.val = 126 then 4 else if f.val = 128 then 4 else 0
                    else
                      if index < 440 then
                        fun f => if f.val = 70 then 24 else if f.val = 72 then 20 else if f.val = 78 then 20 else if f.val = 128 then 11 else if f.val = 129 then 15 else 0
                      else
                        fun f => if f.val = 124 then 11 else if f.val = 126 then 5 else if f.val = 128 then 5 else if f.val = 129 then 7 else 0
                else
                  if index < 445 then
                    if index < 443 then
                      if index < 442 then
                        fun f => if f.val = 112 then 8 else if f.val = 124 then 5 else if f.val = 126 then 11 else 0
                      else
                        fun f => if f.val = 71 then 20 else if f.val = 72 then 24 else if f.val = 74 then 20 else if f.val = 114 then 12 else if f.val = 117 then 15 else if f.val = 128 then 15 else 0
                    else
                      if index < 444 then
                        fun f => if f.val = 92 then 11 else if f.val = 95 then 8 else if f.val = 106 then 11 else if f.val = 114 then 10 else if f.val = 115 then 11 else if f.val = 117 then 7 else 0
                      else
                        fun f => if f.val = 92 then 5 else if f.val = 93 then 8 else if f.val = 106 then 5 else 0
                  else
                    if index < 447 then
                      if index < 446 then
                        fun f => if f.val = 114 then 4 else if f.val = 115 then 5 else if f.val = 128 then 7 else 0
                      else
                        fun f => if f.val = 111 then 11 else if f.val = 114 then 5 else if f.val = 128 then 8 else if f.val = 129 then 8 else 0
                    else
                      if index < 448 then
                        fun f => if f.val = 111 then 5 else if f.val = 114 then 11 else if f.val = 117 then 8 else 0
                      else
                        if index < 449 then
                          fun f => if f.val = 88 then 24 else if f.val = 102 then 12 else if f.val = 103 then 12 else 0
                        else
                          fun f => if f.val = 97 then 24 else if f.val = 105 then 12 else if f.val = 107 then 12 else 0
              else
                if index < 458 then
                  if index < 454 then
                    if index < 452 then
                      if index < 451 then
                        fun f => if f.val = 102 then 10 else if f.val = 103 then 10 else if f.val = 105 then 10 else if f.val = 107 then 10 else 0
                      else
                        fun f => if f.val = 88 then 8 else if f.val = 97 then 7 else if f.val = 102 then 4 else if f.val = 107 then 4 else 0
                    else
                      if index < 453 then
                        fun f => if f.val = 88 then 20 else if f.val = 97 then 19 else if f.val = 103 then 4 else if f.val = 105 then 4 else 0
                      else
                        fun f => if f.val = 87 then 24 else if f.val = 99 then 12 else if f.val = 101 then 12 else 0
                  else
                    if index < 456 then
                      if index < 455 then
                        fun f => if f.val = 99 then 10 else if f.val = 101 then 10 else if f.val = 102 then 11 else if f.val = 103 then 11 else 0
                      else
                        fun f => if f.val = 87 then 7 else if f.val = 88 then 7 else if f.val = 99 then 4 else if f.val = 102 then 5 else 0
                    else
                      if index < 457 then
                        fun f => if f.val = 87 then 19 else if f.val = 88 then 19 else if f.val = 101 then 4 else if f.val = 103 then 5 else 0
                      else
                        fun f => if f.val = 86 then 12 else if f.val = 89 then 12 else if f.val = 98 then 24 else 0
                else
                  if index < 462 then
                    if index < 460 then
                      if index < 459 then
                        fun f => if f.val = 86 then 10 else if f.val = 89 then 10 else if f.val = 105 then 11 else if f.val = 107 then 11 else 0
                      else
                        fun f => if f.val = 89 then 4 else if f.val = 97 then 8 else if f.val = 98 then 8 else if f.val = 107 then 5 else 0
                    else
                      if index < 461 then
                        fun f => if f.val = 86 then 4 else if f.val = 97 then 20 else if f.val = 98 then 20 else if f.val = 105 then 5 else 0
                      else
                        fun f => if f.val = 86 then 11 else if f.val = 89 then 11 else if f.val = 99 then 11 else if f.val = 101 then 11 else 0
                  else
                    if index < 464 then
                      if index < 463 then
                        fun f => if f.val = 87 then 8 else if f.val = 89 then 5 else if f.val = 98 then 7 else if f.val = 99 then 5 else 0
                      else
                        fun f => if f.val = 86 then 5 else if f.val = 87 then 20 else if f.val = 98 then 19 else if f.val = 101 then 5 else 0
                    else
                      if index < 465 then
                        fun f => if f.val = 102 then 15 else if f.val = 103 then 15 else if f.val = 104 then 24 else 0
                      else
                        if index < 466 then
                          fun f => if f.val = 105 then 15 else if f.val = 106 then 24 else if f.val = 107 then 15 else 0
                        else
                          fun f => if f.val = 102 then 7 else if f.val = 104 then 8 else if f.val = 106 then 7 else if f.val = 107 then 7 else 0
          else
            if index < 500 then
              if index < 483 then
                if index < 475 then
                  if index < 471 then
                    if index < 469 then
                      if index < 468 then
                        fun f => if f.val = 103 then 7 else if f.val = 104 then 20 else if f.val = 105 then 7 else if f.val = 106 then 19 else 0
                      else
                        fun f => if f.val = 99 then 15 else if f.val = 100 then 24 else if f.val = 101 then 15 else 0
                    else
                      if index < 470 then
                        fun f => if f.val = 99 then 7 else if f.val = 100 then 7 else if f.val = 102 then 8 else if f.val = 104 then 7 else 0
                      else
                        fun f => if f.val = 100 then 19 else if f.val = 101 then 7 else if f.val = 103 then 8 else if f.val = 104 then 19 else 0
                  else
                    if index < 473 then
                      if index < 472 then
                        fun f => if f.val = 86 then 15 else if f.val = 89 then 15 else if f.val = 92 then 24 else 0
                      else
                        fun f => if f.val = 89 then 7 else if f.val = 92 then 8 else if f.val = 106 then 8 else if f.val = 107 then 8 else 0
                    else
                      if index < 474 then
                        fun f => if f.val = 86 then 7 else if f.val = 92 then 20 else if f.val = 105 then 8 else if f.val = 106 then 20 else 0
                      else
                        fun f => if f.val = 89 then 8 else if f.val = 92 then 7 else if f.val = 99 then 8 else if f.val = 100 then 8 else 0
                else
                  if index < 479 then
                    if index < 477 then
                      if index < 476 then
                        fun f => if f.val = 86 then 8 else if f.val = 92 then 19 else if f.val = 100 then 20 else if f.val = 101 then 8 else 0
                      else
                        fun f => if f.val = 88 then 15 else if f.val = 90 then 19 else if f.val = 102 then 21 else 0
                    else
                      if index < 478 then
                        fun f => if f.val = 97 then 15 else if f.val = 107 then 21 else if f.val = 109 then 12 else if f.val = 113 then 12 else if f.val = 118 then 15 else 0
                      else
                        fun f => if f.val = 90 then 24 else if f.val = 102 then 19 else if f.val = 107 then 19 else if f.val = 112 then 19 else if f.val = 113 then 10 else 0
                  else
                    if index < 481 then
                      if index < 480 then
                        fun f => if f.val = 109 then 10 else if f.val = 110 then 15 else if f.val = 112 then 21 else if f.val = 113 then 4 else 0
                      else
                        fun f => if f.val = 109 then 4 else if f.val = 110 then 7 else if f.val = 118 then 7 else 0
                    else
                      if index < 482 then
                        fun f => if f.val = 87 then 15 else if f.val = 91 then 21 else if f.val = 99 then 21 else 0
                      else
                        fun f => if f.val = 90 then 21 else if f.val = 91 then 19 else if f.val = 99 then 19 else if f.val = 102 then 20 else 0
              else
                if index < 491 then
                  if index < 487 then
                    if index < 485 then
                      if index < 484 then
                        fun f => if f.val = 89 then 21 else if f.val = 95 then 19 else if f.val = 98 then 15 else 0
                      else
                        fun f => if f.val = 89 then 19 else if f.val = 95 then 24 else if f.val = 107 then 20 else if f.val = 113 then 11 else if f.val = 117 then 19 else 0
                    else
                      if index < 486 then
                        fun f => if f.val = 109 then 11 else if f.val = 113 then 5 else if f.val = 117 then 21 else if f.val = 120 then 15 else 0
                      else
                        fun f => if f.val = 109 then 5 else if f.val = 118 then 8 else if f.val = 120 then 7 else 0
                  else
                    if index < 489 then
                      if index < 488 then
                        fun f => if f.val = 89 then 20 else if f.val = 91 then 20 else if f.val = 95 then 21 else if f.val = 99 then 20 else 0
                      else
                        fun f => if f.val = 90 then 20 else if f.val = 102 then 24 else if f.val = 104 then 15 else 0
                    else
                      if index < 490 then
                        fun f => if f.val = 106 then 15 else if f.val = 107 then 24 else if f.val = 113 then 15 else if f.val = 115 then 15 else if f.val = 122 then 12 else 0
                      else
                        fun f => if f.val = 112 then 24 else if f.val = 113 then 7 else if f.val = 122 then 10 else if f.val = 126 then 15 else 0
                else
                  if index < 495 then
                    if index < 493 then
                      if index < 492 then
                        fun f => if f.val = 115 then 7 else if f.val = 122 then 4 else if f.val = 126 then 7 else 0
                      else
                        fun f => if f.val = 91 then 24 else if f.val = 99 then 24 else if f.val = 100 then 15 else 0
                    else
                      if index < 494 then
                        fun f => if f.val = 89 then 24 else if f.val = 92 then 15 else if f.val = 95 then 20 else 0
                      else
                        fun f => if f.val = 113 then 8 else if f.val = 114 then 15 else if f.val = 117 then 24 else if f.val = 122 then 11 else 0
                  else
                    if index < 497 then
                      if index < 496 then
                        fun f => if f.val = 114 then 7 else if f.val = 115 then 8 else if f.val = 122 then 5 else 0
                      else
                        fun f => if f.val = 88 then 21 else if f.val = 94 then 12 else if f.val = 96 then 19 else if f.val = 103 then 21 else 0
                    else
                      if index < 498 then
                        fun f => if f.val = 94 then 10 else if f.val = 96 then 24 else if f.val = 97 then 21 else if f.val = 105 then 21 else 0
                      else
                        if index < 499 then
                          fun f => if f.val = 94 then 4 else if f.val = 103 then 19 else if f.val = 105 then 19 else 0
                        else
                          fun f => if f.val = 87 then 21 else if f.val = 94 then 11 else if f.val = 96 then 21 else if f.val = 101 then 21 else 0
            else
              if index < 517 then
                if index < 508 then
                  if index < 504 then
                    if index < 502 then
                      if index < 501 then
                        fun f => if f.val = 94 then 5 else if f.val = 101 then 19 else if f.val = 103 then 20 else 0
                      else
                        fun f => if f.val = 86 then 21 else if f.val = 94 then 15 else if f.val = 96 then 20 else if f.val = 98 then 21 else 0
                    else
                      if index < 503 then
                        fun f => if f.val = 86 then 19 else if f.val = 94 then 7 else if f.val = 105 then 20 else 0
                      else
                        fun f => if f.val = 86 then 20 else if f.val = 94 then 8 else if f.val = 101 then 20 else 0
                  else
                    if index < 506 then
                      if index < 505 then
                        fun f => if f.val = 93 then 19 else if f.val = 94 then 21 else if f.val = 103 then 24 else if f.val = 104 then 21 else 0
                      else
                        fun f => if f.val = 93 then 24 else if f.val = 94 then 19 else if f.val = 105 then 24 else if f.val = 106 then 21 else 0
                    else
                      if index < 507 then
                        fun f => if f.val = 93 then 21 else if f.val = 94 then 20 else if f.val = 100 then 21 else if f.val = 101 then 24 else 0
                      else
                        fun f => if f.val = 86 then 24 else if f.val = 92 then 21 else if f.val = 93 then 20 else if f.val = 94 then 24 else 0
                else
                  if index < 512 then
                    if index < 510 then
                      if index < 509 then
                        fun f => if f.val = 110 then 20 else if f.val = 124 then 7 else if f.val = 125 then 12 else 0
                      else
                        fun f => if f.val = 119 then 20 else if f.val = 127 then 12 else if f.val = 129 then 21 else 0
                    else
                      if index < 511 then
                        fun f => if f.val = 124 then 15 else if f.val = 125 then 10 else if f.val = 127 then 10 else if f.val = 129 then 19 else 0
                      else
                        fun f => if f.val = 110 then 21 else if f.val = 119 then 21 else if f.val = 125 then 4 else if f.val = 127 then 4 else 0
                  else
                    if index < 514 then
                      if index < 513 then
                        fun f => if f.val = 109 then 24 else if f.val = 121 then 12 else if f.val = 123 then 12 else 0
                      else
                        fun f => if f.val = 121 then 10 else if f.val = 123 then 10 else if f.val = 124 then 24 else if f.val = 125 then 11 else 0
                    else
                      if index < 515 then
                        fun f => if f.val = 109 then 7 else if f.val = 110 then 8 else if f.val = 121 then 4 else if f.val = 124 then 19 else 0
                      else
                        if index < 516 then
                          fun f => if f.val = 109 then 19 else if f.val = 110 then 24 else if f.val = 123 then 4 else if f.val = 125 then 5 else 0
                        else
                          fun f => if f.val = 108 then 12 else if f.val = 111 then 7 else if f.val = 120 then 20 else 0
              else
                if index < 525 then
                  if index < 521 then
                    if index < 519 then
                      if index < 518 then
                        fun f => if f.val = 108 then 10 else if f.val = 111 then 15 else if f.val = 127 then 11 else if f.val = 129 then 20 else 0
                      else
                        fun f => if f.val = 108 then 4 else if f.val = 119 then 24 else if f.val = 120 then 21 else if f.val = 127 then 5 else 0
                    else
                      if index < 520 then
                        fun f => if f.val = 108 then 11 else if f.val = 111 then 24 else if f.val = 121 then 11 else if f.val = 123 then 11 else 0
                      else
                        fun f => if f.val = 109 then 8 else if f.val = 111 then 19 else if f.val = 120 then 8 else if f.val = 121 then 5 else 0
                  else
                    if index < 523 then
                      if index < 522 then
                        fun f => if f.val = 108 then 5 else if f.val = 109 then 20 else if f.val = 120 then 24 else if f.val = 123 then 5 else 0
                      else
                        fun f => if f.val = 124 then 8 else if f.val = 125 then 15 else if f.val = 126 then 20 else 0
                    else
                      if index < 524 then
                        fun f => if f.val = 127 then 15 else if f.val = 128 then 20 else if f.val = 129 then 24 else 0
                      else
                        fun f => if f.val = 125 then 7 else if f.val = 126 then 21 else if f.val = 127 then 7 else if f.val = 128 then 21 else 0
                else
                  if index < 529 then
                    if index < 527 then
                      if index < 526 then
                        fun f => if f.val = 121 then 15 else if f.val = 122 then 24 else if f.val = 123 then 15 else 0
                      else
                        fun f => if f.val = 121 then 7 else if f.val = 122 then 7 else if f.val = 124 then 20 else if f.val = 126 then 8 else 0
                    else
                      if index < 528 then
                        fun f => if f.val = 122 then 19 else if f.val = 123 then 7 else if f.val = 125 then 8 else if f.val = 126 then 24 else 0
                      else
                        fun f => if f.val = 108 then 15 else if f.val = 111 then 8 else if f.val = 114 then 20 else 0
                  else
                    if index < 531 then
                      if index < 530 then
                        fun f => if f.val = 108 then 7 else if f.val = 114 then 21 else if f.val = 127 then 8 else if f.val = 128 then 24 else 0
                      else
                        fun f => if f.val = 111 then 20 else if f.val = 114 then 8 else if f.val = 121 then 8 else if f.val = 122 then 8 else 0
                    else
                      if index < 532 then
                        fun f => if f.val = 108 then 8 else if f.val = 114 then 24 else if f.val = 122 then 20 else if f.val = 123 then 8 else 0
                      else
                        if index < 533 then
                          fun f => if f.val = 109 then 15 else if f.val = 113 then 21 else if f.val = 121 then 21 else 0
                        else
                          fun f => if f.val = 112 then 20 else if f.val = 113 then 19 else if f.val = 121 then 19 else if f.val = 124 then 21 else 0
    else
      if index < 801 then
        if index < 667 then
          if index < 600 then
            if index < 567 then
              if index < 550 then
                if index < 542 then
                  if index < 538 then
                    if index < 536 then
                      if index < 535 then
                        fun f => if f.val = 111 then 21 else if f.val = 113 then 20 else if f.val = 117 then 20 else if f.val = 121 then 20 else 0
                      else
                        fun f => if f.val = 113 then 24 else if f.val = 121 then 24 else if f.val = 122 then 15 else 0
                    else
                      if index < 537 then
                        fun f => if f.val = 110 then 19 else if f.val = 116 then 12 else if f.val = 118 then 19 else if f.val = 125 then 21 else 0
                      else
                        fun f => if f.val = 116 then 10 else if f.val = 118 then 21 else if f.val = 119 then 19 else if f.val = 127 then 21 else 0
                  else
                    if index < 540 then
                      if index < 539 then
                        fun f => if f.val = 116 then 4 else if f.val = 125 then 19 else if f.val = 127 then 19 else 0
                      else
                        fun f => if f.val = 109 then 21 else if f.val = 116 then 11 else if f.val = 118 then 24 else if f.val = 123 then 21 else 0
                    else
                      if index < 541 then
                        fun f => if f.val = 116 then 5 else if f.val = 123 then 19 else if f.val = 125 then 20 else 0
                      else
                        fun f => if f.val = 108 then 21 else if f.val = 116 then 15 else if f.val = 118 then 20 else if f.val = 120 then 19 else 0
                else
                  if index < 546 then
                    if index < 544 then
                      if index < 543 then
                        fun f => if f.val = 108 then 19 else if f.val = 116 then 7 else if f.val = 127 then 20 else 0
                      else
                        fun f => if f.val = 108 then 20 else if f.val = 116 then 8 else if f.val = 123 then 20 else 0
                    else
                      if index < 545 then
                        fun f => if f.val = 115 then 19 else if f.val = 116 then 21 else if f.val = 125 then 24 else if f.val = 126 then 19 else 0
                      else
                        fun f => if f.val = 115 then 21 else if f.val = 116 then 19 else if f.val = 127 then 24 else if f.val = 128 then 19 else 0
                  else
                    if index < 548 then
                      if index < 547 then
                        fun f => if f.val = 115 then 24 else if f.val = 116 then 20 else if f.val = 122 then 21 else if f.val = 123 then 24 else 0
                      else
                        fun f => if f.val = 108 then 24 else if f.val = 114 then 19 else if f.val = 115 then 20 else if f.val = 116 then 24 else 0
                    else
                      if index < 549 then
                        fun f => if f.val = 15 then 9 else if f.val = 16 then 9 else 0
                      else
                        fun f => if f.val = 2 then 9 else if f.val = 15 then 3 else 0
              else
                if index < 558 then
                  if index < 554 then
                    if index < 552 then
                      if index < 551 then
                        fun f => if f.val = 2 then 3 else if f.val = 16 then 3 else 0
                      else
                        fun f => if f.val = 18 then 9 else if f.val = 20 then 9 else 0
                    else
                      if index < 553 then
                        fun f => if f.val = 11 then 9 else if f.val = 20 then 3 else 0
                      else
                        fun f => if f.val = 11 then 3 else if f.val = 18 then 3 else 0
                  else
                    if index < 556 then
                      if index < 555 then
                        fun f => if f.val = 15 then 1 else if f.val = 20 then 1 else 0
                      else
                        fun f => if f.val = 16 then 1 else if f.val = 18 then 1 else 0
                    else
                      if index < 557 then
                        fun f => if f.val = 2 then 1 else if f.val = 11 then 1 else 0
                      else
                        fun f => if f.val = 14 then 9 else if f.val = 66 then 9 else 0
                else
                  if index < 562 then
                    if index < 560 then
                      if index < 559 then
                        fun f => if f.val = 1 then 9 else if f.val = 80 then 9 else 0
                      else
                        fun f => if f.val = 1 then 3 else if f.val = 14 then 3 else 0
                    else
                      if index < 561 then
                        fun f => if f.val = 67 then 9 else if f.val = 80 then 3 else 0
                      else
                        fun f => if f.val = 66 then 3 else if f.val = 67 then 3 else 0
                  else
                    if index < 564 then
                      if index < 563 then
                        fun f => if f.val = 15 then 2 else if f.val = 79 then 9 else 0
                      else
                        fun f => if f.val = 14 then 1 else if f.val = 16 then 2 else 0
                    else
                      if index < 565 then
                        fun f => if f.val = 66 then 1 else if f.val = 79 then 3 else 0
                      else
                        if index < 566 then
                          fun f => if f.val = 1 then 1 else if f.val = 2 then 2 else 0
                        else
                          fun f => if f.val = 80 then 1 else if f.val = 81 then 9 else 0
            else
              if index < 583 then
                if index < 575 then
                  if index < 571 then
                    if index < 569 then
                      if index < 568 then
                        fun f => if f.val = 79 then 1 else if f.val = 81 then 3 else 0
                      else
                        fun f => if f.val = 67 then 1 else if f.val = 81 then 1 else 0
                    else
                      if index < 570 then
                        fun f => if f.val = 0 then 9 else if f.val = 3 then 9 else 0
                      else
                        fun f => if f.val = 3 then 3 else if f.val = 12 then 9 else 0
                  else
                    if index < 573 then
                      if index < 572 then
                        fun f => if f.val = 0 then 3 else if f.val = 12 then 3 else 0
                      else
                        fun f => if f.val = 3 then 1 else if f.val = 20 then 2 else 0
                    else
                      if index < 574 then
                        fun f => if f.val = 0 then 1 else if f.val = 18 then 2 else 0
                      else
                        fun f => if f.val = 11 then 2 else if f.val = 12 then 1 else 0
                else
                  if index < 579 then
                    if index < 577 then
                      if index < 576 then
                        fun f => if f.val = 3 then 2 else if f.val = 70 then 9 else 0
                      else
                        fun f => if f.val = 0 then 2 else if f.val = 14 then 2 else 0
                    else
                      if index < 578 then
                        fun f => if f.val = 66 then 2 else if f.val = 70 then 3 else 0
                      else
                        fun f => if f.val = 1 then 2 else if f.val = 12 then 2 else 0
                  else
                    if index < 581 then
                      if index < 580 then
                        fun f => if f.val = 69 then 9 else if f.val = 80 then 2 else 0
                      else
                        fun f => if f.val = 69 then 3 else if f.val = 70 then 1 else 0
                    else
                      if index < 582 then
                        fun f => if f.val = 67 then 2 else if f.val = 69 then 1 else 0
                      else
                        fun f => if f.val = 15 then 6 else if f.val = 17 then 9 else 0
              else
                if index < 591 then
                  if index < 587 then
                    if index < 585 then
                      if index < 584 then
                        fun f => if f.val = 16 then 6 else if f.val = 17 then 3 else 0
                      else
                        fun f => if f.val = 19 then 9 else if f.val = 20 then 6 else 0
                    else
                      if index < 586 then
                        fun f => if f.val = 18 then 6 else if f.val = 19 then 3 else 0
                      else
                        fun f => if f.val = 17 then 1 else if f.val = 19 then 1 else 0
                  else
                    if index < 589 then
                      if index < 588 then
                        fun f => if f.val = 13 then 9 else if f.val = 68 then 9 else 0
                      else
                        fun f => if f.val = 13 then 3 else if f.val = 14 then 6 else 0
                    else
                      if index < 590 then
                        fun f => if f.val = 68 then 3 else if f.val = 77 then 9 else 0
                      else
                        fun f => if f.val = 66 then 6 else if f.val = 77 then 3 else 0
                else
                  if index < 595 then
                    if index < 593 then
                      if index < 592 then
                        fun f => if f.val = 13 then 1 else if f.val = 17 then 2 else 0
                      else
                        fun f => if f.val = 65 then 9 else if f.val = 68 then 1 else 0
                    else
                      if index < 594 then
                        fun f => if f.val = 65 then 3 else if f.val = 79 then 2 else 0
                      else
                        fun f => if f.val = 65 then 1 else if f.val = 77 then 1 else 0
                  else
                    if index < 597 then
                      if index < 596 then
                        fun f => if f.val = 3 then 6 else if f.val = 6 then 9 else 0
                      else
                        fun f => if f.val = 0 then 6 else if f.val = 6 then 3 else 0
                    else
                      if index < 598 then
                        fun f => if f.val = 6 then 1 else if f.val = 19 then 2 else 0
                      else
                        if index < 599 then
                          fun f => if f.val = 6 then 2 else if f.val = 13 then 2 else 0
                        else
                          fun f => if f.val = 68 then 2 else if f.val = 74 then 9 else 0
          else
            if index < 633 then
              if index < 616 then
                if index < 608 then
                  if index < 604 then
                    if index < 602 then
                      if index < 601 then
                        fun f => if f.val = 70 then 2 else if f.val = 74 then 3 else 0
                      else
                        fun f => if f.val = 74 then 1 else if f.val = 77 then 2 else 0
                    else
                      if index < 603 then
                        fun f => if f.val = 4 then 9 else if f.val = 15 then 18 else 0
                      else
                        fun f => if f.val = 2 then 6 else if f.val = 4 then 3 else 0
                  else
                    if index < 606 then
                      if index < 605 then
                        fun f => if f.val = 20 then 18 else if f.val = 26 then 9 else 0
                      else
                        fun f => if f.val = 11 then 6 else if f.val = 31 then 9 else 0
                    else
                      if index < 607 then
                        fun f => if f.val = 22 then 9 else if f.val = 26 then 3 else 0
                      else
                        fun f => if f.val = 22 then 3 else if f.val = 31 then 3 else 0
                else
                  if index < 612 then
                    if index < 610 then
                      if index < 609 then
                        fun f => if f.val = 4 then 1 else if f.val = 25 then 9 else 0
                      else
                        fun f => if f.val = 25 then 3 else if f.val = 26 then 1 else 0
                    else
                      if index < 611 then
                        fun f => if f.val = 23 then 9 else if f.val = 25 then 1 else 0
                      else
                        fun f => if f.val = 23 then 3 else if f.val = 31 then 1 else 0
                  else
                    if index < 614 then
                      if index < 613 then
                        fun f => if f.val = 22 then 1 else if f.val = 23 then 1 else 0
                      else
                        fun f => if f.val = 5 then 9 else if f.val = 78 then 9 else 0
                    else
                      if index < 615 then
                        fun f => if f.val = 1 then 6 else if f.val = 5 then 3 else 0
                      else
                        fun f => if f.val = 80 then 6 else if f.val = 82 then 9 else 0
              else
                if index < 624 then
                  if index < 620 then
                    if index < 618 then
                      if index < 617 then
                        fun f => if f.val = 78 then 3 else if f.val = 82 then 3 else 0
                      else
                        fun f => if f.val = 4 then 2 else if f.val = 5 then 1 else 0
                    else
                      if index < 619 then
                        fun f => if f.val = 78 then 1 else if f.val = 79 then 6 else 0
                      else
                        fun f => if f.val = 81 then 2 else if f.val = 82 then 1 else 0
                  else
                    if index < 622 then
                      if index < 621 then
                        fun f => if f.val = 3 then 18 else if f.val = 9 then 9 else 0
                      else
                        fun f => if f.val = 9 then 3 else if f.val = 12 then 6 else 0
                    else
                      if index < 623 then
                        fun f => if f.val = 9 then 1 else if f.val = 30 then 9 else 0
                      else
                        fun f => if f.val = 26 then 2 else if f.val = 30 then 3 else 0
                else
                  if index < 628 then
                    if index < 626 then
                      if index < 625 then
                        fun f => if f.val = 30 then 1 else if f.val = 33 then 9 else 0
                      else
                        fun f => if f.val = 31 then 2 else if f.val = 33 then 3 else 0
                    else
                      if index < 627 then
                        fun f => if f.val = 22 then 2 else if f.val = 33 then 1 else 0
                      else
                        fun f => if f.val = 5 then 2 else if f.val = 9 then 2 else 0
                  else
                    if index < 630 then
                      if index < 629 then
                        fun f => if f.val = 70 then 6 else if f.val = 78 then 2 else 0
                      else
                        fun f => if f.val = 69 then 2 else if f.val = 82 then 2 else 0
                    else
                      if index < 631 then
                        fun f => if f.val = 4 then 6 else if f.val = 17 then 6 else 0
                      else
                        if index < 632 then
                          fun f => if f.val = 19 then 6 else if f.val = 28 then 9 else 0
                        else
                          fun f => if f.val = 26 then 6 else if f.val = 35 then 9 else 0
            else
              if index < 650 then
                if index < 641 then
                  if index < 637 then
                    if index < 635 then
                      if index < 634 then
                        fun f => if f.val = 28 then 3 else if f.val = 35 then 3 else 0
                      else
                        fun f => if f.val = 25 then 2 else if f.val = 39 then 9 else 0
                    else
                      if index < 636 then
                        fun f => if f.val = 28 then 1 else if f.val = 39 then 3 else 0
                      else
                        fun f => if f.val = 35 then 1 else if f.val = 39 then 1 else 0
                  else
                    if index < 639 then
                      if index < 638 then
                        fun f => if f.val = 5 then 6 else if f.val = 13 then 6 else 0
                      else
                        fun f => if f.val = 68 then 6 else if f.val = 71 then 9 else 0
                    else
                      if index < 640 then
                        fun f => if f.val = 71 then 3 else if f.val = 78 then 6 else 0
                      else
                        fun f => if f.val = 65 then 2 else if f.val = 71 then 1 else 0
                else
                  if index < 645 then
                    if index < 643 then
                      if index < 642 then
                        fun f => if f.val = 6 then 6 else if f.val = 9 then 6 else 0
                      else
                        fun f => if f.val = 27 then 9 else if f.val = 30 then 2 else 0
                    else
                      if index < 644 then
                        fun f => if f.val = 27 then 3 else if f.val = 28 then 2 else 0
                      else
                        fun f => if f.val = 27 then 1 else if f.val = 35 then 2 else 0
                  else
                    if index < 647 then
                      if index < 646 then
                        fun f => if f.val = 71 then 2 else if f.val = 74 then 2 else 0
                      else
                        fun f => if f.val = 8 then 9 else if f.val = 10 then 9 else 0
                    else
                      if index < 648 then
                        fun f => if f.val = 8 then 3 else if f.val = 16 then 18 else 0
                      else
                        if index < 649 then
                          fun f => if f.val = 2 then 18 else if f.val = 10 then 3 else 0
                        else
                          fun f => if f.val = 8 then 1 else if f.val = 18 then 18 else 0
              else
                if index < 658 then
                  if index < 654 then
                    if index < 652 then
                      if index < 651 then
                        fun f => if f.val = 10 then 1 else if f.val = 11 then 18 else 0
                      else
                        fun f => if f.val = 8 then 2 else if f.val = 14 then 18 else 0
                    else
                      if index < 653 then
                        fun f => if f.val = 1 then 18 else if f.val = 10 then 2 else 0
                      else
                        fun f => if f.val = 0 then 18 else if f.val = 8 then 6 else 0
                  else
                    if index < 656 then
                      if index < 655 then
                        fun f => if f.val = 10 then 6 else if f.val = 12 then 18 else 0
                      else
                        fun f => if f.val = 7 then 9 else if f.val = 8 then 18 else 0
                    else
                      if index < 657 then
                        fun f => if f.val = 7 then 3 else if f.val = 17 then 18 else 0
                      else
                        fun f => if f.val = 7 then 1 else if f.val = 19 then 18 else 0
                else
                  if index < 662 then
                    if index < 660 then
                      if index < 659 then
                        fun f => if f.val = 7 then 2 else if f.val = 13 then 18 else 0
                      else
                        fun f => if f.val = 6 then 18 else if f.val = 7 then 6 else 0
                    else
                      if index < 661 then
                        fun f => if f.val = 10 then 18 else if f.val = 54 then 9 else 0
                      else
                        fun f => if f.val = 4 then 18 else if f.val = 47 then 9 else 0
                  else
                    if index < 664 then
                      if index < 663 then
                        fun f => if f.val = 45 then 9 else if f.val = 47 then 3 else 0
                      else
                        fun f => if f.val = 45 then 3 else if f.val = 54 then 3 else 0
                    else
                      if index < 665 then
                        fun f => if f.val = 32 then 9 else if f.val = 53 then 9 else 0
                      else
                        if index < 666 then
                          fun f => if f.val = 31 then 6 else if f.val = 32 then 3 else 0
                        else
                          fun f => if f.val = 53 then 3 else if f.val = 54 then 1 else 0
        else
          if index < 734 then
            if index < 700 then
              if index < 683 then
                if index < 675 then
                  if index < 671 then
                    if index < 669 then
                      if index < 668 then
                        fun f => if f.val = 25 then 6 else if f.val = 47 then 1 else 0
                      else
                        fun f => if f.val = 23 then 2 else if f.val = 32 then 1 else 0
                    else
                      if index < 670 then
                        fun f => if f.val = 45 then 1 else if f.val = 53 then 1 else 0
                      else
                        fun f => if f.val = 5 then 18 else if f.val = 64 then 9 else 0
                  else
                    if index < 673 then
                      if index < 672 then
                        fun f => if f.val = 54 then 2 else if f.val = 64 then 3 else 0
                      else
                        fun f => if f.val = 59 then 9 else if f.val = 64 then 1 else 0
                    else
                      if index < 674 then
                        fun f => if f.val = 47 then 2 else if f.val = 59 then 3 else 0
                      else
                        fun f => if f.val = 45 then 2 else if f.val = 59 then 1 else 0
                else
                  if index < 679 then
                    if index < 677 then
                      if index < 676 then
                        fun f => if f.val = 9 then 18 else if f.val = 52 then 9 else 0
                      else
                        fun f => if f.val = 52 then 3 else if f.val = 55 then 9 else 0
                    else
                      if index < 678 then
                        fun f => if f.val = 54 then 6 else if f.val = 55 then 3 else 0
                      else
                        fun f => if f.val = 30 then 6 else if f.val = 52 then 1 else 0
                  else
                    if index < 681 then
                      if index < 680 then
                        fun f => if f.val = 32 then 2 else if f.val = 33 then 2 else 0
                      else
                        fun f => if f.val = 53 then 2 else if f.val = 55 then 1 else 0
                    else
                      if index < 682 then
                        fun f => if f.val = 46 then 9 else if f.val = 64 then 2 else 0
                      else
                        fun f => if f.val = 46 then 3 else if f.val = 52 then 2 else 0
              else
                if index < 691 then
                  if index < 687 then
                    if index < 685 then
                      if index < 684 then
                        fun f => if f.val = 46 then 1 else if f.val = 55 then 2 else 0
                      else
                        fun f => if f.val = 7 then 18 else if f.val = 63 then 9 else 0
                    else
                      if index < 686 then
                        fun f => if f.val = 47 then 6 else if f.val = 61 then 9 else 0
                      else
                        fun f => if f.val = 61 then 3 else if f.val = 63 then 3 else 0
                  else
                    if index < 689 then
                      if index < 688 then
                        fun f => if f.val = 41 then 9 else if f.val = 50 then 9 else 0
                      else
                        fun f => if f.val = 28 then 6 else if f.val = 41 then 3 else 0
                    else
                      if index < 690 then
                        fun f => if f.val = 50 then 3 else if f.val = 63 then 1 else 0
                      else
                        fun f => if f.val = 39 then 2 else if f.val = 41 then 1 else 0
                else
                  if index < 695 then
                    if index < 693 then
                      if index < 692 then
                        fun f => if f.val = 50 then 1 else if f.val = 61 then 1 else 0
                      else
                        fun f => if f.val = 63 then 2 else if f.val = 64 then 6 else 0
                    else
                      if index < 694 then
                        fun f => if f.val = 59 then 2 else if f.val = 61 then 2 else 0
                      else
                        fun f => if f.val = 49 then 9 else if f.val = 52 then 6 else 0
                  else
                    if index < 697 then
                      if index < 696 then
                        fun f => if f.val = 49 then 3 else if f.val = 63 then 6 else 0
                      else
                        fun f => if f.val = 27 then 2 else if f.val = 41 then 2 else 0
                    else
                      if index < 698 then
                        fun f => if f.val = 49 then 1 else if f.val = 50 then 2 else 0
                      else
                        if index < 699 then
                          fun f => if f.val = 46 then 2 else if f.val = 49 then 2 else 0
                        else
                          fun f => if f.val = 37 then 9 else if f.val = 38 then 9 else 0
            else
              if index < 717 then
                if index < 708 then
                  if index < 704 then
                    if index < 702 then
                      if index < 701 then
                        fun f => if f.val = 23 then 6 else if f.val = 37 then 3 else 0
                      else
                        fun f => if f.val = 23 then 18 else if f.val = 38 then 3 else 0
                    else
                      if index < 703 then
                        fun f => if f.val = 40 then 9 else if f.val = 42 then 9 else 0
                      else
                        fun f => if f.val = 32 then 6 else if f.val = 42 then 3 else 0
                  else
                    if index < 706 then
                      if index < 705 then
                        fun f => if f.val = 32 then 18 else if f.val = 40 then 3 else 0
                      else
                        fun f => if f.val = 37 then 1 else if f.val = 42 then 1 else 0
                    else
                      if index < 707 then
                        fun f => if f.val = 38 then 1 else if f.val = 40 then 1 else 0
                      else
                        fun f => if f.val = 34 then 9 else if f.val = 36 then 9 else 0
                else
                  if index < 712 then
                    if index < 710 then
                      if index < 709 then
                        fun f => if f.val = 22 then 6 else if f.val = 34 then 3 else 0
                      else
                        fun f => if f.val = 22 then 18 else if f.val = 36 then 3 else 0
                    else
                      if index < 711 then
                        fun f => if f.val = 34 then 1 else if f.val = 37 then 2 else 0
                      else
                        fun f => if f.val = 36 then 1 else if f.val = 38 then 2 else 0
                  else
                    if index < 714 then
                      if index < 713 then
                        fun f => if f.val = 21 then 9 else if f.val = 24 then 9 else 0
                      else
                        fun f => if f.val = 24 then 3 else if f.val = 33 then 6 else 0
                    else
                      if index < 715 then
                        fun f => if f.val = 21 then 3 else if f.val = 33 then 18 else 0
                      else
                        if index < 716 then
                          fun f => if f.val = 24 then 1 else if f.val = 42 then 2 else 0
                        else
                          fun f => if f.val = 21 then 1 else if f.val = 40 then 2 else 0
              else
                if index < 725 then
                  if index < 721 then
                    if index < 719 then
                      if index < 718 then
                        fun f => if f.val = 24 then 2 else if f.val = 34 then 2 else 0
                      else
                        fun f => if f.val = 21 then 2 else if f.val = 36 then 2 else 0
                    else
                      if index < 720 then
                        fun f => if f.val = 37 then 6 else if f.val = 39 then 6 else 0
                      else
                        fun f => if f.val = 38 then 6 else if f.val = 39 then 18 else 0
                  else
                    if index < 723 then
                      if index < 722 then
                        fun f => if f.val = 41 then 6 else if f.val = 42 then 6 else 0
                      else
                        fun f => if f.val = 40 then 6 else if f.val = 41 then 18 else 0
                    else
                      if index < 724 then
                        fun f => if f.val = 34 then 6 else if f.val = 35 then 6 else 0
                      else
                        fun f => if f.val = 35 then 18 else if f.val = 36 then 6 else 0
                else
                  if index < 729 then
                    if index < 727 then
                      if index < 726 then
                        fun f => if f.val = 24 then 6 else if f.val = 27 then 6 else 0
                      else
                        fun f => if f.val = 21 then 6 else if f.val = 27 then 18 else 0
                    else
                      if index < 728 then
                        fun f => if f.val = 25 then 18 else if f.val = 37 then 18 else 0
                      else
                        fun f => if f.val = 42 then 18 else if f.val = 48 then 9 else 0
                  else
                    if index < 731 then
                      if index < 730 then
                        fun f => if f.val = 44 then 9 else if f.val = 48 then 3 else 0
                      else
                        fun f => if f.val = 44 then 3 else if f.val = 53 then 6 else 0
                    else
                      if index < 732 then
                        fun f => if f.val = 47 then 18 else if f.val = 48 then 1 else 0
                      else
                        if index < 733 then
                          fun f => if f.val = 44 then 1 else if f.val = 45 then 6 else 0
                        else
                          fun f => if f.val = 26 then 18 else if f.val = 34 then 18 else 0
          else
            if index < 767 then
              if index < 750 then
                if index < 742 then
                  if index < 738 then
                    if index < 736 then
                      if index < 735 then
                        fun f => if f.val = 24 then 18 else if f.val = 30 then 18 else 0
                      else
                        fun f => if f.val = 48 then 2 else if f.val = 52 then 18 else 0
                    else
                      if index < 737 then
                        fun f => if f.val = 44 then 2 else if f.val = 55 then 6 else 0
                      else
                        fun f => if f.val = 48 then 6 else if f.val = 57 then 9 else 0
                  else
                    if index < 740 then
                      if index < 739 then
                        fun f => if f.val = 50 then 6 else if f.val = 57 then 3 else 0
                      else
                        fun f => if f.val = 57 then 1 else if f.val = 61 then 6 else 0
                    else
                      if index < 741 then
                        fun f => if f.val = 49 then 6 else if f.val = 57 then 2 else 0
                      else
                        fun f => if f.val = 29 then 9 else if f.val = 31 then 18 else 0
                else
                  if index < 746 then
                    if index < 744 then
                      if index < 743 then
                        fun f => if f.val = 29 then 3 else if f.val = 38 then 18 else 0
                      else
                        fun f => if f.val = 29 then 1 else if f.val = 40 then 18 else 0
                    else
                      if index < 745 then
                        fun f => if f.val = 29 then 2 else if f.val = 36 then 18 else 0
                      else
                        fun f => if f.val = 21 then 18 else if f.val = 29 then 6 else 0
                  else
                    if index < 748 then
                      if index < 747 then
                        fun f => if f.val = 28 then 18 else if f.val = 29 then 18 else 0
                      else
                        fun f => if f.val = 59 then 6 else if f.val = 60 then 9 else 0
                    else
                      if index < 749 then
                        fun f => if f.val = 45 then 18 else if f.val = 60 then 3 else 0
                      else
                        fun f => if f.val = 62 then 9 else if f.val = 64 then 18 else 0
              else
                if index < 758 then
                  if index < 754 then
                    if index < 752 then
                      if index < 751 then
                        fun f => if f.val = 54 then 18 else if f.val = 62 then 3 else 0
                      else
                        fun f => if f.val = 60 then 1 else if f.val = 62 then 1 else 0
                    else
                      if index < 753 then
                        fun f => if f.val = 56 then 9 else if f.val = 58 then 9 else 0
                      else
                        fun f => if f.val = 44 then 6 else if f.val = 56 then 3 else 0
                  else
                    if index < 756 then
                      if index < 755 then
                        fun f => if f.val = 44 then 18 else if f.val = 58 then 3 else 0
                      else
                        fun f => if f.val = 56 then 1 else if f.val = 59 then 18 else 0
                    else
                      if index < 757 then
                        fun f => if f.val = 58 then 1 else if f.val = 60 then 2 else 0
                      else
                        fun f => if f.val = 43 then 9 else if f.val = 46 then 6 else 0
                else
                  if index < 762 then
                    if index < 760 then
                      if index < 759 then
                        fun f => if f.val = 43 then 3 else if f.val = 55 then 18 else 0
                      else
                        fun f => if f.val = 43 then 1 else if f.val = 62 then 2 else 0
                    else
                      if index < 761 then
                        fun f => if f.val = 46 then 18 else if f.val = 56 then 2 else 0
                      else
                        fun f => if f.val = 43 then 2 else if f.val = 58 then 2 else 0
                  else
                    if index < 764 then
                      if index < 763 then
                        fun f => if f.val = 60 then 6 else if f.val = 61 then 18 else 0
                      else
                        fun f => if f.val = 62 then 6 else if f.val = 63 then 18 else 0
                    else
                      if index < 765 then
                        fun f => if f.val = 56 then 6 else if f.val = 57 then 6 else 0
                      else
                        if index < 766 then
                          fun f => if f.val = 57 then 18 else if f.val = 58 then 6 else 0
                        else
                          fun f => if f.val = 43 then 6 else if f.val = 49 then 18 else 0
            else
              if index < 784 then
                if index < 775 then
                  if index < 771 then
                    if index < 769 then
                      if index < 768 then
                        fun f => if f.val = 48 then 18 else if f.val = 56 then 18 else 0
                      else
                        fun f => if f.val = 51 then 9 else if f.val = 53 then 18 else 0
                    else
                      if index < 770 then
                        fun f => if f.val = 51 then 3 else if f.val = 60 then 18 else 0
                      else
                        fun f => if f.val = 51 then 1 else if f.val = 62 then 18 else 0
                  else
                    if index < 773 then
                      if index < 772 then
                        fun f => if f.val = 51 then 2 else if f.val = 58 then 18 else 0
                      else
                        fun f => if f.val = 43 then 18 else if f.val = 51 then 6 else 0
                    else
                      if index < 774 then
                        fun f => if f.val = 50 then 18 else if f.val = 51 then 18 else 0
                      else
                        fun f => if f.val = 83 then 9 else if f.val = 85 then 9 else 0
                else
                  if index < 779 then
                    if index < 777 then
                      if index < 776 then
                        fun f => if f.val = 76 then 9 else if f.val = 85 then 3 else 0
                      else
                        fun f => if f.val = 76 then 3 else if f.val = 83 then 3 else 0
                    else
                      if index < 778 then
                        fun f => if f.val = 80 then 18 else if f.val = 85 then 1 else 0
                      else
                        fun f => if f.val = 81 then 6 else if f.val = 83 then 1 else 0
                  else
                    if index < 781 then
                      if index < 780 then
                        fun f => if f.val = 67 then 6 else if f.val = 76 then 1 else 0
                      else
                        fun f => if f.val = 68 then 18 else if f.val = 85 then 2 else 0
                    else
                      if index < 782 then
                        fun f => if f.val = 65 then 6 else if f.val = 83 then 2 else 0
                      else
                        if index < 783 then
                          fun f => if f.val = 76 then 2 else if f.val = 77 then 6 else 0
                        else
                          fun f => if f.val = 84 then 9 else if f.val = 85 then 6 else 0
              else
                if index < 792 then
                  if index < 788 then
                    if index < 786 then
                      if index < 785 then
                        fun f => if f.val = 83 then 6 else if f.val = 84 then 3 else 0
                      else
                        fun f => if f.val = 82 then 6 else if f.val = 84 then 1 else 0
                    else
                      if index < 787 then
                        fun f => if f.val = 71 then 6 else if f.val = 84 then 2 else 0
                      else
                        fun f => if f.val = 85 then 18 else if f.val = 91 then 9 else 0
                  else
                    if index < 790 then
                      if index < 789 then
                        fun f => if f.val = 76 then 6 else if f.val = 96 then 9 else 0
                      else
                        fun f => if f.val = 87 then 9 else if f.val = 91 then 3 else 0
                    else
                      if index < 791 then
                        fun f => if f.val = 87 then 3 else if f.val = 96 then 3 else 0
                      else
                        fun f => if f.val = 69 then 6 else if f.val = 90 then 9 else 0
                else
                  if index < 796 then
                    if index < 794 then
                      if index < 793 then
                        fun f => if f.val = 90 then 3 else if f.val = 91 then 1 else 0
                      else
                        fun f => if f.val = 88 then 9 else if f.val = 90 then 1 else 0
                    else
                      if index < 795 then
                        fun f => if f.val = 88 then 3 else if f.val = 96 then 1 else 0
                      else
                        fun f => if f.val = 87 then 1 else if f.val = 88 then 1 else 0
                  else
                    if index < 798 then
                      if index < 797 then
                        fun f => if f.val = 74 then 6 else if f.val = 95 then 9 else 0
                      else
                        fun f => if f.val = 91 then 2 else if f.val = 95 then 3 else 0
                    else
                      if index < 799 then
                        fun f => if f.val = 95 then 1 else if f.val = 98 then 9 else 0
                      else
                        if index < 800 then
                          fun f => if f.val = 96 then 2 else if f.val = 98 then 3 else 0
                        else
                          fun f => if f.val = 87 then 2 else if f.val = 98 then 1 else 0
      else
        if index < 935 then
          if index < 868 then
            if index < 834 then
              if index < 817 then
                if index < 809 then
                  if index < 805 then
                    if index < 803 then
                      if index < 802 then
                        fun f => if f.val = 84 then 6 else if f.val = 93 then 9 else 0
                      else
                        fun f => if f.val = 91 then 6 else if f.val = 100 then 9 else 0
                    else
                      if index < 804 then
                        fun f => if f.val = 93 then 3 else if f.val = 100 then 3 else 0
                      else
                        fun f => if f.val = 90 then 2 else if f.val = 104 then 9 else 0
                  else
                    if index < 807 then
                      if index < 806 then
                        fun f => if f.val = 93 then 1 else if f.val = 104 then 3 else 0
                      else
                        fun f => if f.val = 100 then 1 else if f.val = 104 then 1 else 0
                    else
                      if index < 808 then
                        fun f => if f.val = 92 then 9 else if f.val = 95 then 2 else 0
                      else
                        fun f => if f.val = 92 then 3 else if f.val = 93 then 2 else 0
                else
                  if index < 813 then
                    if index < 811 then
                      if index < 810 then
                        fun f => if f.val = 92 then 1 else if f.val = 100 then 2 else 0
                      else
                        fun f => if f.val = 73 then 9 else if f.val = 75 then 9 else 0
                    else
                      if index < 812 then
                        fun f => if f.val = 73 then 3 else if f.val = 81 then 18 else 0
                      else
                        fun f => if f.val = 67 then 18 else if f.val = 75 then 3 else 0
                  else
                    if index < 815 then
                      if index < 814 then
                        fun f => if f.val = 73 then 1 else if f.val = 83 then 18 else 0
                      else
                        fun f => if f.val = 75 then 1 else if f.val = 76 then 18 else 0
                    else
                      if index < 816 then
                        fun f => if f.val = 73 then 2 else if f.val = 79 then 18 else 0
                      else
                        fun f => if f.val = 66 then 18 else if f.val = 75 then 2 else 0
              else
                if index < 825 then
                  if index < 821 then
                    if index < 819 then
                      if index < 818 then
                        fun f => if f.val = 65 then 18 else if f.val = 73 then 6 else 0
                      else
                        fun f => if f.val = 75 then 6 else if f.val = 77 then 18 else 0
                    else
                      if index < 820 then
                        fun f => if f.val = 72 then 9 else if f.val = 73 then 18 else 0
                      else
                        fun f => if f.val = 72 then 3 else if f.val = 82 then 18 else 0
                  else
                    if index < 823 then
                      if index < 822 then
                        fun f => if f.val = 72 then 1 else if f.val = 84 then 18 else 0
                      else
                        fun f => if f.val = 72 then 2 else if f.val = 78 then 18 else 0
                    else
                      if index < 824 then
                        fun f => if f.val = 71 then 18 else if f.val = 72 then 6 else 0
                      else
                        fun f => if f.val = 75 then 18 else if f.val = 119 then 9 else 0
                else
                  if index < 829 then
                    if index < 827 then
                      if index < 826 then
                        fun f => if f.val = 69 then 18 else if f.val = 112 then 9 else 0
                      else
                        fun f => if f.val = 110 then 9 else if f.val = 112 then 3 else 0
                    else
                      if index < 828 then
                        fun f => if f.val = 110 then 3 else if f.val = 119 then 3 else 0
                      else
                        fun f => if f.val = 97 then 9 else if f.val = 118 then 9 else 0
                  else
                    if index < 831 then
                      if index < 830 then
                        fun f => if f.val = 96 then 6 else if f.val = 97 then 3 else 0
                      else
                        fun f => if f.val = 118 then 3 else if f.val = 119 then 1 else 0
                    else
                      if index < 832 then
                        fun f => if f.val = 90 then 6 else if f.val = 112 then 1 else 0
                      else
                        if index < 833 then
                          fun f => if f.val = 88 then 2 else if f.val = 97 then 1 else 0
                        else
                          fun f => if f.val = 110 then 1 else if f.val = 118 then 1 else 0
            else
              if index < 851 then
                if index < 842 then
                  if index < 838 then
                    if index < 836 then
                      if index < 835 then
                        fun f => if f.val = 70 then 18 else if f.val = 129 then 9 else 0
                      else
                        fun f => if f.val = 119 then 2 else if f.val = 129 then 3 else 0
                    else
                      if index < 837 then
                        fun f => if f.val = 124 then 9 else if f.val = 129 then 1 else 0
                      else
                        fun f => if f.val = 112 then 2 else if f.val = 124 then 3 else 0
                  else
                    if index < 840 then
                      if index < 839 then
                        fun f => if f.val = 110 then 2 else if f.val = 124 then 1 else 0
                      else
                        fun f => if f.val = 74 then 18 else if f.val = 117 then 9 else 0
                    else
                      if index < 841 then
                        fun f => if f.val = 117 then 3 else if f.val = 120 then 9 else 0
                      else
                        fun f => if f.val = 119 then 6 else if f.val = 120 then 3 else 0
                else
                  if index < 846 then
                    if index < 844 then
                      if index < 843 then
                        fun f => if f.val = 95 then 6 else if f.val = 117 then 1 else 0
                      else
                        fun f => if f.val = 97 then 2 else if f.val = 98 then 2 else 0
                    else
                      if index < 845 then
                        fun f => if f.val = 118 then 2 else if f.val = 120 then 1 else 0
                      else
                        fun f => if f.val = 111 then 9 else if f.val = 129 then 2 else 0
                  else
                    if index < 848 then
                      if index < 847 then
                        fun f => if f.val = 111 then 3 else if f.val = 117 then 2 else 0
                      else
                        fun f => if f.val = 111 then 1 else if f.val = 120 then 2 else 0
                    else
                      if index < 849 then
                        fun f => if f.val = 72 then 18 else if f.val = 128 then 9 else 0
                      else
                        if index < 850 then
                          fun f => if f.val = 112 then 6 else if f.val = 126 then 9 else 0
                        else
                          fun f => if f.val = 126 then 3 else if f.val = 128 then 3 else 0
              else
                if index < 859 then
                  if index < 855 then
                    if index < 853 then
                      if index < 852 then
                        fun f => if f.val = 106 then 9 else if f.val = 115 then 9 else 0
                      else
                        fun f => if f.val = 93 then 6 else if f.val = 106 then 3 else 0
                    else
                      if index < 854 then
                        fun f => if f.val = 115 then 3 else if f.val = 128 then 1 else 0
                      else
                        fun f => if f.val = 104 then 2 else if f.val = 106 then 1 else 0
                  else
                    if index < 857 then
                      if index < 856 then
                        fun f => if f.val = 115 then 1 else if f.val = 126 then 1 else 0
                      else
                        fun f => if f.val = 128 then 2 else if f.val = 129 then 6 else 0
                    else
                      if index < 858 then
                        fun f => if f.val = 124 then 2 else if f.val = 126 then 2 else 0
                      else
                        fun f => if f.val = 114 then 9 else if f.val = 117 then 6 else 0
                else
                  if index < 863 then
                    if index < 861 then
                      if index < 860 then
                        fun f => if f.val = 114 then 3 else if f.val = 128 then 6 else 0
                      else
                        fun f => if f.val = 92 then 2 else if f.val = 106 then 2 else 0
                    else
                      if index < 862 then
                        fun f => if f.val = 114 then 1 else if f.val = 115 then 2 else 0
                      else
                        fun f => if f.val = 111 then 2 else if f.val = 114 then 2 else 0
                  else
                    if index < 865 then
                      if index < 864 then
                        fun f => if f.val = 102 then 9 else if f.val = 103 then 9 else 0
                      else
                        fun f => if f.val = 88 then 6 else if f.val = 102 then 3 else 0
                    else
                      if index < 866 then
                        fun f => if f.val = 88 then 18 else if f.val = 103 then 3 else 0
                      else
                        if index < 867 then
                          fun f => if f.val = 105 then 9 else if f.val = 107 then 9 else 0
                        else
                          fun f => if f.val = 97 then 6 else if f.val = 107 then 3 else 0
          else
            if index < 901 then
              if index < 884 then
                if index < 876 then
                  if index < 872 then
                    if index < 870 then
                      if index < 869 then
                        fun f => if f.val = 97 then 18 else if f.val = 105 then 3 else 0
                      else
                        fun f => if f.val = 102 then 1 else if f.val = 107 then 1 else 0
                    else
                      if index < 871 then
                        fun f => if f.val = 103 then 1 else if f.val = 105 then 1 else 0
                      else
                        fun f => if f.val = 99 then 9 else if f.val = 101 then 9 else 0
                  else
                    if index < 874 then
                      if index < 873 then
                        fun f => if f.val = 87 then 6 else if f.val = 99 then 3 else 0
                      else
                        fun f => if f.val = 87 then 18 else if f.val = 101 then 3 else 0
                    else
                      if index < 875 then
                        fun f => if f.val = 99 then 1 else if f.val = 102 then 2 else 0
                      else
                        fun f => if f.val = 101 then 1 else if f.val = 103 then 2 else 0
                else
                  if index < 880 then
                    if index < 878 then
                      if index < 877 then
                        fun f => if f.val = 86 then 9 else if f.val = 89 then 9 else 0
                      else
                        fun f => if f.val = 89 then 3 else if f.val = 98 then 6 else 0
                    else
                      if index < 879 then
                        fun f => if f.val = 86 then 3 else if f.val = 98 then 18 else 0
                      else
                        fun f => if f.val = 89 then 1 else if f.val = 107 then 2 else 0
                  else
                    if index < 882 then
                      if index < 881 then
                        fun f => if f.val = 86 then 1 else if f.val = 105 then 2 else 0
                      else
                        fun f => if f.val = 89 then 2 else if f.val = 99 then 2 else 0
                    else
                      if index < 883 then
                        fun f => if f.val = 86 then 2 else if f.val = 101 then 2 else 0
                      else
                        fun f => if f.val = 102 then 6 else if f.val = 104 then 6 else 0
              else
                if index < 892 then
                  if index < 888 then
                    if index < 886 then
                      if index < 885 then
                        fun f => if f.val = 103 then 6 else if f.val = 104 then 18 else 0
                      else
                        fun f => if f.val = 106 then 6 else if f.val = 107 then 6 else 0
                    else
                      if index < 887 then
                        fun f => if f.val = 105 then 6 else if f.val = 106 then 18 else 0
                      else
                        fun f => if f.val = 99 then 6 else if f.val = 100 then 6 else 0
                  else
                    if index < 890 then
                      if index < 889 then
                        fun f => if f.val = 100 then 18 else if f.val = 101 then 6 else 0
                      else
                        fun f => if f.val = 89 then 6 else if f.val = 92 then 6 else 0
                    else
                      if index < 891 then
                        fun f => if f.val = 86 then 6 else if f.val = 92 then 18 else 0
                      else
                        fun f => if f.val = 90 then 18 else if f.val = 102 then 18 else 0
                else
                  if index < 896 then
                    if index < 894 then
                      if index < 893 then
                        fun f => if f.val = 107 then 18 else if f.val = 113 then 9 else 0
                      else
                        fun f => if f.val = 109 then 9 else if f.val = 113 then 3 else 0
                    else
                      if index < 895 then
                        fun f => if f.val = 109 then 3 else if f.val = 118 then 6 else 0
                      else
                        fun f => if f.val = 112 then 18 else if f.val = 113 then 1 else 0
                  else
                    if index < 898 then
                      if index < 897 then
                        fun f => if f.val = 109 then 1 else if f.val = 110 then 6 else 0
                      else
                        fun f => if f.val = 91 then 18 else if f.val = 99 then 18 else 0
                    else
                      if index < 899 then
                        fun f => if f.val = 89 then 18 else if f.val = 95 then 18 else 0
                      else
                        if index < 900 then
                          fun f => if f.val = 113 then 2 else if f.val = 117 then 18 else 0
                        else
                          fun f => if f.val = 109 then 2 else if f.val = 120 then 6 else 0
            else
              if index < 918 then
                if index < 909 then
                  if index < 905 then
                    if index < 903 then
                      if index < 902 then
                        fun f => if f.val = 113 then 6 else if f.val = 122 then 9 else 0
                      else
                        fun f => if f.val = 115 then 6 else if f.val = 122 then 3 else 0
                    else
                      if index < 904 then
                        fun f => if f.val = 122 then 1 else if f.val = 126 then 6 else 0
                      else
                        fun f => if f.val = 114 then 6 else if f.val = 122 then 2 else 0
                  else
                    if index < 907 then
                      if index < 906 then
                        fun f => if f.val = 94 then 9 else if f.val = 96 then 18 else 0
                      else
                        fun f => if f.val = 94 then 3 else if f.val = 103 then 18 else 0
                    else
                      if index < 908 then
                        fun f => if f.val = 94 then 1 else if f.val = 105 then 18 else 0
                      else
                        fun f => if f.val = 94 then 2 else if f.val = 101 then 18 else 0
                else
                  if index < 913 then
                    if index < 911 then
                      if index < 910 then
                        fun f => if f.val = 86 then 18 else if f.val = 94 then 6 else 0
                      else
                        fun f => if f.val = 93 then 18 else if f.val = 94 then 18 else 0
                    else
                      if index < 912 then
                        fun f => if f.val = 124 then 6 else if f.val = 125 then 9 else 0
                      else
                        fun f => if f.val = 110 then 18 else if f.val = 125 then 3 else 0
                  else
                    if index < 915 then
                      if index < 914 then
                        fun f => if f.val = 127 then 9 else if f.val = 129 then 18 else 0
                      else
                        fun f => if f.val = 119 then 18 else if f.val = 127 then 3 else 0
                    else
                      if index < 916 then
                        fun f => if f.val = 125 then 1 else if f.val = 127 then 1 else 0
                      else
                        if index < 917 then
                          fun f => if f.val = 121 then 9 else if f.val = 123 then 9 else 0
                        else
                          fun f => if f.val = 109 then 6 else if f.val = 121 then 3 else 0
              else
                if index < 926 then
                  if index < 922 then
                    if index < 920 then
                      if index < 919 then
                        fun f => if f.val = 109 then 18 else if f.val = 123 then 3 else 0
                      else
                        fun f => if f.val = 121 then 1 else if f.val = 124 then 18 else 0
                    else
                      if index < 921 then
                        fun f => if f.val = 123 then 1 else if f.val = 125 then 2 else 0
                      else
                        fun f => if f.val = 108 then 9 else if f.val = 111 then 6 else 0
                  else
                    if index < 924 then
                      if index < 923 then
                        fun f => if f.val = 108 then 3 else if f.val = 120 then 18 else 0
                      else
                        fun f => if f.val = 108 then 1 else if f.val = 127 then 2 else 0
                    else
                      if index < 925 then
                        fun f => if f.val = 111 then 18 else if f.val = 121 then 2 else 0
                      else
                        fun f => if f.val = 108 then 2 else if f.val = 123 then 2 else 0
                else
                  if index < 930 then
                    if index < 928 then
                      if index < 927 then
                        fun f => if f.val = 125 then 6 else if f.val = 126 then 18 else 0
                      else
                        fun f => if f.val = 127 then 6 else if f.val = 128 then 18 else 0
                    else
                      if index < 929 then
                        fun f => if f.val = 121 then 6 else if f.val = 122 then 6 else 0
                      else
                        fun f => if f.val = 122 then 18 else if f.val = 123 then 6 else 0
                  else
                    if index < 932 then
                      if index < 931 then
                        fun f => if f.val = 108 then 6 else if f.val = 114 then 18 else 0
                      else
                        fun f => if f.val = 113 then 18 else if f.val = 121 then 18 else 0
                    else
                      if index < 933 then
                        fun f => if f.val = 116 then 9 else if f.val = 118 then 18 else 0
                      else
                        if index < 934 then
                          fun f => if f.val = 116 then 3 else if f.val = 125 then 18 else 0
                        else
                          fun f => if f.val = 116 then 1 else if f.val = 127 then 18 else 0
        else
          if index < 1002 then
            if index < 968 then
              if index < 951 then
                if index < 943 then
                  if index < 939 then
                    if index < 937 then
                      if index < 936 then
                        fun f => if f.val = 116 then 2 else if f.val = 123 then 18 else 0
                      else
                        fun f => if f.val = 108 then 18 else if f.val = 116 then 6 else 0
                    else
                      if index < 938 then
                        fun f => if f.val = 115 then 18 else if f.val = 116 then 18 else 0
                      else
                        fun f => if f.val = 15 then 0 else 0
                  else
                    if index < 941 then
                      if index < 940 then
                        fun f => if f.val = 16 then 0 else 0
                      else
                        fun f => if f.val = 2 then 0 else 0
                    else
                      if index < 942 then
                        fun f => if f.val = 20 then 0 else 0
                      else
                        fun f => if f.val = 18 then 0 else 0
                else
                  if index < 947 then
                    if index < 945 then
                      if index < 944 then
                        fun f => if f.val = 11 then 0 else 0
                      else
                        fun f => if f.val = 14 then 0 else 0
                    else
                      if index < 946 then
                        fun f => if f.val = 66 then 0 else 0
                      else
                        fun f => if f.val = 1 then 0 else 0
                  else
                    if index < 949 then
                      if index < 948 then
                        fun f => if f.val = 80 then 0 else 0
                      else
                        fun f => if f.val = 67 then 0 else 0
                    else
                      if index < 950 then
                        fun f => if f.val = 79 then 0 else 0
                      else
                        fun f => if f.val = 81 then 0 else 0
              else
                if index < 959 then
                  if index < 955 then
                    if index < 953 then
                      if index < 952 then
                        fun f => if f.val = 3 then 0 else 0
                      else
                        fun f => if f.val = 0 then 0 else 0
                    else
                      if index < 954 then
                        fun f => if f.val = 12 then 0 else 0
                      else
                        fun f => if f.val = 70 then 0 else 0
                  else
                    if index < 957 then
                      if index < 956 then
                        fun f => if f.val = 69 then 0 else 0
                      else
                        fun f => if f.val = 17 then 0 else 0
                    else
                      if index < 958 then
                        fun f => if f.val = 19 then 0 else 0
                      else
                        fun f => if f.val = 13 then 0 else 0
                else
                  if index < 963 then
                    if index < 961 then
                      if index < 960 then
                        fun f => if f.val = 68 then 0 else 0
                      else
                        fun f => if f.val = 77 then 0 else 0
                    else
                      if index < 962 then
                        fun f => if f.val = 65 then 0 else 0
                      else
                        fun f => if f.val = 6 then 0 else 0
                  else
                    if index < 965 then
                      if index < 964 then
                        fun f => if f.val = 74 then 0 else 0
                      else
                        fun f => if f.val = 4 then 0 else 0
                    else
                      if index < 966 then
                        fun f => if f.val = 26 then 0 else 0
                      else
                        if index < 967 then
                          fun f => if f.val = 31 then 0 else 0
                        else
                          fun f => if f.val = 22 then 0 else 0
            else
              if index < 985 then
                if index < 976 then
                  if index < 972 then
                    if index < 970 then
                      if index < 969 then
                        fun f => if f.val = 25 then 0 else 0
                      else
                        fun f => if f.val = 23 then 0 else 0
                    else
                      if index < 971 then
                        fun f => if f.val = 5 then 0 else 0
                      else
                        fun f => if f.val = 78 then 0 else 0
                  else
                    if index < 974 then
                      if index < 973 then
                        fun f => if f.val = 82 then 0 else 0
                      else
                        fun f => if f.val = 9 then 0 else 0
                    else
                      if index < 975 then
                        fun f => if f.val = 30 then 0 else 0
                      else
                        fun f => if f.val = 33 then 0 else 0
                else
                  if index < 980 then
                    if index < 978 then
                      if index < 977 then
                        fun f => if f.val = 28 then 0 else 0
                      else
                        fun f => if f.val = 35 then 0 else 0
                    else
                      if index < 979 then
                        fun f => if f.val = 39 then 0 else 0
                      else
                        fun f => if f.val = 71 then 0 else 0
                  else
                    if index < 982 then
                      if index < 981 then
                        fun f => if f.val = 27 then 0 else 0
                      else
                        fun f => if f.val = 8 then 0 else 0
                    else
                      if index < 983 then
                        fun f => if f.val = 10 then 0 else 0
                      else
                        if index < 984 then
                          fun f => if f.val = 7 then 0 else 0
                        else
                          fun f => if f.val = 54 then 0 else 0
              else
                if index < 993 then
                  if index < 989 then
                    if index < 987 then
                      if index < 986 then
                        fun f => if f.val = 47 then 0 else 0
                      else
                        fun f => if f.val = 45 then 0 else 0
                    else
                      if index < 988 then
                        fun f => if f.val = 32 then 0 else 0
                      else
                        fun f => if f.val = 53 then 0 else 0
                  else
                    if index < 991 then
                      if index < 990 then
                        fun f => if f.val = 64 then 0 else 0
                      else
                        fun f => if f.val = 59 then 0 else 0
                    else
                      if index < 992 then
                        fun f => if f.val = 52 then 0 else 0
                      else
                        fun f => if f.val = 55 then 0 else 0
                else
                  if index < 997 then
                    if index < 995 then
                      if index < 994 then
                        fun f => if f.val = 46 then 0 else 0
                      else
                        fun f => if f.val = 63 then 0 else 0
                    else
                      if index < 996 then
                        fun f => if f.val = 61 then 0 else 0
                      else
                        fun f => if f.val = 41 then 0 else 0
                  else
                    if index < 999 then
                      if index < 998 then
                        fun f => if f.val = 50 then 0 else 0
                      else
                        fun f => if f.val = 49 then 0 else 0
                    else
                      if index < 1000 then
                        fun f => if f.val = 37 then 0 else 0
                      else
                        if index < 1001 then
                          fun f => if f.val = 38 then 0 else 0
                        else
                          fun f => if f.val = 42 then 0 else 0
          else
            if index < 1035 then
              if index < 1018 then
                if index < 1010 then
                  if index < 1006 then
                    if index < 1004 then
                      if index < 1003 then
                        fun f => if f.val = 40 then 0 else 0
                      else
                        fun f => if f.val = 34 then 0 else 0
                    else
                      if index < 1005 then
                        fun f => if f.val = 36 then 0 else 0
                      else
                        fun f => if f.val = 24 then 0 else 0
                  else
                    if index < 1008 then
                      if index < 1007 then
                        fun f => if f.val = 21 then 0 else 0
                      else
                        fun f => if f.val = 48 then 0 else 0
                    else
                      if index < 1009 then
                        fun f => if f.val = 44 then 0 else 0
                      else
                        fun f => if f.val = 57 then 0 else 0
                else
                  if index < 1014 then
                    if index < 1012 then
                      if index < 1011 then
                        fun f => if f.val = 29 then 0 else 0
                      else
                        fun f => if f.val = 60 then 0 else 0
                    else
                      if index < 1013 then
                        fun f => if f.val = 62 then 0 else 0
                      else
                        fun f => if f.val = 56 then 0 else 0
                  else
                    if index < 1016 then
                      if index < 1015 then
                        fun f => if f.val = 58 then 0 else 0
                      else
                        fun f => if f.val = 43 then 0 else 0
                    else
                      if index < 1017 then
                        fun f => if f.val = 51 then 0 else 0
                      else
                        fun f => if f.val = 85 then 0 else 0
              else
                if index < 1026 then
                  if index < 1022 then
                    if index < 1020 then
                      if index < 1019 then
                        fun f => if f.val = 83 then 0 else 0
                      else
                        fun f => if f.val = 76 then 0 else 0
                    else
                      if index < 1021 then
                        fun f => if f.val = 84 then 0 else 0
                      else
                        fun f => if f.val = 91 then 0 else 0
                  else
                    if index < 1024 then
                      if index < 1023 then
                        fun f => if f.val = 96 then 0 else 0
                      else
                        fun f => if f.val = 87 then 0 else 0
                    else
                      if index < 1025 then
                        fun f => if f.val = 90 then 0 else 0
                      else
                        fun f => if f.val = 88 then 0 else 0
                else
                  if index < 1030 then
                    if index < 1028 then
                      if index < 1027 then
                        fun f => if f.val = 95 then 0 else 0
                      else
                        fun f => if f.val = 98 then 0 else 0
                    else
                      if index < 1029 then
                        fun f => if f.val = 93 then 0 else 0
                      else
                        fun f => if f.val = 100 then 0 else 0
                  else
                    if index < 1032 then
                      if index < 1031 then
                        fun f => if f.val = 104 then 0 else 0
                      else
                        fun f => if f.val = 92 then 0 else 0
                    else
                      if index < 1033 then
                        fun f => if f.val = 73 then 0 else 0
                      else
                        if index < 1034 then
                          fun f => if f.val = 75 then 0 else 0
                        else
                          fun f => if f.val = 72 then 0 else 0
            else
              if index < 1052 then
                if index < 1043 then
                  if index < 1039 then
                    if index < 1037 then
                      if index < 1036 then
                        fun f => if f.val = 119 then 0 else 0
                      else
                        fun f => if f.val = 112 then 0 else 0
                    else
                      if index < 1038 then
                        fun f => if f.val = 110 then 0 else 0
                      else
                        fun f => if f.val = 97 then 0 else 0
                  else
                    if index < 1041 then
                      if index < 1040 then
                        fun f => if f.val = 118 then 0 else 0
                      else
                        fun f => if f.val = 129 then 0 else 0
                    else
                      if index < 1042 then
                        fun f => if f.val = 124 then 0 else 0
                      else
                        fun f => if f.val = 117 then 0 else 0
                else
                  if index < 1047 then
                    if index < 1045 then
                      if index < 1044 then
                        fun f => if f.val = 120 then 0 else 0
                      else
                        fun f => if f.val = 111 then 0 else 0
                    else
                      if index < 1046 then
                        fun f => if f.val = 128 then 0 else 0
                      else
                        fun f => if f.val = 126 then 0 else 0
                  else
                    if index < 1049 then
                      if index < 1048 then
                        fun f => if f.val = 106 then 0 else 0
                      else
                        fun f => if f.val = 115 then 0 else 0
                    else
                      if index < 1050 then
                        fun f => if f.val = 114 then 0 else 0
                      else
                        if index < 1051 then
                          fun f => if f.val = 102 then 0 else 0
                        else
                          fun f => if f.val = 103 then 0 else 0
              else
                if index < 1060 then
                  if index < 1056 then
                    if index < 1054 then
                      if index < 1053 then
                        fun f => if f.val = 107 then 0 else 0
                      else
                        fun f => if f.val = 105 then 0 else 0
                    else
                      if index < 1055 then
                        fun f => if f.val = 99 then 0 else 0
                      else
                        fun f => if f.val = 101 then 0 else 0
                  else
                    if index < 1058 then
                      if index < 1057 then
                        fun f => if f.val = 89 then 0 else 0
                      else
                        fun f => if f.val = 86 then 0 else 0
                    else
                      if index < 1059 then
                        fun f => if f.val = 113 then 0 else 0
                      else
                        fun f => if f.val = 109 then 0 else 0
                else
                  if index < 1064 then
                    if index < 1062 then
                      if index < 1061 then
                        fun f => if f.val = 122 then 0 else 0
                      else
                        fun f => if f.val = 94 then 0 else 0
                    else
                      if index < 1063 then
                        fun f => if f.val = 125 then 0 else 0
                      else
                        fun f => if f.val = 127 then 0 else 0
                  else
                    if index < 1066 then
                      if index < 1065 then
                        fun f => if f.val = 121 then 0 else 0
                      else
                        fun f => if f.val = 123 then 0 else 0
                    else
                      if index < 1067 then
                        fun f => if f.val = 108 then 0 else 0
                      else
                        if index < 1068 then
                          fun f => if f.val = 116 then 0 else 0
                        else
                          fun f => 0

private def cubeCofacetCode (i : Fin 1069) (f : Fin 130) : Fin 27 :=
  cubeCofacetCodeTable i.val f

private def cubeCofacetCertificate (i : Fin 1069) : Prop :=
  ∀ f ∈ cubeCofacets i, codeFace f (cubeCofacetCode i f) = i

-- This instance traverses the finite set, not the ambient type `Fin 130`.
private instance cubeCofacetCertificate_decidable (i : Fin 1069) :
    Decidable (cubeCofacetCertificate i) :=
  Finset.decidableDforallFinset

private theorem cubeCofacetCertificate_of_check (i : Fin 1069)
    (h : @decide (cubeCofacetCertificate i)
      (cubeCofacetCertificate_decidable i) = true) :
    cubeCofacetCertificate i :=
  @of_decide_eq_true (cubeCofacetCertificate i)
    (cubeCofacetCertificate_decidable i) h

private theorem cofacet0000 : cubeCofacetCertificate (⟨0, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0001 : cubeCofacetCertificate (⟨1, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0002 : cubeCofacetCertificate (⟨2, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0003 : cubeCofacetCertificate (⟨3, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0004 : cubeCofacetCertificate (⟨4, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0005 : cubeCofacetCertificate (⟨5, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0006 : cubeCofacetCertificate (⟨6, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0007 : cubeCofacetCertificate (⟨7, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0008 : cubeCofacetCertificate (⟨8, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0009 : cubeCofacetCertificate (⟨9, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0010 : cubeCofacetCertificate (⟨10, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0011 : cubeCofacetCertificate (⟨11, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0012 : cubeCofacetCertificate (⟨12, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0013 : cubeCofacetCertificate (⟨13, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0014 : cubeCofacetCertificate (⟨14, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0015 : cubeCofacetCertificate (⟨15, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0016 : cubeCofacetCertificate (⟨16, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0017 : cubeCofacetCertificate (⟨17, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0018 : cubeCofacetCertificate (⟨18, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0019 : cubeCofacetCertificate (⟨19, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0020 : cubeCofacetCertificate (⟨20, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0021 : cubeCofacetCertificate (⟨21, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0022 : cubeCofacetCertificate (⟨22, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0023 : cubeCofacetCertificate (⟨23, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0024 : cubeCofacetCertificate (⟨24, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0025 : cubeCofacetCertificate (⟨25, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0026 : cubeCofacetCertificate (⟨26, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0027 : cubeCofacetCertificate (⟨27, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0028 : cubeCofacetCertificate (⟨28, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0029 : cubeCofacetCertificate (⟨29, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0030 : cubeCofacetCertificate (⟨30, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0031 : cubeCofacetCertificate (⟨31, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0032 : cubeCofacetCertificate (⟨32, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0033 : cubeCofacetCertificate (⟨33, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0034 : cubeCofacetCertificate (⟨34, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0035 : cubeCofacetCertificate (⟨35, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0036 : cubeCofacetCertificate (⟨36, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0037 : cubeCofacetCertificate (⟨37, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0038 : cubeCofacetCertificate (⟨38, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0039 : cubeCofacetCertificate (⟨39, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0040 : cubeCofacetCertificate (⟨40, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0041 : cubeCofacetCertificate (⟨41, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0042 : cubeCofacetCertificate (⟨42, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0043 : cubeCofacetCertificate (⟨43, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0044 : cubeCofacetCertificate (⟨44, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0045 : cubeCofacetCertificate (⟨45, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0046 : cubeCofacetCertificate (⟨46, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0047 : cubeCofacetCertificate (⟨47, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0048 : cubeCofacetCertificate (⟨48, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0049 : cubeCofacetCertificate (⟨49, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0050 : cubeCofacetCertificate (⟨50, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0051 : cubeCofacetCertificate (⟨51, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0052 : cubeCofacetCertificate (⟨52, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0053 : cubeCofacetCertificate (⟨53, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0054 : cubeCofacetCertificate (⟨54, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0055 : cubeCofacetCertificate (⟨55, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0056 : cubeCofacetCertificate (⟨56, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0057 : cubeCofacetCertificate (⟨57, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0058 : cubeCofacetCertificate (⟨58, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0059 : cubeCofacetCertificate (⟨59, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0060 : cubeCofacetCertificate (⟨60, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0061 : cubeCofacetCertificate (⟨61, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0062 : cubeCofacetCertificate (⟨62, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0063 : cubeCofacetCertificate (⟨63, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0064 : cubeCofacetCertificate (⟨64, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0065 : cubeCofacetCertificate (⟨65, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0066 : cubeCofacetCertificate (⟨66, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0067 : cubeCofacetCertificate (⟨67, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0068 : cubeCofacetCertificate (⟨68, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0069 : cubeCofacetCertificate (⟨69, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0070 : cubeCofacetCertificate (⟨70, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0071 : cubeCofacetCertificate (⟨71, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0072 : cubeCofacetCertificate (⟨72, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0073 : cubeCofacetCertificate (⟨73, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0074 : cubeCofacetCertificate (⟨74, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0075 : cubeCofacetCertificate (⟨75, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0076 : cubeCofacetCertificate (⟨76, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0077 : cubeCofacetCertificate (⟨77, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0078 : cubeCofacetCertificate (⟨78, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0079 : cubeCofacetCertificate (⟨79, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0080 : cubeCofacetCertificate (⟨80, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0081 : cubeCofacetCertificate (⟨81, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0082 : cubeCofacetCertificate (⟨82, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0083 : cubeCofacetCertificate (⟨83, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0084 : cubeCofacetCertificate (⟨84, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0085 : cubeCofacetCertificate (⟨85, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0086 : cubeCofacetCertificate (⟨86, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0087 : cubeCofacetCertificate (⟨87, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0088 : cubeCofacetCertificate (⟨88, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0089 : cubeCofacetCertificate (⟨89, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0090 : cubeCofacetCertificate (⟨90, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0091 : cubeCofacetCertificate (⟨91, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0092 : cubeCofacetCertificate (⟨92, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0093 : cubeCofacetCertificate (⟨93, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0094 : cubeCofacetCertificate (⟨94, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0095 : cubeCofacetCertificate (⟨95, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0096 : cubeCofacetCertificate (⟨96, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0097 : cubeCofacetCertificate (⟨97, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0098 : cubeCofacetCertificate (⟨98, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0099 : cubeCofacetCertificate (⟨99, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0100 : cubeCofacetCertificate (⟨100, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0101 : cubeCofacetCertificate (⟨101, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0102 : cubeCofacetCertificate (⟨102, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0103 : cubeCofacetCertificate (⟨103, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0104 : cubeCofacetCertificate (⟨104, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0105 : cubeCofacetCertificate (⟨105, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0106 : cubeCofacetCertificate (⟨106, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0107 : cubeCofacetCertificate (⟨107, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0108 : cubeCofacetCertificate (⟨108, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0109 : cubeCofacetCertificate (⟨109, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0110 : cubeCofacetCertificate (⟨110, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0111 : cubeCofacetCertificate (⟨111, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0112 : cubeCofacetCertificate (⟨112, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0113 : cubeCofacetCertificate (⟨113, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0114 : cubeCofacetCertificate (⟨114, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0115 : cubeCofacetCertificate (⟨115, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0116 : cubeCofacetCertificate (⟨116, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0117 : cubeCofacetCertificate (⟨117, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0118 : cubeCofacetCertificate (⟨118, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0119 : cubeCofacetCertificate (⟨119, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0120 : cubeCofacetCertificate (⟨120, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0121 : cubeCofacetCertificate (⟨121, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0122 : cubeCofacetCertificate (⟨122, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0123 : cubeCofacetCertificate (⟨123, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0124 : cubeCofacetCertificate (⟨124, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0125 : cubeCofacetCertificate (⟨125, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0126 : cubeCofacetCertificate (⟨126, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0127 : cubeCofacetCertificate (⟨127, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0128 : cubeCofacetCertificate (⟨128, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0129 : cubeCofacetCertificate (⟨129, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0130 : cubeCofacetCertificate (⟨130, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0131 : cubeCofacetCertificate (⟨131, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0132 : cubeCofacetCertificate (⟨132, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0133 : cubeCofacetCertificate (⟨133, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0134 : cubeCofacetCertificate (⟨134, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0135 : cubeCofacetCertificate (⟨135, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0136 : cubeCofacetCertificate (⟨136, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0137 : cubeCofacetCertificate (⟨137, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0138 : cubeCofacetCertificate (⟨138, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0139 : cubeCofacetCertificate (⟨139, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0140 : cubeCofacetCertificate (⟨140, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0141 : cubeCofacetCertificate (⟨141, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0142 : cubeCofacetCertificate (⟨142, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0143 : cubeCofacetCertificate (⟨143, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0144 : cubeCofacetCertificate (⟨144, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0145 : cubeCofacetCertificate (⟨145, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0146 : cubeCofacetCertificate (⟨146, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0147 : cubeCofacetCertificate (⟨147, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0148 : cubeCofacetCertificate (⟨148, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0149 : cubeCofacetCertificate (⟨149, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0150 : cubeCofacetCertificate (⟨150, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0151 : cubeCofacetCertificate (⟨151, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0152 : cubeCofacetCertificate (⟨152, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0153 : cubeCofacetCertificate (⟨153, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0154 : cubeCofacetCertificate (⟨154, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0155 : cubeCofacetCertificate (⟨155, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0156 : cubeCofacetCertificate (⟨156, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0157 : cubeCofacetCertificate (⟨157, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0158 : cubeCofacetCertificate (⟨158, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0159 : cubeCofacetCertificate (⟨159, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0160 : cubeCofacetCertificate (⟨160, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0161 : cubeCofacetCertificate (⟨161, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0162 : cubeCofacetCertificate (⟨162, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0163 : cubeCofacetCertificate (⟨163, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0164 : cubeCofacetCertificate (⟨164, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0165 : cubeCofacetCertificate (⟨165, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0166 : cubeCofacetCertificate (⟨166, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0167 : cubeCofacetCertificate (⟨167, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0168 : cubeCofacetCertificate (⟨168, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0169 : cubeCofacetCertificate (⟨169, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0170 : cubeCofacetCertificate (⟨170, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0171 : cubeCofacetCertificate (⟨171, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0172 : cubeCofacetCertificate (⟨172, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0173 : cubeCofacetCertificate (⟨173, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0174 : cubeCofacetCertificate (⟨174, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0175 : cubeCofacetCertificate (⟨175, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0176 : cubeCofacetCertificate (⟨176, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0177 : cubeCofacetCertificate (⟨177, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0178 : cubeCofacetCertificate (⟨178, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0179 : cubeCofacetCertificate (⟨179, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0180 : cubeCofacetCertificate (⟨180, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0181 : cubeCofacetCertificate (⟨181, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0182 : cubeCofacetCertificate (⟨182, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0183 : cubeCofacetCertificate (⟨183, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0184 : cubeCofacetCertificate (⟨184, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0185 : cubeCofacetCertificate (⟨185, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0186 : cubeCofacetCertificate (⟨186, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0187 : cubeCofacetCertificate (⟨187, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0188 : cubeCofacetCertificate (⟨188, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0189 : cubeCofacetCertificate (⟨189, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0190 : cubeCofacetCertificate (⟨190, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0191 : cubeCofacetCertificate (⟨191, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0192 : cubeCofacetCertificate (⟨192, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0193 : cubeCofacetCertificate (⟨193, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0194 : cubeCofacetCertificate (⟨194, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0195 : cubeCofacetCertificate (⟨195, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0196 : cubeCofacetCertificate (⟨196, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0197 : cubeCofacetCertificate (⟨197, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0198 : cubeCofacetCertificate (⟨198, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0199 : cubeCofacetCertificate (⟨199, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0200 : cubeCofacetCertificate (⟨200, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0201 : cubeCofacetCertificate (⟨201, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0202 : cubeCofacetCertificate (⟨202, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0203 : cubeCofacetCertificate (⟨203, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0204 : cubeCofacetCertificate (⟨204, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0205 : cubeCofacetCertificate (⟨205, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0206 : cubeCofacetCertificate (⟨206, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0207 : cubeCofacetCertificate (⟨207, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0208 : cubeCofacetCertificate (⟨208, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0209 : cubeCofacetCertificate (⟨209, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0210 : cubeCofacetCertificate (⟨210, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0211 : cubeCofacetCertificate (⟨211, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0212 : cubeCofacetCertificate (⟨212, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0213 : cubeCofacetCertificate (⟨213, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0214 : cubeCofacetCertificate (⟨214, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0215 : cubeCofacetCertificate (⟨215, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0216 : cubeCofacetCertificate (⟨216, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0217 : cubeCofacetCertificate (⟨217, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0218 : cubeCofacetCertificate (⟨218, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0219 : cubeCofacetCertificate (⟨219, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0220 : cubeCofacetCertificate (⟨220, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0221 : cubeCofacetCertificate (⟨221, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0222 : cubeCofacetCertificate (⟨222, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0223 : cubeCofacetCertificate (⟨223, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0224 : cubeCofacetCertificate (⟨224, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0225 : cubeCofacetCertificate (⟨225, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0226 : cubeCofacetCertificate (⟨226, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0227 : cubeCofacetCertificate (⟨227, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0228 : cubeCofacetCertificate (⟨228, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0229 : cubeCofacetCertificate (⟨229, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0230 : cubeCofacetCertificate (⟨230, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0231 : cubeCofacetCertificate (⟨231, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0232 : cubeCofacetCertificate (⟨232, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0233 : cubeCofacetCertificate (⟨233, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0234 : cubeCofacetCertificate (⟨234, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0235 : cubeCofacetCertificate (⟨235, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0236 : cubeCofacetCertificate (⟨236, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0237 : cubeCofacetCertificate (⟨237, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0238 : cubeCofacetCertificate (⟨238, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0239 : cubeCofacetCertificate (⟨239, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0240 : cubeCofacetCertificate (⟨240, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0241 : cubeCofacetCertificate (⟨241, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0242 : cubeCofacetCertificate (⟨242, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0243 : cubeCofacetCertificate (⟨243, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0244 : cubeCofacetCertificate (⟨244, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0245 : cubeCofacetCertificate (⟨245, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0246 : cubeCofacetCertificate (⟨246, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0247 : cubeCofacetCertificate (⟨247, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0248 : cubeCofacetCertificate (⟨248, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0249 : cubeCofacetCertificate (⟨249, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0250 : cubeCofacetCertificate (⟨250, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0251 : cubeCofacetCertificate (⟨251, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0252 : cubeCofacetCertificate (⟨252, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0253 : cubeCofacetCertificate (⟨253, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0254 : cubeCofacetCertificate (⟨254, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0255 : cubeCofacetCertificate (⟨255, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0256 : cubeCofacetCertificate (⟨256, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0257 : cubeCofacetCertificate (⟨257, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0258 : cubeCofacetCertificate (⟨258, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0259 : cubeCofacetCertificate (⟨259, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0260 : cubeCofacetCertificate (⟨260, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0261 : cubeCofacetCertificate (⟨261, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0262 : cubeCofacetCertificate (⟨262, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0263 : cubeCofacetCertificate (⟨263, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0264 : cubeCofacetCertificate (⟨264, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0265 : cubeCofacetCertificate (⟨265, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0266 : cubeCofacetCertificate (⟨266, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0267 : cubeCofacetCertificate (⟨267, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0268 : cubeCofacetCertificate (⟨268, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0269 : cubeCofacetCertificate (⟨269, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0270 : cubeCofacetCertificate (⟨270, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0271 : cubeCofacetCertificate (⟨271, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0272 : cubeCofacetCertificate (⟨272, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0273 : cubeCofacetCertificate (⟨273, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0274 : cubeCofacetCertificate (⟨274, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0275 : cubeCofacetCertificate (⟨275, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0276 : cubeCofacetCertificate (⟨276, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0277 : cubeCofacetCertificate (⟨277, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0278 : cubeCofacetCertificate (⟨278, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0279 : cubeCofacetCertificate (⟨279, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0280 : cubeCofacetCertificate (⟨280, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0281 : cubeCofacetCertificate (⟨281, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0282 : cubeCofacetCertificate (⟨282, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0283 : cubeCofacetCertificate (⟨283, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0284 : cubeCofacetCertificate (⟨284, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0285 : cubeCofacetCertificate (⟨285, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0286 : cubeCofacetCertificate (⟨286, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0287 : cubeCofacetCertificate (⟨287, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0288 : cubeCofacetCertificate (⟨288, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0289 : cubeCofacetCertificate (⟨289, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0290 : cubeCofacetCertificate (⟨290, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0291 : cubeCofacetCertificate (⟨291, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0292 : cubeCofacetCertificate (⟨292, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0293 : cubeCofacetCertificate (⟨293, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0294 : cubeCofacetCertificate (⟨294, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0295 : cubeCofacetCertificate (⟨295, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0296 : cubeCofacetCertificate (⟨296, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0297 : cubeCofacetCertificate (⟨297, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0298 : cubeCofacetCertificate (⟨298, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0299 : cubeCofacetCertificate (⟨299, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0300 : cubeCofacetCertificate (⟨300, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0301 : cubeCofacetCertificate (⟨301, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0302 : cubeCofacetCertificate (⟨302, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0303 : cubeCofacetCertificate (⟨303, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0304 : cubeCofacetCertificate (⟨304, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0305 : cubeCofacetCertificate (⟨305, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0306 : cubeCofacetCertificate (⟨306, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0307 : cubeCofacetCertificate (⟨307, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0308 : cubeCofacetCertificate (⟨308, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0309 : cubeCofacetCertificate (⟨309, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0310 : cubeCofacetCertificate (⟨310, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0311 : cubeCofacetCertificate (⟨311, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0312 : cubeCofacetCertificate (⟨312, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0313 : cubeCofacetCertificate (⟨313, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0314 : cubeCofacetCertificate (⟨314, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0315 : cubeCofacetCertificate (⟨315, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0316 : cubeCofacetCertificate (⟨316, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0317 : cubeCofacetCertificate (⟨317, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0318 : cubeCofacetCertificate (⟨318, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0319 : cubeCofacetCertificate (⟨319, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0320 : cubeCofacetCertificate (⟨320, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0321 : cubeCofacetCertificate (⟨321, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0322 : cubeCofacetCertificate (⟨322, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0323 : cubeCofacetCertificate (⟨323, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0324 : cubeCofacetCertificate (⟨324, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0325 : cubeCofacetCertificate (⟨325, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0326 : cubeCofacetCertificate (⟨326, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0327 : cubeCofacetCertificate (⟨327, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0328 : cubeCofacetCertificate (⟨328, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0329 : cubeCofacetCertificate (⟨329, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0330 : cubeCofacetCertificate (⟨330, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0331 : cubeCofacetCertificate (⟨331, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0332 : cubeCofacetCertificate (⟨332, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0333 : cubeCofacetCertificate (⟨333, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0334 : cubeCofacetCertificate (⟨334, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0335 : cubeCofacetCertificate (⟨335, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0336 : cubeCofacetCertificate (⟨336, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0337 : cubeCofacetCertificate (⟨337, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0338 : cubeCofacetCertificate (⟨338, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0339 : cubeCofacetCertificate (⟨339, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0340 : cubeCofacetCertificate (⟨340, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0341 : cubeCofacetCertificate (⟨341, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0342 : cubeCofacetCertificate (⟨342, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0343 : cubeCofacetCertificate (⟨343, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0344 : cubeCofacetCertificate (⟨344, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0345 : cubeCofacetCertificate (⟨345, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0346 : cubeCofacetCertificate (⟨346, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0347 : cubeCofacetCertificate (⟨347, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0348 : cubeCofacetCertificate (⟨348, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0349 : cubeCofacetCertificate (⟨349, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0350 : cubeCofacetCertificate (⟨350, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0351 : cubeCofacetCertificate (⟨351, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0352 : cubeCofacetCertificate (⟨352, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0353 : cubeCofacetCertificate (⟨353, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0354 : cubeCofacetCertificate (⟨354, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0355 : cubeCofacetCertificate (⟨355, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0356 : cubeCofacetCertificate (⟨356, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0357 : cubeCofacetCertificate (⟨357, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0358 : cubeCofacetCertificate (⟨358, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0359 : cubeCofacetCertificate (⟨359, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0360 : cubeCofacetCertificate (⟨360, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0361 : cubeCofacetCertificate (⟨361, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0362 : cubeCofacetCertificate (⟨362, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0363 : cubeCofacetCertificate (⟨363, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0364 : cubeCofacetCertificate (⟨364, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0365 : cubeCofacetCertificate (⟨365, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0366 : cubeCofacetCertificate (⟨366, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0367 : cubeCofacetCertificate (⟨367, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0368 : cubeCofacetCertificate (⟨368, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0369 : cubeCofacetCertificate (⟨369, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0370 : cubeCofacetCertificate (⟨370, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0371 : cubeCofacetCertificate (⟨371, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0372 : cubeCofacetCertificate (⟨372, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0373 : cubeCofacetCertificate (⟨373, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0374 : cubeCofacetCertificate (⟨374, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0375 : cubeCofacetCertificate (⟨375, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0376 : cubeCofacetCertificate (⟨376, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0377 : cubeCofacetCertificate (⟨377, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0378 : cubeCofacetCertificate (⟨378, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0379 : cubeCofacetCertificate (⟨379, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0380 : cubeCofacetCertificate (⟨380, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0381 : cubeCofacetCertificate (⟨381, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0382 : cubeCofacetCertificate (⟨382, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0383 : cubeCofacetCertificate (⟨383, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0384 : cubeCofacetCertificate (⟨384, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0385 : cubeCofacetCertificate (⟨385, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0386 : cubeCofacetCertificate (⟨386, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0387 : cubeCofacetCertificate (⟨387, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0388 : cubeCofacetCertificate (⟨388, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0389 : cubeCofacetCertificate (⟨389, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0390 : cubeCofacetCertificate (⟨390, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0391 : cubeCofacetCertificate (⟨391, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0392 : cubeCofacetCertificate (⟨392, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0393 : cubeCofacetCertificate (⟨393, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0394 : cubeCofacetCertificate (⟨394, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0395 : cubeCofacetCertificate (⟨395, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0396 : cubeCofacetCertificate (⟨396, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0397 : cubeCofacetCertificate (⟨397, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0398 : cubeCofacetCertificate (⟨398, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0399 : cubeCofacetCertificate (⟨399, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0400 : cubeCofacetCertificate (⟨400, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0401 : cubeCofacetCertificate (⟨401, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0402 : cubeCofacetCertificate (⟨402, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0403 : cubeCofacetCertificate (⟨403, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0404 : cubeCofacetCertificate (⟨404, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0405 : cubeCofacetCertificate (⟨405, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0406 : cubeCofacetCertificate (⟨406, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0407 : cubeCofacetCertificate (⟨407, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0408 : cubeCofacetCertificate (⟨408, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0409 : cubeCofacetCertificate (⟨409, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0410 : cubeCofacetCertificate (⟨410, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0411 : cubeCofacetCertificate (⟨411, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0412 : cubeCofacetCertificate (⟨412, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0413 : cubeCofacetCertificate (⟨413, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0414 : cubeCofacetCertificate (⟨414, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0415 : cubeCofacetCertificate (⟨415, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0416 : cubeCofacetCertificate (⟨416, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0417 : cubeCofacetCertificate (⟨417, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0418 : cubeCofacetCertificate (⟨418, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0419 : cubeCofacetCertificate (⟨419, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0420 : cubeCofacetCertificate (⟨420, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0421 : cubeCofacetCertificate (⟨421, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0422 : cubeCofacetCertificate (⟨422, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0423 : cubeCofacetCertificate (⟨423, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0424 : cubeCofacetCertificate (⟨424, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0425 : cubeCofacetCertificate (⟨425, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0426 : cubeCofacetCertificate (⟨426, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0427 : cubeCofacetCertificate (⟨427, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0428 : cubeCofacetCertificate (⟨428, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0429 : cubeCofacetCertificate (⟨429, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0430 : cubeCofacetCertificate (⟨430, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0431 : cubeCofacetCertificate (⟨431, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0432 : cubeCofacetCertificate (⟨432, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0433 : cubeCofacetCertificate (⟨433, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0434 : cubeCofacetCertificate (⟨434, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0435 : cubeCofacetCertificate (⟨435, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0436 : cubeCofacetCertificate (⟨436, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0437 : cubeCofacetCertificate (⟨437, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0438 : cubeCofacetCertificate (⟨438, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0439 : cubeCofacetCertificate (⟨439, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0440 : cubeCofacetCertificate (⟨440, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0441 : cubeCofacetCertificate (⟨441, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0442 : cubeCofacetCertificate (⟨442, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0443 : cubeCofacetCertificate (⟨443, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0444 : cubeCofacetCertificate (⟨444, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0445 : cubeCofacetCertificate (⟨445, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0446 : cubeCofacetCertificate (⟨446, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0447 : cubeCofacetCertificate (⟨447, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0448 : cubeCofacetCertificate (⟨448, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0449 : cubeCofacetCertificate (⟨449, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0450 : cubeCofacetCertificate (⟨450, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0451 : cubeCofacetCertificate (⟨451, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0452 : cubeCofacetCertificate (⟨452, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0453 : cubeCofacetCertificate (⟨453, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0454 : cubeCofacetCertificate (⟨454, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0455 : cubeCofacetCertificate (⟨455, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0456 : cubeCofacetCertificate (⟨456, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0457 : cubeCofacetCertificate (⟨457, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0458 : cubeCofacetCertificate (⟨458, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0459 : cubeCofacetCertificate (⟨459, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0460 : cubeCofacetCertificate (⟨460, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0461 : cubeCofacetCertificate (⟨461, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0462 : cubeCofacetCertificate (⟨462, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0463 : cubeCofacetCertificate (⟨463, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0464 : cubeCofacetCertificate (⟨464, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0465 : cubeCofacetCertificate (⟨465, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0466 : cubeCofacetCertificate (⟨466, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0467 : cubeCofacetCertificate (⟨467, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0468 : cubeCofacetCertificate (⟨468, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0469 : cubeCofacetCertificate (⟨469, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0470 : cubeCofacetCertificate (⟨470, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0471 : cubeCofacetCertificate (⟨471, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0472 : cubeCofacetCertificate (⟨472, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0473 : cubeCofacetCertificate (⟨473, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0474 : cubeCofacetCertificate (⟨474, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0475 : cubeCofacetCertificate (⟨475, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0476 : cubeCofacetCertificate (⟨476, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0477 : cubeCofacetCertificate (⟨477, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0478 : cubeCofacetCertificate (⟨478, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0479 : cubeCofacetCertificate (⟨479, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0480 : cubeCofacetCertificate (⟨480, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0481 : cubeCofacetCertificate (⟨481, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0482 : cubeCofacetCertificate (⟨482, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0483 : cubeCofacetCertificate (⟨483, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0484 : cubeCofacetCertificate (⟨484, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0485 : cubeCofacetCertificate (⟨485, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0486 : cubeCofacetCertificate (⟨486, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0487 : cubeCofacetCertificate (⟨487, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0488 : cubeCofacetCertificate (⟨488, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0489 : cubeCofacetCertificate (⟨489, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0490 : cubeCofacetCertificate (⟨490, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0491 : cubeCofacetCertificate (⟨491, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0492 : cubeCofacetCertificate (⟨492, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0493 : cubeCofacetCertificate (⟨493, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0494 : cubeCofacetCertificate (⟨494, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0495 : cubeCofacetCertificate (⟨495, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0496 : cubeCofacetCertificate (⟨496, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0497 : cubeCofacetCertificate (⟨497, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0498 : cubeCofacetCertificate (⟨498, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0499 : cubeCofacetCertificate (⟨499, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0500 : cubeCofacetCertificate (⟨500, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0501 : cubeCofacetCertificate (⟨501, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0502 : cubeCofacetCertificate (⟨502, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0503 : cubeCofacetCertificate (⟨503, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0504 : cubeCofacetCertificate (⟨504, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0505 : cubeCofacetCertificate (⟨505, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0506 : cubeCofacetCertificate (⟨506, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0507 : cubeCofacetCertificate (⟨507, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0508 : cubeCofacetCertificate (⟨508, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0509 : cubeCofacetCertificate (⟨509, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0510 : cubeCofacetCertificate (⟨510, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0511 : cubeCofacetCertificate (⟨511, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0512 : cubeCofacetCertificate (⟨512, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0513 : cubeCofacetCertificate (⟨513, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0514 : cubeCofacetCertificate (⟨514, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0515 : cubeCofacetCertificate (⟨515, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0516 : cubeCofacetCertificate (⟨516, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0517 : cubeCofacetCertificate (⟨517, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0518 : cubeCofacetCertificate (⟨518, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0519 : cubeCofacetCertificate (⟨519, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0520 : cubeCofacetCertificate (⟨520, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0521 : cubeCofacetCertificate (⟨521, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0522 : cubeCofacetCertificate (⟨522, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0523 : cubeCofacetCertificate (⟨523, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0524 : cubeCofacetCertificate (⟨524, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0525 : cubeCofacetCertificate (⟨525, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0526 : cubeCofacetCertificate (⟨526, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0527 : cubeCofacetCertificate (⟨527, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0528 : cubeCofacetCertificate (⟨528, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0529 : cubeCofacetCertificate (⟨529, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0530 : cubeCofacetCertificate (⟨530, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0531 : cubeCofacetCertificate (⟨531, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0532 : cubeCofacetCertificate (⟨532, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0533 : cubeCofacetCertificate (⟨533, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0534 : cubeCofacetCertificate (⟨534, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0535 : cubeCofacetCertificate (⟨535, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0536 : cubeCofacetCertificate (⟨536, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0537 : cubeCofacetCertificate (⟨537, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0538 : cubeCofacetCertificate (⟨538, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0539 : cubeCofacetCertificate (⟨539, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0540 : cubeCofacetCertificate (⟨540, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0541 : cubeCofacetCertificate (⟨541, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0542 : cubeCofacetCertificate (⟨542, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0543 : cubeCofacetCertificate (⟨543, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0544 : cubeCofacetCertificate (⟨544, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0545 : cubeCofacetCertificate (⟨545, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0546 : cubeCofacetCertificate (⟨546, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0547 : cubeCofacetCertificate (⟨547, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0548 : cubeCofacetCertificate (⟨548, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0549 : cubeCofacetCertificate (⟨549, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0550 : cubeCofacetCertificate (⟨550, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0551 : cubeCofacetCertificate (⟨551, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0552 : cubeCofacetCertificate (⟨552, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0553 : cubeCofacetCertificate (⟨553, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0554 : cubeCofacetCertificate (⟨554, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0555 : cubeCofacetCertificate (⟨555, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0556 : cubeCofacetCertificate (⟨556, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0557 : cubeCofacetCertificate (⟨557, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0558 : cubeCofacetCertificate (⟨558, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0559 : cubeCofacetCertificate (⟨559, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0560 : cubeCofacetCertificate (⟨560, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0561 : cubeCofacetCertificate (⟨561, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0562 : cubeCofacetCertificate (⟨562, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0563 : cubeCofacetCertificate (⟨563, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0564 : cubeCofacetCertificate (⟨564, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0565 : cubeCofacetCertificate (⟨565, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0566 : cubeCofacetCertificate (⟨566, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0567 : cubeCofacetCertificate (⟨567, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0568 : cubeCofacetCertificate (⟨568, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0569 : cubeCofacetCertificate (⟨569, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0570 : cubeCofacetCertificate (⟨570, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0571 : cubeCofacetCertificate (⟨571, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0572 : cubeCofacetCertificate (⟨572, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0573 : cubeCofacetCertificate (⟨573, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0574 : cubeCofacetCertificate (⟨574, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0575 : cubeCofacetCertificate (⟨575, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0576 : cubeCofacetCertificate (⟨576, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0577 : cubeCofacetCertificate (⟨577, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0578 : cubeCofacetCertificate (⟨578, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0579 : cubeCofacetCertificate (⟨579, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0580 : cubeCofacetCertificate (⟨580, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0581 : cubeCofacetCertificate (⟨581, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0582 : cubeCofacetCertificate (⟨582, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0583 : cubeCofacetCertificate (⟨583, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0584 : cubeCofacetCertificate (⟨584, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0585 : cubeCofacetCertificate (⟨585, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0586 : cubeCofacetCertificate (⟨586, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0587 : cubeCofacetCertificate (⟨587, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0588 : cubeCofacetCertificate (⟨588, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0589 : cubeCofacetCertificate (⟨589, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0590 : cubeCofacetCertificate (⟨590, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0591 : cubeCofacetCertificate (⟨591, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0592 : cubeCofacetCertificate (⟨592, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0593 : cubeCofacetCertificate (⟨593, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0594 : cubeCofacetCertificate (⟨594, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0595 : cubeCofacetCertificate (⟨595, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0596 : cubeCofacetCertificate (⟨596, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0597 : cubeCofacetCertificate (⟨597, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0598 : cubeCofacetCertificate (⟨598, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0599 : cubeCofacetCertificate (⟨599, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0600 : cubeCofacetCertificate (⟨600, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0601 : cubeCofacetCertificate (⟨601, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0602 : cubeCofacetCertificate (⟨602, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0603 : cubeCofacetCertificate (⟨603, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0604 : cubeCofacetCertificate (⟨604, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0605 : cubeCofacetCertificate (⟨605, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0606 : cubeCofacetCertificate (⟨606, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0607 : cubeCofacetCertificate (⟨607, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0608 : cubeCofacetCertificate (⟨608, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0609 : cubeCofacetCertificate (⟨609, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0610 : cubeCofacetCertificate (⟨610, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0611 : cubeCofacetCertificate (⟨611, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0612 : cubeCofacetCertificate (⟨612, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0613 : cubeCofacetCertificate (⟨613, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0614 : cubeCofacetCertificate (⟨614, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0615 : cubeCofacetCertificate (⟨615, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0616 : cubeCofacetCertificate (⟨616, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0617 : cubeCofacetCertificate (⟨617, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0618 : cubeCofacetCertificate (⟨618, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0619 : cubeCofacetCertificate (⟨619, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0620 : cubeCofacetCertificate (⟨620, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0621 : cubeCofacetCertificate (⟨621, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0622 : cubeCofacetCertificate (⟨622, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0623 : cubeCofacetCertificate (⟨623, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0624 : cubeCofacetCertificate (⟨624, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0625 : cubeCofacetCertificate (⟨625, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0626 : cubeCofacetCertificate (⟨626, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0627 : cubeCofacetCertificate (⟨627, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0628 : cubeCofacetCertificate (⟨628, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0629 : cubeCofacetCertificate (⟨629, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0630 : cubeCofacetCertificate (⟨630, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0631 : cubeCofacetCertificate (⟨631, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0632 : cubeCofacetCertificate (⟨632, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0633 : cubeCofacetCertificate (⟨633, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0634 : cubeCofacetCertificate (⟨634, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0635 : cubeCofacetCertificate (⟨635, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0636 : cubeCofacetCertificate (⟨636, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0637 : cubeCofacetCertificate (⟨637, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0638 : cubeCofacetCertificate (⟨638, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0639 : cubeCofacetCertificate (⟨639, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0640 : cubeCofacetCertificate (⟨640, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0641 : cubeCofacetCertificate (⟨641, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0642 : cubeCofacetCertificate (⟨642, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0643 : cubeCofacetCertificate (⟨643, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0644 : cubeCofacetCertificate (⟨644, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0645 : cubeCofacetCertificate (⟨645, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0646 : cubeCofacetCertificate (⟨646, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0647 : cubeCofacetCertificate (⟨647, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0648 : cubeCofacetCertificate (⟨648, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0649 : cubeCofacetCertificate (⟨649, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0650 : cubeCofacetCertificate (⟨650, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0651 : cubeCofacetCertificate (⟨651, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0652 : cubeCofacetCertificate (⟨652, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0653 : cubeCofacetCertificate (⟨653, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0654 : cubeCofacetCertificate (⟨654, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0655 : cubeCofacetCertificate (⟨655, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0656 : cubeCofacetCertificate (⟨656, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0657 : cubeCofacetCertificate (⟨657, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0658 : cubeCofacetCertificate (⟨658, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0659 : cubeCofacetCertificate (⟨659, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0660 : cubeCofacetCertificate (⟨660, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0661 : cubeCofacetCertificate (⟨661, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0662 : cubeCofacetCertificate (⟨662, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0663 : cubeCofacetCertificate (⟨663, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0664 : cubeCofacetCertificate (⟨664, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0665 : cubeCofacetCertificate (⟨665, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0666 : cubeCofacetCertificate (⟨666, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0667 : cubeCofacetCertificate (⟨667, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0668 : cubeCofacetCertificate (⟨668, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0669 : cubeCofacetCertificate (⟨669, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0670 : cubeCofacetCertificate (⟨670, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0671 : cubeCofacetCertificate (⟨671, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0672 : cubeCofacetCertificate (⟨672, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0673 : cubeCofacetCertificate (⟨673, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0674 : cubeCofacetCertificate (⟨674, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0675 : cubeCofacetCertificate (⟨675, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0676 : cubeCofacetCertificate (⟨676, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0677 : cubeCofacetCertificate (⟨677, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0678 : cubeCofacetCertificate (⟨678, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0679 : cubeCofacetCertificate (⟨679, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0680 : cubeCofacetCertificate (⟨680, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0681 : cubeCofacetCertificate (⟨681, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0682 : cubeCofacetCertificate (⟨682, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0683 : cubeCofacetCertificate (⟨683, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0684 : cubeCofacetCertificate (⟨684, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0685 : cubeCofacetCertificate (⟨685, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0686 : cubeCofacetCertificate (⟨686, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0687 : cubeCofacetCertificate (⟨687, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0688 : cubeCofacetCertificate (⟨688, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0689 : cubeCofacetCertificate (⟨689, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0690 : cubeCofacetCertificate (⟨690, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0691 : cubeCofacetCertificate (⟨691, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0692 : cubeCofacetCertificate (⟨692, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0693 : cubeCofacetCertificate (⟨693, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0694 : cubeCofacetCertificate (⟨694, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0695 : cubeCofacetCertificate (⟨695, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0696 : cubeCofacetCertificate (⟨696, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0697 : cubeCofacetCertificate (⟨697, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0698 : cubeCofacetCertificate (⟨698, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0699 : cubeCofacetCertificate (⟨699, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0700 : cubeCofacetCertificate (⟨700, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0701 : cubeCofacetCertificate (⟨701, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0702 : cubeCofacetCertificate (⟨702, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0703 : cubeCofacetCertificate (⟨703, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0704 : cubeCofacetCertificate (⟨704, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0705 : cubeCofacetCertificate (⟨705, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0706 : cubeCofacetCertificate (⟨706, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0707 : cubeCofacetCertificate (⟨707, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0708 : cubeCofacetCertificate (⟨708, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0709 : cubeCofacetCertificate (⟨709, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0710 : cubeCofacetCertificate (⟨710, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0711 : cubeCofacetCertificate (⟨711, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0712 : cubeCofacetCertificate (⟨712, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0713 : cubeCofacetCertificate (⟨713, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0714 : cubeCofacetCertificate (⟨714, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0715 : cubeCofacetCertificate (⟨715, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0716 : cubeCofacetCertificate (⟨716, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0717 : cubeCofacetCertificate (⟨717, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0718 : cubeCofacetCertificate (⟨718, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0719 : cubeCofacetCertificate (⟨719, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0720 : cubeCofacetCertificate (⟨720, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0721 : cubeCofacetCertificate (⟨721, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0722 : cubeCofacetCertificate (⟨722, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0723 : cubeCofacetCertificate (⟨723, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0724 : cubeCofacetCertificate (⟨724, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0725 : cubeCofacetCertificate (⟨725, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0726 : cubeCofacetCertificate (⟨726, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0727 : cubeCofacetCertificate (⟨727, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0728 : cubeCofacetCertificate (⟨728, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0729 : cubeCofacetCertificate (⟨729, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0730 : cubeCofacetCertificate (⟨730, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0731 : cubeCofacetCertificate (⟨731, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0732 : cubeCofacetCertificate (⟨732, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0733 : cubeCofacetCertificate (⟨733, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0734 : cubeCofacetCertificate (⟨734, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0735 : cubeCofacetCertificate (⟨735, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0736 : cubeCofacetCertificate (⟨736, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0737 : cubeCofacetCertificate (⟨737, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0738 : cubeCofacetCertificate (⟨738, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0739 : cubeCofacetCertificate (⟨739, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0740 : cubeCofacetCertificate (⟨740, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0741 : cubeCofacetCertificate (⟨741, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0742 : cubeCofacetCertificate (⟨742, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0743 : cubeCofacetCertificate (⟨743, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0744 : cubeCofacetCertificate (⟨744, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0745 : cubeCofacetCertificate (⟨745, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0746 : cubeCofacetCertificate (⟨746, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0747 : cubeCofacetCertificate (⟨747, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0748 : cubeCofacetCertificate (⟨748, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0749 : cubeCofacetCertificate (⟨749, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0750 : cubeCofacetCertificate (⟨750, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0751 : cubeCofacetCertificate (⟨751, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0752 : cubeCofacetCertificate (⟨752, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0753 : cubeCofacetCertificate (⟨753, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0754 : cubeCofacetCertificate (⟨754, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0755 : cubeCofacetCertificate (⟨755, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0756 : cubeCofacetCertificate (⟨756, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0757 : cubeCofacetCertificate (⟨757, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0758 : cubeCofacetCertificate (⟨758, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0759 : cubeCofacetCertificate (⟨759, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0760 : cubeCofacetCertificate (⟨760, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0761 : cubeCofacetCertificate (⟨761, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0762 : cubeCofacetCertificate (⟨762, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0763 : cubeCofacetCertificate (⟨763, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0764 : cubeCofacetCertificate (⟨764, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0765 : cubeCofacetCertificate (⟨765, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0766 : cubeCofacetCertificate (⟨766, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0767 : cubeCofacetCertificate (⟨767, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0768 : cubeCofacetCertificate (⟨768, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0769 : cubeCofacetCertificate (⟨769, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0770 : cubeCofacetCertificate (⟨770, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0771 : cubeCofacetCertificate (⟨771, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0772 : cubeCofacetCertificate (⟨772, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0773 : cubeCofacetCertificate (⟨773, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0774 : cubeCofacetCertificate (⟨774, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0775 : cubeCofacetCertificate (⟨775, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0776 : cubeCofacetCertificate (⟨776, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0777 : cubeCofacetCertificate (⟨777, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0778 : cubeCofacetCertificate (⟨778, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0779 : cubeCofacetCertificate (⟨779, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0780 : cubeCofacetCertificate (⟨780, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0781 : cubeCofacetCertificate (⟨781, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0782 : cubeCofacetCertificate (⟨782, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0783 : cubeCofacetCertificate (⟨783, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0784 : cubeCofacetCertificate (⟨784, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0785 : cubeCofacetCertificate (⟨785, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0786 : cubeCofacetCertificate (⟨786, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0787 : cubeCofacetCertificate (⟨787, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0788 : cubeCofacetCertificate (⟨788, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0789 : cubeCofacetCertificate (⟨789, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0790 : cubeCofacetCertificate (⟨790, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0791 : cubeCofacetCertificate (⟨791, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0792 : cubeCofacetCertificate (⟨792, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0793 : cubeCofacetCertificate (⟨793, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0794 : cubeCofacetCertificate (⟨794, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0795 : cubeCofacetCertificate (⟨795, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0796 : cubeCofacetCertificate (⟨796, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0797 : cubeCofacetCertificate (⟨797, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0798 : cubeCofacetCertificate (⟨798, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0799 : cubeCofacetCertificate (⟨799, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0800 : cubeCofacetCertificate (⟨800, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0801 : cubeCofacetCertificate (⟨801, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0802 : cubeCofacetCertificate (⟨802, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0803 : cubeCofacetCertificate (⟨803, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0804 : cubeCofacetCertificate (⟨804, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0805 : cubeCofacetCertificate (⟨805, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0806 : cubeCofacetCertificate (⟨806, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0807 : cubeCofacetCertificate (⟨807, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0808 : cubeCofacetCertificate (⟨808, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0809 : cubeCofacetCertificate (⟨809, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0810 : cubeCofacetCertificate (⟨810, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0811 : cubeCofacetCertificate (⟨811, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0812 : cubeCofacetCertificate (⟨812, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0813 : cubeCofacetCertificate (⟨813, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0814 : cubeCofacetCertificate (⟨814, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0815 : cubeCofacetCertificate (⟨815, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0816 : cubeCofacetCertificate (⟨816, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0817 : cubeCofacetCertificate (⟨817, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0818 : cubeCofacetCertificate (⟨818, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0819 : cubeCofacetCertificate (⟨819, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0820 : cubeCofacetCertificate (⟨820, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0821 : cubeCofacetCertificate (⟨821, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0822 : cubeCofacetCertificate (⟨822, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0823 : cubeCofacetCertificate (⟨823, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0824 : cubeCofacetCertificate (⟨824, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0825 : cubeCofacetCertificate (⟨825, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0826 : cubeCofacetCertificate (⟨826, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0827 : cubeCofacetCertificate (⟨827, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0828 : cubeCofacetCertificate (⟨828, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0829 : cubeCofacetCertificate (⟨829, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0830 : cubeCofacetCertificate (⟨830, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0831 : cubeCofacetCertificate (⟨831, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0832 : cubeCofacetCertificate (⟨832, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0833 : cubeCofacetCertificate (⟨833, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0834 : cubeCofacetCertificate (⟨834, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0835 : cubeCofacetCertificate (⟨835, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0836 : cubeCofacetCertificate (⟨836, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0837 : cubeCofacetCertificate (⟨837, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0838 : cubeCofacetCertificate (⟨838, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0839 : cubeCofacetCertificate (⟨839, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0840 : cubeCofacetCertificate (⟨840, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0841 : cubeCofacetCertificate (⟨841, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0842 : cubeCofacetCertificate (⟨842, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0843 : cubeCofacetCertificate (⟨843, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0844 : cubeCofacetCertificate (⟨844, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0845 : cubeCofacetCertificate (⟨845, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0846 : cubeCofacetCertificate (⟨846, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0847 : cubeCofacetCertificate (⟨847, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0848 : cubeCofacetCertificate (⟨848, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0849 : cubeCofacetCertificate (⟨849, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0850 : cubeCofacetCertificate (⟨850, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0851 : cubeCofacetCertificate (⟨851, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0852 : cubeCofacetCertificate (⟨852, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0853 : cubeCofacetCertificate (⟨853, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0854 : cubeCofacetCertificate (⟨854, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0855 : cubeCofacetCertificate (⟨855, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0856 : cubeCofacetCertificate (⟨856, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0857 : cubeCofacetCertificate (⟨857, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0858 : cubeCofacetCertificate (⟨858, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0859 : cubeCofacetCertificate (⟨859, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0860 : cubeCofacetCertificate (⟨860, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0861 : cubeCofacetCertificate (⟨861, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0862 : cubeCofacetCertificate (⟨862, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0863 : cubeCofacetCertificate (⟨863, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0864 : cubeCofacetCertificate (⟨864, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0865 : cubeCofacetCertificate (⟨865, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0866 : cubeCofacetCertificate (⟨866, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0867 : cubeCofacetCertificate (⟨867, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0868 : cubeCofacetCertificate (⟨868, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0869 : cubeCofacetCertificate (⟨869, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0870 : cubeCofacetCertificate (⟨870, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0871 : cubeCofacetCertificate (⟨871, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0872 : cubeCofacetCertificate (⟨872, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0873 : cubeCofacetCertificate (⟨873, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0874 : cubeCofacetCertificate (⟨874, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0875 : cubeCofacetCertificate (⟨875, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0876 : cubeCofacetCertificate (⟨876, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0877 : cubeCofacetCertificate (⟨877, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0878 : cubeCofacetCertificate (⟨878, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0879 : cubeCofacetCertificate (⟨879, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0880 : cubeCofacetCertificate (⟨880, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0881 : cubeCofacetCertificate (⟨881, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0882 : cubeCofacetCertificate (⟨882, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0883 : cubeCofacetCertificate (⟨883, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0884 : cubeCofacetCertificate (⟨884, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0885 : cubeCofacetCertificate (⟨885, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0886 : cubeCofacetCertificate (⟨886, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0887 : cubeCofacetCertificate (⟨887, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0888 : cubeCofacetCertificate (⟨888, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0889 : cubeCofacetCertificate (⟨889, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0890 : cubeCofacetCertificate (⟨890, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0891 : cubeCofacetCertificate (⟨891, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0892 : cubeCofacetCertificate (⟨892, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0893 : cubeCofacetCertificate (⟨893, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0894 : cubeCofacetCertificate (⟨894, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0895 : cubeCofacetCertificate (⟨895, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0896 : cubeCofacetCertificate (⟨896, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0897 : cubeCofacetCertificate (⟨897, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0898 : cubeCofacetCertificate (⟨898, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0899 : cubeCofacetCertificate (⟨899, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0900 : cubeCofacetCertificate (⟨900, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0901 : cubeCofacetCertificate (⟨901, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0902 : cubeCofacetCertificate (⟨902, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0903 : cubeCofacetCertificate (⟨903, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0904 : cubeCofacetCertificate (⟨904, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0905 : cubeCofacetCertificate (⟨905, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0906 : cubeCofacetCertificate (⟨906, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0907 : cubeCofacetCertificate (⟨907, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0908 : cubeCofacetCertificate (⟨908, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0909 : cubeCofacetCertificate (⟨909, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0910 : cubeCofacetCertificate (⟨910, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0911 : cubeCofacetCertificate (⟨911, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0912 : cubeCofacetCertificate (⟨912, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0913 : cubeCofacetCertificate (⟨913, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0914 : cubeCofacetCertificate (⟨914, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0915 : cubeCofacetCertificate (⟨915, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0916 : cubeCofacetCertificate (⟨916, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0917 : cubeCofacetCertificate (⟨917, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0918 : cubeCofacetCertificate (⟨918, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0919 : cubeCofacetCertificate (⟨919, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0920 : cubeCofacetCertificate (⟨920, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0921 : cubeCofacetCertificate (⟨921, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0922 : cubeCofacetCertificate (⟨922, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0923 : cubeCofacetCertificate (⟨923, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0924 : cubeCofacetCertificate (⟨924, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0925 : cubeCofacetCertificate (⟨925, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0926 : cubeCofacetCertificate (⟨926, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0927 : cubeCofacetCertificate (⟨927, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0928 : cubeCofacetCertificate (⟨928, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0929 : cubeCofacetCertificate (⟨929, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0930 : cubeCofacetCertificate (⟨930, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0931 : cubeCofacetCertificate (⟨931, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0932 : cubeCofacetCertificate (⟨932, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0933 : cubeCofacetCertificate (⟨933, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0934 : cubeCofacetCertificate (⟨934, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0935 : cubeCofacetCertificate (⟨935, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0936 : cubeCofacetCertificate (⟨936, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0937 : cubeCofacetCertificate (⟨937, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0938 : cubeCofacetCertificate (⟨938, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0939 : cubeCofacetCertificate (⟨939, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0940 : cubeCofacetCertificate (⟨940, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0941 : cubeCofacetCertificate (⟨941, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0942 : cubeCofacetCertificate (⟨942, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0943 : cubeCofacetCertificate (⟨943, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0944 : cubeCofacetCertificate (⟨944, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0945 : cubeCofacetCertificate (⟨945, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0946 : cubeCofacetCertificate (⟨946, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0947 : cubeCofacetCertificate (⟨947, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0948 : cubeCofacetCertificate (⟨948, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0949 : cubeCofacetCertificate (⟨949, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0950 : cubeCofacetCertificate (⟨950, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0951 : cubeCofacetCertificate (⟨951, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0952 : cubeCofacetCertificate (⟨952, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0953 : cubeCofacetCertificate (⟨953, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0954 : cubeCofacetCertificate (⟨954, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0955 : cubeCofacetCertificate (⟨955, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0956 : cubeCofacetCertificate (⟨956, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0957 : cubeCofacetCertificate (⟨957, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0958 : cubeCofacetCertificate (⟨958, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0959 : cubeCofacetCertificate (⟨959, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0960 : cubeCofacetCertificate (⟨960, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0961 : cubeCofacetCertificate (⟨961, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0962 : cubeCofacetCertificate (⟨962, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0963 : cubeCofacetCertificate (⟨963, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0964 : cubeCofacetCertificate (⟨964, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0965 : cubeCofacetCertificate (⟨965, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0966 : cubeCofacetCertificate (⟨966, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0967 : cubeCofacetCertificate (⟨967, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0968 : cubeCofacetCertificate (⟨968, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0969 : cubeCofacetCertificate (⟨969, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0970 : cubeCofacetCertificate (⟨970, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0971 : cubeCofacetCertificate (⟨971, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0972 : cubeCofacetCertificate (⟨972, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0973 : cubeCofacetCertificate (⟨973, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0974 : cubeCofacetCertificate (⟨974, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0975 : cubeCofacetCertificate (⟨975, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0976 : cubeCofacetCertificate (⟨976, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0977 : cubeCofacetCertificate (⟨977, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0978 : cubeCofacetCertificate (⟨978, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0979 : cubeCofacetCertificate (⟨979, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0980 : cubeCofacetCertificate (⟨980, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0981 : cubeCofacetCertificate (⟨981, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0982 : cubeCofacetCertificate (⟨982, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0983 : cubeCofacetCertificate (⟨983, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0984 : cubeCofacetCertificate (⟨984, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0985 : cubeCofacetCertificate (⟨985, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0986 : cubeCofacetCertificate (⟨986, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0987 : cubeCofacetCertificate (⟨987, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0988 : cubeCofacetCertificate (⟨988, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0989 : cubeCofacetCertificate (⟨989, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0990 : cubeCofacetCertificate (⟨990, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0991 : cubeCofacetCertificate (⟨991, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0992 : cubeCofacetCertificate (⟨992, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0993 : cubeCofacetCertificate (⟨993, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0994 : cubeCofacetCertificate (⟨994, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0995 : cubeCofacetCertificate (⟨995, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0996 : cubeCofacetCertificate (⟨996, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0997 : cubeCofacetCertificate (⟨997, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0998 : cubeCofacetCertificate (⟨998, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet0999 : cubeCofacetCertificate (⟨999, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1000 : cubeCofacetCertificate (⟨1000, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1001 : cubeCofacetCertificate (⟨1001, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1002 : cubeCofacetCertificate (⟨1002, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1003 : cubeCofacetCertificate (⟨1003, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1004 : cubeCofacetCertificate (⟨1004, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1005 : cubeCofacetCertificate (⟨1005, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1006 : cubeCofacetCertificate (⟨1006, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1007 : cubeCofacetCertificate (⟨1007, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1008 : cubeCofacetCertificate (⟨1008, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1009 : cubeCofacetCertificate (⟨1009, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1010 : cubeCofacetCertificate (⟨1010, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1011 : cubeCofacetCertificate (⟨1011, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1012 : cubeCofacetCertificate (⟨1012, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1013 : cubeCofacetCertificate (⟨1013, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1014 : cubeCofacetCertificate (⟨1014, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1015 : cubeCofacetCertificate (⟨1015, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1016 : cubeCofacetCertificate (⟨1016, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1017 : cubeCofacetCertificate (⟨1017, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1018 : cubeCofacetCertificate (⟨1018, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1019 : cubeCofacetCertificate (⟨1019, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1020 : cubeCofacetCertificate (⟨1020, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1021 : cubeCofacetCertificate (⟨1021, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1022 : cubeCofacetCertificate (⟨1022, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1023 : cubeCofacetCertificate (⟨1023, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1024 : cubeCofacetCertificate (⟨1024, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1025 : cubeCofacetCertificate (⟨1025, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1026 : cubeCofacetCertificate (⟨1026, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1027 : cubeCofacetCertificate (⟨1027, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1028 : cubeCofacetCertificate (⟨1028, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1029 : cubeCofacetCertificate (⟨1029, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1030 : cubeCofacetCertificate (⟨1030, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1031 : cubeCofacetCertificate (⟨1031, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1032 : cubeCofacetCertificate (⟨1032, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1033 : cubeCofacetCertificate (⟨1033, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1034 : cubeCofacetCertificate (⟨1034, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1035 : cubeCofacetCertificate (⟨1035, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1036 : cubeCofacetCertificate (⟨1036, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1037 : cubeCofacetCertificate (⟨1037, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1038 : cubeCofacetCertificate (⟨1038, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1039 : cubeCofacetCertificate (⟨1039, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1040 : cubeCofacetCertificate (⟨1040, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1041 : cubeCofacetCertificate (⟨1041, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1042 : cubeCofacetCertificate (⟨1042, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1043 : cubeCofacetCertificate (⟨1043, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1044 : cubeCofacetCertificate (⟨1044, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1045 : cubeCofacetCertificate (⟨1045, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1046 : cubeCofacetCertificate (⟨1046, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1047 : cubeCofacetCertificate (⟨1047, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1048 : cubeCofacetCertificate (⟨1048, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1049 : cubeCofacetCertificate (⟨1049, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1050 : cubeCofacetCertificate (⟨1050, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1051 : cubeCofacetCertificate (⟨1051, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1052 : cubeCofacetCertificate (⟨1052, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1053 : cubeCofacetCertificate (⟨1053, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1054 : cubeCofacetCertificate (⟨1054, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1055 : cubeCofacetCertificate (⟨1055, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1056 : cubeCofacetCertificate (⟨1056, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1057 : cubeCofacetCertificate (⟨1057, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1058 : cubeCofacetCertificate (⟨1058, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1059 : cubeCofacetCertificate (⟨1059, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1060 : cubeCofacetCertificate (⟨1060, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1061 : cubeCofacetCertificate (⟨1061, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1062 : cubeCofacetCertificate (⟨1062, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1063 : cubeCofacetCertificate (⟨1063, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1064 : cubeCofacetCertificate (⟨1064, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1065 : cubeCofacetCertificate (⟨1065, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1066 : cubeCofacetCertificate (⟨1066, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1067 : cubeCofacetCertificate (⟨1067, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacet1068 : cubeCofacetCertificate (⟨1068, by decide⟩ : Fin 1069) := by
  apply cubeCofacetCertificate_of_check
  decide +kernel

private theorem cofacetGroup0000 (i : Fin 1069)
    (hlo : 0 ≤ i.val) (hhi : i.val < 32) :
    cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h16 : i.val < 16
  ·
    by_cases h8 : i.val < 8
    ·
      by_cases h4 : i.val < 4
      ·
        by_cases h2 : i.val < 2
        ·
          by_cases h1 : i.val < 1
          ·
            have he : (⟨0, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 0 = i.val
              omega
            simpa only [he] using cofacet0000
          ·
            have he : (⟨1, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1 = i.val
              omega
            simpa only [he] using cofacet0001
        ·
          by_cases h3 : i.val < 3
          ·
            have he : (⟨2, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 2 = i.val
              omega
            simpa only [he] using cofacet0002
          ·
            have he : (⟨3, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 3 = i.val
              omega
            simpa only [he] using cofacet0003
      ·
        by_cases h6 : i.val < 6
        ·
          by_cases h5 : i.val < 5
          ·
            have he : (⟨4, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 4 = i.val
              omega
            simpa only [he] using cofacet0004
          ·
            have he : (⟨5, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 5 = i.val
              omega
            simpa only [he] using cofacet0005
        ·
          by_cases h7 : i.val < 7
          ·
            have he : (⟨6, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 6 = i.val
              omega
            simpa only [he] using cofacet0006
          ·
            have he : (⟨7, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 7 = i.val
              omega
            simpa only [he] using cofacet0007
    ·
      by_cases h12 : i.val < 12
      ·
        by_cases h10 : i.val < 10
        ·
          by_cases h9 : i.val < 9
          ·
            have he : (⟨8, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 8 = i.val
              omega
            simpa only [he] using cofacet0008
          ·
            have he : (⟨9, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 9 = i.val
              omega
            simpa only [he] using cofacet0009
        ·
          by_cases h11 : i.val < 11
          ·
            have he : (⟨10, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 10 = i.val
              omega
            simpa only [he] using cofacet0010
          ·
            have he : (⟨11, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 11 = i.val
              omega
            simpa only [he] using cofacet0011
      ·
        by_cases h14 : i.val < 14
        ·
          by_cases h13 : i.val < 13
          ·
            have he : (⟨12, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 12 = i.val
              omega
            simpa only [he] using cofacet0012
          ·
            have he : (⟨13, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 13 = i.val
              omega
            simpa only [he] using cofacet0013
        ·
          by_cases h15 : i.val < 15
          ·
            have he : (⟨14, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 14 = i.val
              omega
            simpa only [he] using cofacet0014
          ·
            have he : (⟨15, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 15 = i.val
              omega
            simpa only [he] using cofacet0015
  ·
    by_cases h24 : i.val < 24
    ·
      by_cases h20 : i.val < 20
      ·
        by_cases h18 : i.val < 18
        ·
          by_cases h17 : i.val < 17
          ·
            have he : (⟨16, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 16 = i.val
              omega
            simpa only [he] using cofacet0016
          ·
            have he : (⟨17, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 17 = i.val
              omega
            simpa only [he] using cofacet0017
        ·
          by_cases h19 : i.val < 19
          ·
            have he : (⟨18, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 18 = i.val
              omega
            simpa only [he] using cofacet0018
          ·
            have he : (⟨19, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 19 = i.val
              omega
            simpa only [he] using cofacet0019
      ·
        by_cases h22 : i.val < 22
        ·
          by_cases h21 : i.val < 21
          ·
            have he : (⟨20, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 20 = i.val
              omega
            simpa only [he] using cofacet0020
          ·
            have he : (⟨21, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 21 = i.val
              omega
            simpa only [he] using cofacet0021
        ·
          by_cases h23 : i.val < 23
          ·
            have he : (⟨22, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 22 = i.val
              omega
            simpa only [he] using cofacet0022
          ·
            have he : (⟨23, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 23 = i.val
              omega
            simpa only [he] using cofacet0023
    ·
      by_cases h28 : i.val < 28
      ·
        by_cases h26 : i.val < 26
        ·
          by_cases h25 : i.val < 25
          ·
            have he : (⟨24, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 24 = i.val
              omega
            simpa only [he] using cofacet0024
          ·
            have he : (⟨25, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 25 = i.val
              omega
            simpa only [he] using cofacet0025
        ·
          by_cases h27 : i.val < 27
          ·
            have he : (⟨26, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 26 = i.val
              omega
            simpa only [he] using cofacet0026
          ·
            have he : (⟨27, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 27 = i.val
              omega
            simpa only [he] using cofacet0027
      ·
        by_cases h30 : i.val < 30
        ·
          by_cases h29 : i.val < 29
          ·
            have he : (⟨28, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 28 = i.val
              omega
            simpa only [he] using cofacet0028
          ·
            have he : (⟨29, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 29 = i.val
              omega
            simpa only [he] using cofacet0029
        ·
          by_cases h31 : i.val < 31
          ·
            have he : (⟨30, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 30 = i.val
              omega
            simpa only [he] using cofacet0030
          ·
            have he : (⟨31, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 31 = i.val
              omega
            simpa only [he] using cofacet0031

private theorem cofacetGroup0001 (i : Fin 1069)
    (hlo : 32 ≤ i.val) (hhi : i.val < 64) :
    cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h48 : i.val < 48
  ·
    by_cases h40 : i.val < 40
    ·
      by_cases h36 : i.val < 36
      ·
        by_cases h34 : i.val < 34
        ·
          by_cases h33 : i.val < 33
          ·
            have he : (⟨32, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 32 = i.val
              omega
            simpa only [he] using cofacet0032
          ·
            have he : (⟨33, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 33 = i.val
              omega
            simpa only [he] using cofacet0033
        ·
          by_cases h35 : i.val < 35
          ·
            have he : (⟨34, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 34 = i.val
              omega
            simpa only [he] using cofacet0034
          ·
            have he : (⟨35, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 35 = i.val
              omega
            simpa only [he] using cofacet0035
      ·
        by_cases h38 : i.val < 38
        ·
          by_cases h37 : i.val < 37
          ·
            have he : (⟨36, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 36 = i.val
              omega
            simpa only [he] using cofacet0036
          ·
            have he : (⟨37, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 37 = i.val
              omega
            simpa only [he] using cofacet0037
        ·
          by_cases h39 : i.val < 39
          ·
            have he : (⟨38, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 38 = i.val
              omega
            simpa only [he] using cofacet0038
          ·
            have he : (⟨39, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 39 = i.val
              omega
            simpa only [he] using cofacet0039
    ·
      by_cases h44 : i.val < 44
      ·
        by_cases h42 : i.val < 42
        ·
          by_cases h41 : i.val < 41
          ·
            have he : (⟨40, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 40 = i.val
              omega
            simpa only [he] using cofacet0040
          ·
            have he : (⟨41, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 41 = i.val
              omega
            simpa only [he] using cofacet0041
        ·
          by_cases h43 : i.val < 43
          ·
            have he : (⟨42, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 42 = i.val
              omega
            simpa only [he] using cofacet0042
          ·
            have he : (⟨43, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 43 = i.val
              omega
            simpa only [he] using cofacet0043
      ·
        by_cases h46 : i.val < 46
        ·
          by_cases h45 : i.val < 45
          ·
            have he : (⟨44, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 44 = i.val
              omega
            simpa only [he] using cofacet0044
          ·
            have he : (⟨45, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 45 = i.val
              omega
            simpa only [he] using cofacet0045
        ·
          by_cases h47 : i.val < 47
          ·
            have he : (⟨46, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 46 = i.val
              omega
            simpa only [he] using cofacet0046
          ·
            have he : (⟨47, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 47 = i.val
              omega
            simpa only [he] using cofacet0047
  ·
    by_cases h56 : i.val < 56
    ·
      by_cases h52 : i.val < 52
      ·
        by_cases h50 : i.val < 50
        ·
          by_cases h49 : i.val < 49
          ·
            have he : (⟨48, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 48 = i.val
              omega
            simpa only [he] using cofacet0048
          ·
            have he : (⟨49, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 49 = i.val
              omega
            simpa only [he] using cofacet0049
        ·
          by_cases h51 : i.val < 51
          ·
            have he : (⟨50, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 50 = i.val
              omega
            simpa only [he] using cofacet0050
          ·
            have he : (⟨51, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 51 = i.val
              omega
            simpa only [he] using cofacet0051
      ·
        by_cases h54 : i.val < 54
        ·
          by_cases h53 : i.val < 53
          ·
            have he : (⟨52, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 52 = i.val
              omega
            simpa only [he] using cofacet0052
          ·
            have he : (⟨53, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 53 = i.val
              omega
            simpa only [he] using cofacet0053
        ·
          by_cases h55 : i.val < 55
          ·
            have he : (⟨54, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 54 = i.val
              omega
            simpa only [he] using cofacet0054
          ·
            have he : (⟨55, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 55 = i.val
              omega
            simpa only [he] using cofacet0055
    ·
      by_cases h60 : i.val < 60
      ·
        by_cases h58 : i.val < 58
        ·
          by_cases h57 : i.val < 57
          ·
            have he : (⟨56, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 56 = i.val
              omega
            simpa only [he] using cofacet0056
          ·
            have he : (⟨57, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 57 = i.val
              omega
            simpa only [he] using cofacet0057
        ·
          by_cases h59 : i.val < 59
          ·
            have he : (⟨58, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 58 = i.val
              omega
            simpa only [he] using cofacet0058
          ·
            have he : (⟨59, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 59 = i.val
              omega
            simpa only [he] using cofacet0059
      ·
        by_cases h62 : i.val < 62
        ·
          by_cases h61 : i.val < 61
          ·
            have he : (⟨60, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 60 = i.val
              omega
            simpa only [he] using cofacet0060
          ·
            have he : (⟨61, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 61 = i.val
              omega
            simpa only [he] using cofacet0061
        ·
          by_cases h63 : i.val < 63
          ·
            have he : (⟨62, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 62 = i.val
              omega
            simpa only [he] using cofacet0062
          ·
            have he : (⟨63, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 63 = i.val
              omega
            simpa only [he] using cofacet0063

private theorem cofacetGroup0002 (i : Fin 1069)
    (hlo : 64 ≤ i.val) (hhi : i.val < 96) :
    cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h80 : i.val < 80
  ·
    by_cases h72 : i.val < 72
    ·
      by_cases h68 : i.val < 68
      ·
        by_cases h66 : i.val < 66
        ·
          by_cases h65 : i.val < 65
          ·
            have he : (⟨64, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 64 = i.val
              omega
            simpa only [he] using cofacet0064
          ·
            have he : (⟨65, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 65 = i.val
              omega
            simpa only [he] using cofacet0065
        ·
          by_cases h67 : i.val < 67
          ·
            have he : (⟨66, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 66 = i.val
              omega
            simpa only [he] using cofacet0066
          ·
            have he : (⟨67, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 67 = i.val
              omega
            simpa only [he] using cofacet0067
      ·
        by_cases h70 : i.val < 70
        ·
          by_cases h69 : i.val < 69
          ·
            have he : (⟨68, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 68 = i.val
              omega
            simpa only [he] using cofacet0068
          ·
            have he : (⟨69, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 69 = i.val
              omega
            simpa only [he] using cofacet0069
        ·
          by_cases h71 : i.val < 71
          ·
            have he : (⟨70, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 70 = i.val
              omega
            simpa only [he] using cofacet0070
          ·
            have he : (⟨71, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 71 = i.val
              omega
            simpa only [he] using cofacet0071
    ·
      by_cases h76 : i.val < 76
      ·
        by_cases h74 : i.val < 74
        ·
          by_cases h73 : i.val < 73
          ·
            have he : (⟨72, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 72 = i.val
              omega
            simpa only [he] using cofacet0072
          ·
            have he : (⟨73, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 73 = i.val
              omega
            simpa only [he] using cofacet0073
        ·
          by_cases h75 : i.val < 75
          ·
            have he : (⟨74, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 74 = i.val
              omega
            simpa only [he] using cofacet0074
          ·
            have he : (⟨75, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 75 = i.val
              omega
            simpa only [he] using cofacet0075
      ·
        by_cases h78 : i.val < 78
        ·
          by_cases h77 : i.val < 77
          ·
            have he : (⟨76, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 76 = i.val
              omega
            simpa only [he] using cofacet0076
          ·
            have he : (⟨77, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 77 = i.val
              omega
            simpa only [he] using cofacet0077
        ·
          by_cases h79 : i.val < 79
          ·
            have he : (⟨78, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 78 = i.val
              omega
            simpa only [he] using cofacet0078
          ·
            have he : (⟨79, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 79 = i.val
              omega
            simpa only [he] using cofacet0079
  ·
    by_cases h88 : i.val < 88
    ·
      by_cases h84 : i.val < 84
      ·
        by_cases h82 : i.val < 82
        ·
          by_cases h81 : i.val < 81
          ·
            have he : (⟨80, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 80 = i.val
              omega
            simpa only [he] using cofacet0080
          ·
            have he : (⟨81, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 81 = i.val
              omega
            simpa only [he] using cofacet0081
        ·
          by_cases h83 : i.val < 83
          ·
            have he : (⟨82, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 82 = i.val
              omega
            simpa only [he] using cofacet0082
          ·
            have he : (⟨83, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 83 = i.val
              omega
            simpa only [he] using cofacet0083
      ·
        by_cases h86 : i.val < 86
        ·
          by_cases h85 : i.val < 85
          ·
            have he : (⟨84, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 84 = i.val
              omega
            simpa only [he] using cofacet0084
          ·
            have he : (⟨85, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 85 = i.val
              omega
            simpa only [he] using cofacet0085
        ·
          by_cases h87 : i.val < 87
          ·
            have he : (⟨86, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 86 = i.val
              omega
            simpa only [he] using cofacet0086
          ·
            have he : (⟨87, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 87 = i.val
              omega
            simpa only [he] using cofacet0087
    ·
      by_cases h92 : i.val < 92
      ·
        by_cases h90 : i.val < 90
        ·
          by_cases h89 : i.val < 89
          ·
            have he : (⟨88, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 88 = i.val
              omega
            simpa only [he] using cofacet0088
          ·
            have he : (⟨89, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 89 = i.val
              omega
            simpa only [he] using cofacet0089
        ·
          by_cases h91 : i.val < 91
          ·
            have he : (⟨90, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 90 = i.val
              omega
            simpa only [he] using cofacet0090
          ·
            have he : (⟨91, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 91 = i.val
              omega
            simpa only [he] using cofacet0091
      ·
        by_cases h94 : i.val < 94
        ·
          by_cases h93 : i.val < 93
          ·
            have he : (⟨92, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 92 = i.val
              omega
            simpa only [he] using cofacet0092
          ·
            have he : (⟨93, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 93 = i.val
              omega
            simpa only [he] using cofacet0093
        ·
          by_cases h95 : i.val < 95
          ·
            have he : (⟨94, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 94 = i.val
              omega
            simpa only [he] using cofacet0094
          ·
            have he : (⟨95, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 95 = i.val
              omega
            simpa only [he] using cofacet0095

private theorem cofacetGroup0003 (i : Fin 1069)
    (hlo : 96 ≤ i.val) (hhi : i.val < 128) :
    cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h112 : i.val < 112
  ·
    by_cases h104 : i.val < 104
    ·
      by_cases h100 : i.val < 100
      ·
        by_cases h98 : i.val < 98
        ·
          by_cases h97 : i.val < 97
          ·
            have he : (⟨96, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 96 = i.val
              omega
            simpa only [he] using cofacet0096
          ·
            have he : (⟨97, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 97 = i.val
              omega
            simpa only [he] using cofacet0097
        ·
          by_cases h99 : i.val < 99
          ·
            have he : (⟨98, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 98 = i.val
              omega
            simpa only [he] using cofacet0098
          ·
            have he : (⟨99, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 99 = i.val
              omega
            simpa only [he] using cofacet0099
      ·
        by_cases h102 : i.val < 102
        ·
          by_cases h101 : i.val < 101
          ·
            have he : (⟨100, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 100 = i.val
              omega
            simpa only [he] using cofacet0100
          ·
            have he : (⟨101, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 101 = i.val
              omega
            simpa only [he] using cofacet0101
        ·
          by_cases h103 : i.val < 103
          ·
            have he : (⟨102, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 102 = i.val
              omega
            simpa only [he] using cofacet0102
          ·
            have he : (⟨103, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 103 = i.val
              omega
            simpa only [he] using cofacet0103
    ·
      by_cases h108 : i.val < 108
      ·
        by_cases h106 : i.val < 106
        ·
          by_cases h105 : i.val < 105
          ·
            have he : (⟨104, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 104 = i.val
              omega
            simpa only [he] using cofacet0104
          ·
            have he : (⟨105, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 105 = i.val
              omega
            simpa only [he] using cofacet0105
        ·
          by_cases h107 : i.val < 107
          ·
            have he : (⟨106, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 106 = i.val
              omega
            simpa only [he] using cofacet0106
          ·
            have he : (⟨107, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 107 = i.val
              omega
            simpa only [he] using cofacet0107
      ·
        by_cases h110 : i.val < 110
        ·
          by_cases h109 : i.val < 109
          ·
            have he : (⟨108, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 108 = i.val
              omega
            simpa only [he] using cofacet0108
          ·
            have he : (⟨109, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 109 = i.val
              omega
            simpa only [he] using cofacet0109
        ·
          by_cases h111 : i.val < 111
          ·
            have he : (⟨110, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 110 = i.val
              omega
            simpa only [he] using cofacet0110
          ·
            have he : (⟨111, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 111 = i.val
              omega
            simpa only [he] using cofacet0111
  ·
    by_cases h120 : i.val < 120
    ·
      by_cases h116 : i.val < 116
      ·
        by_cases h114 : i.val < 114
        ·
          by_cases h113 : i.val < 113
          ·
            have he : (⟨112, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 112 = i.val
              omega
            simpa only [he] using cofacet0112
          ·
            have he : (⟨113, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 113 = i.val
              omega
            simpa only [he] using cofacet0113
        ·
          by_cases h115 : i.val < 115
          ·
            have he : (⟨114, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 114 = i.val
              omega
            simpa only [he] using cofacet0114
          ·
            have he : (⟨115, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 115 = i.val
              omega
            simpa only [he] using cofacet0115
      ·
        by_cases h118 : i.val < 118
        ·
          by_cases h117 : i.val < 117
          ·
            have he : (⟨116, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 116 = i.val
              omega
            simpa only [he] using cofacet0116
          ·
            have he : (⟨117, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 117 = i.val
              omega
            simpa only [he] using cofacet0117
        ·
          by_cases h119 : i.val < 119
          ·
            have he : (⟨118, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 118 = i.val
              omega
            simpa only [he] using cofacet0118
          ·
            have he : (⟨119, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 119 = i.val
              omega
            simpa only [he] using cofacet0119
    ·
      by_cases h124 : i.val < 124
      ·
        by_cases h122 : i.val < 122
        ·
          by_cases h121 : i.val < 121
          ·
            have he : (⟨120, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 120 = i.val
              omega
            simpa only [he] using cofacet0120
          ·
            have he : (⟨121, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 121 = i.val
              omega
            simpa only [he] using cofacet0121
        ·
          by_cases h123 : i.val < 123
          ·
            have he : (⟨122, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 122 = i.val
              omega
            simpa only [he] using cofacet0122
          ·
            have he : (⟨123, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 123 = i.val
              omega
            simpa only [he] using cofacet0123
      ·
        by_cases h126 : i.val < 126
        ·
          by_cases h125 : i.val < 125
          ·
            have he : (⟨124, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 124 = i.val
              omega
            simpa only [he] using cofacet0124
          ·
            have he : (⟨125, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 125 = i.val
              omega
            simpa only [he] using cofacet0125
        ·
          by_cases h127 : i.val < 127
          ·
            have he : (⟨126, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 126 = i.val
              omega
            simpa only [he] using cofacet0126
          ·
            have he : (⟨127, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 127 = i.val
              omega
            simpa only [he] using cofacet0127

private theorem cofacetGroup0004 (i : Fin 1069)
    (hlo : 128 ≤ i.val) (hhi : i.val < 160) :
    cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h144 : i.val < 144
  ·
    by_cases h136 : i.val < 136
    ·
      by_cases h132 : i.val < 132
      ·
        by_cases h130 : i.val < 130
        ·
          by_cases h129 : i.val < 129
          ·
            have he : (⟨128, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 128 = i.val
              omega
            simpa only [he] using cofacet0128
          ·
            have he : (⟨129, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 129 = i.val
              omega
            simpa only [he] using cofacet0129
        ·
          by_cases h131 : i.val < 131
          ·
            have he : (⟨130, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 130 = i.val
              omega
            simpa only [he] using cofacet0130
          ·
            have he : (⟨131, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 131 = i.val
              omega
            simpa only [he] using cofacet0131
      ·
        by_cases h134 : i.val < 134
        ·
          by_cases h133 : i.val < 133
          ·
            have he : (⟨132, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 132 = i.val
              omega
            simpa only [he] using cofacet0132
          ·
            have he : (⟨133, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 133 = i.val
              omega
            simpa only [he] using cofacet0133
        ·
          by_cases h135 : i.val < 135
          ·
            have he : (⟨134, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 134 = i.val
              omega
            simpa only [he] using cofacet0134
          ·
            have he : (⟨135, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 135 = i.val
              omega
            simpa only [he] using cofacet0135
    ·
      by_cases h140 : i.val < 140
      ·
        by_cases h138 : i.val < 138
        ·
          by_cases h137 : i.val < 137
          ·
            have he : (⟨136, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 136 = i.val
              omega
            simpa only [he] using cofacet0136
          ·
            have he : (⟨137, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 137 = i.val
              omega
            simpa only [he] using cofacet0137
        ·
          by_cases h139 : i.val < 139
          ·
            have he : (⟨138, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 138 = i.val
              omega
            simpa only [he] using cofacet0138
          ·
            have he : (⟨139, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 139 = i.val
              omega
            simpa only [he] using cofacet0139
      ·
        by_cases h142 : i.val < 142
        ·
          by_cases h141 : i.val < 141
          ·
            have he : (⟨140, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 140 = i.val
              omega
            simpa only [he] using cofacet0140
          ·
            have he : (⟨141, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 141 = i.val
              omega
            simpa only [he] using cofacet0141
        ·
          by_cases h143 : i.val < 143
          ·
            have he : (⟨142, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 142 = i.val
              omega
            simpa only [he] using cofacet0142
          ·
            have he : (⟨143, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 143 = i.val
              omega
            simpa only [he] using cofacet0143
  ·
    by_cases h152 : i.val < 152
    ·
      by_cases h148 : i.val < 148
      ·
        by_cases h146 : i.val < 146
        ·
          by_cases h145 : i.val < 145
          ·
            have he : (⟨144, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 144 = i.val
              omega
            simpa only [he] using cofacet0144
          ·
            have he : (⟨145, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 145 = i.val
              omega
            simpa only [he] using cofacet0145
        ·
          by_cases h147 : i.val < 147
          ·
            have he : (⟨146, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 146 = i.val
              omega
            simpa only [he] using cofacet0146
          ·
            have he : (⟨147, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 147 = i.val
              omega
            simpa only [he] using cofacet0147
      ·
        by_cases h150 : i.val < 150
        ·
          by_cases h149 : i.val < 149
          ·
            have he : (⟨148, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 148 = i.val
              omega
            simpa only [he] using cofacet0148
          ·
            have he : (⟨149, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 149 = i.val
              omega
            simpa only [he] using cofacet0149
        ·
          by_cases h151 : i.val < 151
          ·
            have he : (⟨150, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 150 = i.val
              omega
            simpa only [he] using cofacet0150
          ·
            have he : (⟨151, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 151 = i.val
              omega
            simpa only [he] using cofacet0151
    ·
      by_cases h156 : i.val < 156
      ·
        by_cases h154 : i.val < 154
        ·
          by_cases h153 : i.val < 153
          ·
            have he : (⟨152, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 152 = i.val
              omega
            simpa only [he] using cofacet0152
          ·
            have he : (⟨153, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 153 = i.val
              omega
            simpa only [he] using cofacet0153
        ·
          by_cases h155 : i.val < 155
          ·
            have he : (⟨154, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 154 = i.val
              omega
            simpa only [he] using cofacet0154
          ·
            have he : (⟨155, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 155 = i.val
              omega
            simpa only [he] using cofacet0155
      ·
        by_cases h158 : i.val < 158
        ·
          by_cases h157 : i.val < 157
          ·
            have he : (⟨156, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 156 = i.val
              omega
            simpa only [he] using cofacet0156
          ·
            have he : (⟨157, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 157 = i.val
              omega
            simpa only [he] using cofacet0157
        ·
          by_cases h159 : i.val < 159
          ·
            have he : (⟨158, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 158 = i.val
              omega
            simpa only [he] using cofacet0158
          ·
            have he : (⟨159, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 159 = i.val
              omega
            simpa only [he] using cofacet0159

private theorem cofacetGroup0005 (i : Fin 1069)
    (hlo : 160 ≤ i.val) (hhi : i.val < 192) :
    cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h176 : i.val < 176
  ·
    by_cases h168 : i.val < 168
    ·
      by_cases h164 : i.val < 164
      ·
        by_cases h162 : i.val < 162
        ·
          by_cases h161 : i.val < 161
          ·
            have he : (⟨160, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 160 = i.val
              omega
            simpa only [he] using cofacet0160
          ·
            have he : (⟨161, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 161 = i.val
              omega
            simpa only [he] using cofacet0161
        ·
          by_cases h163 : i.val < 163
          ·
            have he : (⟨162, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 162 = i.val
              omega
            simpa only [he] using cofacet0162
          ·
            have he : (⟨163, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 163 = i.val
              omega
            simpa only [he] using cofacet0163
      ·
        by_cases h166 : i.val < 166
        ·
          by_cases h165 : i.val < 165
          ·
            have he : (⟨164, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 164 = i.val
              omega
            simpa only [he] using cofacet0164
          ·
            have he : (⟨165, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 165 = i.val
              omega
            simpa only [he] using cofacet0165
        ·
          by_cases h167 : i.val < 167
          ·
            have he : (⟨166, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 166 = i.val
              omega
            simpa only [he] using cofacet0166
          ·
            have he : (⟨167, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 167 = i.val
              omega
            simpa only [he] using cofacet0167
    ·
      by_cases h172 : i.val < 172
      ·
        by_cases h170 : i.val < 170
        ·
          by_cases h169 : i.val < 169
          ·
            have he : (⟨168, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 168 = i.val
              omega
            simpa only [he] using cofacet0168
          ·
            have he : (⟨169, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 169 = i.val
              omega
            simpa only [he] using cofacet0169
        ·
          by_cases h171 : i.val < 171
          ·
            have he : (⟨170, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 170 = i.val
              omega
            simpa only [he] using cofacet0170
          ·
            have he : (⟨171, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 171 = i.val
              omega
            simpa only [he] using cofacet0171
      ·
        by_cases h174 : i.val < 174
        ·
          by_cases h173 : i.val < 173
          ·
            have he : (⟨172, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 172 = i.val
              omega
            simpa only [he] using cofacet0172
          ·
            have he : (⟨173, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 173 = i.val
              omega
            simpa only [he] using cofacet0173
        ·
          by_cases h175 : i.val < 175
          ·
            have he : (⟨174, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 174 = i.val
              omega
            simpa only [he] using cofacet0174
          ·
            have he : (⟨175, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 175 = i.val
              omega
            simpa only [he] using cofacet0175
  ·
    by_cases h184 : i.val < 184
    ·
      by_cases h180 : i.val < 180
      ·
        by_cases h178 : i.val < 178
        ·
          by_cases h177 : i.val < 177
          ·
            have he : (⟨176, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 176 = i.val
              omega
            simpa only [he] using cofacet0176
          ·
            have he : (⟨177, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 177 = i.val
              omega
            simpa only [he] using cofacet0177
        ·
          by_cases h179 : i.val < 179
          ·
            have he : (⟨178, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 178 = i.val
              omega
            simpa only [he] using cofacet0178
          ·
            have he : (⟨179, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 179 = i.val
              omega
            simpa only [he] using cofacet0179
      ·
        by_cases h182 : i.val < 182
        ·
          by_cases h181 : i.val < 181
          ·
            have he : (⟨180, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 180 = i.val
              omega
            simpa only [he] using cofacet0180
          ·
            have he : (⟨181, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 181 = i.val
              omega
            simpa only [he] using cofacet0181
        ·
          by_cases h183 : i.val < 183
          ·
            have he : (⟨182, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 182 = i.val
              omega
            simpa only [he] using cofacet0182
          ·
            have he : (⟨183, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 183 = i.val
              omega
            simpa only [he] using cofacet0183
    ·
      by_cases h188 : i.val < 188
      ·
        by_cases h186 : i.val < 186
        ·
          by_cases h185 : i.val < 185
          ·
            have he : (⟨184, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 184 = i.val
              omega
            simpa only [he] using cofacet0184
          ·
            have he : (⟨185, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 185 = i.val
              omega
            simpa only [he] using cofacet0185
        ·
          by_cases h187 : i.val < 187
          ·
            have he : (⟨186, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 186 = i.val
              omega
            simpa only [he] using cofacet0186
          ·
            have he : (⟨187, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 187 = i.val
              omega
            simpa only [he] using cofacet0187
      ·
        by_cases h190 : i.val < 190
        ·
          by_cases h189 : i.val < 189
          ·
            have he : (⟨188, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 188 = i.val
              omega
            simpa only [he] using cofacet0188
          ·
            have he : (⟨189, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 189 = i.val
              omega
            simpa only [he] using cofacet0189
        ·
          by_cases h191 : i.val < 191
          ·
            have he : (⟨190, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 190 = i.val
              omega
            simpa only [he] using cofacet0190
          ·
            have he : (⟨191, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 191 = i.val
              omega
            simpa only [he] using cofacet0191

private theorem cofacetGroup0006 (i : Fin 1069)
    (hlo : 192 ≤ i.val) (hhi : i.val < 224) :
    cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h208 : i.val < 208
  ·
    by_cases h200 : i.val < 200
    ·
      by_cases h196 : i.val < 196
      ·
        by_cases h194 : i.val < 194
        ·
          by_cases h193 : i.val < 193
          ·
            have he : (⟨192, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 192 = i.val
              omega
            simpa only [he] using cofacet0192
          ·
            have he : (⟨193, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 193 = i.val
              omega
            simpa only [he] using cofacet0193
        ·
          by_cases h195 : i.val < 195
          ·
            have he : (⟨194, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 194 = i.val
              omega
            simpa only [he] using cofacet0194
          ·
            have he : (⟨195, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 195 = i.val
              omega
            simpa only [he] using cofacet0195
      ·
        by_cases h198 : i.val < 198
        ·
          by_cases h197 : i.val < 197
          ·
            have he : (⟨196, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 196 = i.val
              omega
            simpa only [he] using cofacet0196
          ·
            have he : (⟨197, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 197 = i.val
              omega
            simpa only [he] using cofacet0197
        ·
          by_cases h199 : i.val < 199
          ·
            have he : (⟨198, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 198 = i.val
              omega
            simpa only [he] using cofacet0198
          ·
            have he : (⟨199, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 199 = i.val
              omega
            simpa only [he] using cofacet0199
    ·
      by_cases h204 : i.val < 204
      ·
        by_cases h202 : i.val < 202
        ·
          by_cases h201 : i.val < 201
          ·
            have he : (⟨200, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 200 = i.val
              omega
            simpa only [he] using cofacet0200
          ·
            have he : (⟨201, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 201 = i.val
              omega
            simpa only [he] using cofacet0201
        ·
          by_cases h203 : i.val < 203
          ·
            have he : (⟨202, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 202 = i.val
              omega
            simpa only [he] using cofacet0202
          ·
            have he : (⟨203, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 203 = i.val
              omega
            simpa only [he] using cofacet0203
      ·
        by_cases h206 : i.val < 206
        ·
          by_cases h205 : i.val < 205
          ·
            have he : (⟨204, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 204 = i.val
              omega
            simpa only [he] using cofacet0204
          ·
            have he : (⟨205, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 205 = i.val
              omega
            simpa only [he] using cofacet0205
        ·
          by_cases h207 : i.val < 207
          ·
            have he : (⟨206, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 206 = i.val
              omega
            simpa only [he] using cofacet0206
          ·
            have he : (⟨207, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 207 = i.val
              omega
            simpa only [he] using cofacet0207
  ·
    by_cases h216 : i.val < 216
    ·
      by_cases h212 : i.val < 212
      ·
        by_cases h210 : i.val < 210
        ·
          by_cases h209 : i.val < 209
          ·
            have he : (⟨208, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 208 = i.val
              omega
            simpa only [he] using cofacet0208
          ·
            have he : (⟨209, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 209 = i.val
              omega
            simpa only [he] using cofacet0209
        ·
          by_cases h211 : i.val < 211
          ·
            have he : (⟨210, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 210 = i.val
              omega
            simpa only [he] using cofacet0210
          ·
            have he : (⟨211, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 211 = i.val
              omega
            simpa only [he] using cofacet0211
      ·
        by_cases h214 : i.val < 214
        ·
          by_cases h213 : i.val < 213
          ·
            have he : (⟨212, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 212 = i.val
              omega
            simpa only [he] using cofacet0212
          ·
            have he : (⟨213, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 213 = i.val
              omega
            simpa only [he] using cofacet0213
        ·
          by_cases h215 : i.val < 215
          ·
            have he : (⟨214, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 214 = i.val
              omega
            simpa only [he] using cofacet0214
          ·
            have he : (⟨215, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 215 = i.val
              omega
            simpa only [he] using cofacet0215
    ·
      by_cases h220 : i.val < 220
      ·
        by_cases h218 : i.val < 218
        ·
          by_cases h217 : i.val < 217
          ·
            have he : (⟨216, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 216 = i.val
              omega
            simpa only [he] using cofacet0216
          ·
            have he : (⟨217, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 217 = i.val
              omega
            simpa only [he] using cofacet0217
        ·
          by_cases h219 : i.val < 219
          ·
            have he : (⟨218, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 218 = i.val
              omega
            simpa only [he] using cofacet0218
          ·
            have he : (⟨219, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 219 = i.val
              omega
            simpa only [he] using cofacet0219
      ·
        by_cases h222 : i.val < 222
        ·
          by_cases h221 : i.val < 221
          ·
            have he : (⟨220, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 220 = i.val
              omega
            simpa only [he] using cofacet0220
          ·
            have he : (⟨221, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 221 = i.val
              omega
            simpa only [he] using cofacet0221
        ·
          by_cases h223 : i.val < 223
          ·
            have he : (⟨222, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 222 = i.val
              omega
            simpa only [he] using cofacet0222
          ·
            have he : (⟨223, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 223 = i.val
              omega
            simpa only [he] using cofacet0223

private theorem cofacetGroup0007 (i : Fin 1069)
    (hlo : 224 ≤ i.val) (hhi : i.val < 256) :
    cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h240 : i.val < 240
  ·
    by_cases h232 : i.val < 232
    ·
      by_cases h228 : i.val < 228
      ·
        by_cases h226 : i.val < 226
        ·
          by_cases h225 : i.val < 225
          ·
            have he : (⟨224, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 224 = i.val
              omega
            simpa only [he] using cofacet0224
          ·
            have he : (⟨225, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 225 = i.val
              omega
            simpa only [he] using cofacet0225
        ·
          by_cases h227 : i.val < 227
          ·
            have he : (⟨226, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 226 = i.val
              omega
            simpa only [he] using cofacet0226
          ·
            have he : (⟨227, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 227 = i.val
              omega
            simpa only [he] using cofacet0227
      ·
        by_cases h230 : i.val < 230
        ·
          by_cases h229 : i.val < 229
          ·
            have he : (⟨228, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 228 = i.val
              omega
            simpa only [he] using cofacet0228
          ·
            have he : (⟨229, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 229 = i.val
              omega
            simpa only [he] using cofacet0229
        ·
          by_cases h231 : i.val < 231
          ·
            have he : (⟨230, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 230 = i.val
              omega
            simpa only [he] using cofacet0230
          ·
            have he : (⟨231, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 231 = i.val
              omega
            simpa only [he] using cofacet0231
    ·
      by_cases h236 : i.val < 236
      ·
        by_cases h234 : i.val < 234
        ·
          by_cases h233 : i.val < 233
          ·
            have he : (⟨232, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 232 = i.val
              omega
            simpa only [he] using cofacet0232
          ·
            have he : (⟨233, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 233 = i.val
              omega
            simpa only [he] using cofacet0233
        ·
          by_cases h235 : i.val < 235
          ·
            have he : (⟨234, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 234 = i.val
              omega
            simpa only [he] using cofacet0234
          ·
            have he : (⟨235, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 235 = i.val
              omega
            simpa only [he] using cofacet0235
      ·
        by_cases h238 : i.val < 238
        ·
          by_cases h237 : i.val < 237
          ·
            have he : (⟨236, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 236 = i.val
              omega
            simpa only [he] using cofacet0236
          ·
            have he : (⟨237, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 237 = i.val
              omega
            simpa only [he] using cofacet0237
        ·
          by_cases h239 : i.val < 239
          ·
            have he : (⟨238, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 238 = i.val
              omega
            simpa only [he] using cofacet0238
          ·
            have he : (⟨239, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 239 = i.val
              omega
            simpa only [he] using cofacet0239
  ·
    by_cases h248 : i.val < 248
    ·
      by_cases h244 : i.val < 244
      ·
        by_cases h242 : i.val < 242
        ·
          by_cases h241 : i.val < 241
          ·
            have he : (⟨240, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 240 = i.val
              omega
            simpa only [he] using cofacet0240
          ·
            have he : (⟨241, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 241 = i.val
              omega
            simpa only [he] using cofacet0241
        ·
          by_cases h243 : i.val < 243
          ·
            have he : (⟨242, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 242 = i.val
              omega
            simpa only [he] using cofacet0242
          ·
            have he : (⟨243, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 243 = i.val
              omega
            simpa only [he] using cofacet0243
      ·
        by_cases h246 : i.val < 246
        ·
          by_cases h245 : i.val < 245
          ·
            have he : (⟨244, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 244 = i.val
              omega
            simpa only [he] using cofacet0244
          ·
            have he : (⟨245, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 245 = i.val
              omega
            simpa only [he] using cofacet0245
        ·
          by_cases h247 : i.val < 247
          ·
            have he : (⟨246, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 246 = i.val
              omega
            simpa only [he] using cofacet0246
          ·
            have he : (⟨247, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 247 = i.val
              omega
            simpa only [he] using cofacet0247
    ·
      by_cases h252 : i.val < 252
      ·
        by_cases h250 : i.val < 250
        ·
          by_cases h249 : i.val < 249
          ·
            have he : (⟨248, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 248 = i.val
              omega
            simpa only [he] using cofacet0248
          ·
            have he : (⟨249, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 249 = i.val
              omega
            simpa only [he] using cofacet0249
        ·
          by_cases h251 : i.val < 251
          ·
            have he : (⟨250, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 250 = i.val
              omega
            simpa only [he] using cofacet0250
          ·
            have he : (⟨251, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 251 = i.val
              omega
            simpa only [he] using cofacet0251
      ·
        by_cases h254 : i.val < 254
        ·
          by_cases h253 : i.val < 253
          ·
            have he : (⟨252, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 252 = i.val
              omega
            simpa only [he] using cofacet0252
          ·
            have he : (⟨253, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 253 = i.val
              omega
            simpa only [he] using cofacet0253
        ·
          by_cases h255 : i.val < 255
          ·
            have he : (⟨254, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 254 = i.val
              omega
            simpa only [he] using cofacet0254
          ·
            have he : (⟨255, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 255 = i.val
              omega
            simpa only [he] using cofacet0255

private theorem cofacetGroup0008 (i : Fin 1069)
    (hlo : 256 ≤ i.val) (hhi : i.val < 288) :
    cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h272 : i.val < 272
  ·
    by_cases h264 : i.val < 264
    ·
      by_cases h260 : i.val < 260
      ·
        by_cases h258 : i.val < 258
        ·
          by_cases h257 : i.val < 257
          ·
            have he : (⟨256, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 256 = i.val
              omega
            simpa only [he] using cofacet0256
          ·
            have he : (⟨257, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 257 = i.val
              omega
            simpa only [he] using cofacet0257
        ·
          by_cases h259 : i.val < 259
          ·
            have he : (⟨258, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 258 = i.val
              omega
            simpa only [he] using cofacet0258
          ·
            have he : (⟨259, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 259 = i.val
              omega
            simpa only [he] using cofacet0259
      ·
        by_cases h262 : i.val < 262
        ·
          by_cases h261 : i.val < 261
          ·
            have he : (⟨260, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 260 = i.val
              omega
            simpa only [he] using cofacet0260
          ·
            have he : (⟨261, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 261 = i.val
              omega
            simpa only [he] using cofacet0261
        ·
          by_cases h263 : i.val < 263
          ·
            have he : (⟨262, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 262 = i.val
              omega
            simpa only [he] using cofacet0262
          ·
            have he : (⟨263, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 263 = i.val
              omega
            simpa only [he] using cofacet0263
    ·
      by_cases h268 : i.val < 268
      ·
        by_cases h266 : i.val < 266
        ·
          by_cases h265 : i.val < 265
          ·
            have he : (⟨264, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 264 = i.val
              omega
            simpa only [he] using cofacet0264
          ·
            have he : (⟨265, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 265 = i.val
              omega
            simpa only [he] using cofacet0265
        ·
          by_cases h267 : i.val < 267
          ·
            have he : (⟨266, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 266 = i.val
              omega
            simpa only [he] using cofacet0266
          ·
            have he : (⟨267, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 267 = i.val
              omega
            simpa only [he] using cofacet0267
      ·
        by_cases h270 : i.val < 270
        ·
          by_cases h269 : i.val < 269
          ·
            have he : (⟨268, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 268 = i.val
              omega
            simpa only [he] using cofacet0268
          ·
            have he : (⟨269, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 269 = i.val
              omega
            simpa only [he] using cofacet0269
        ·
          by_cases h271 : i.val < 271
          ·
            have he : (⟨270, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 270 = i.val
              omega
            simpa only [he] using cofacet0270
          ·
            have he : (⟨271, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 271 = i.val
              omega
            simpa only [he] using cofacet0271
  ·
    by_cases h280 : i.val < 280
    ·
      by_cases h276 : i.val < 276
      ·
        by_cases h274 : i.val < 274
        ·
          by_cases h273 : i.val < 273
          ·
            have he : (⟨272, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 272 = i.val
              omega
            simpa only [he] using cofacet0272
          ·
            have he : (⟨273, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 273 = i.val
              omega
            simpa only [he] using cofacet0273
        ·
          by_cases h275 : i.val < 275
          ·
            have he : (⟨274, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 274 = i.val
              omega
            simpa only [he] using cofacet0274
          ·
            have he : (⟨275, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 275 = i.val
              omega
            simpa only [he] using cofacet0275
      ·
        by_cases h278 : i.val < 278
        ·
          by_cases h277 : i.val < 277
          ·
            have he : (⟨276, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 276 = i.val
              omega
            simpa only [he] using cofacet0276
          ·
            have he : (⟨277, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 277 = i.val
              omega
            simpa only [he] using cofacet0277
        ·
          by_cases h279 : i.val < 279
          ·
            have he : (⟨278, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 278 = i.val
              omega
            simpa only [he] using cofacet0278
          ·
            have he : (⟨279, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 279 = i.val
              omega
            simpa only [he] using cofacet0279
    ·
      by_cases h284 : i.val < 284
      ·
        by_cases h282 : i.val < 282
        ·
          by_cases h281 : i.val < 281
          ·
            have he : (⟨280, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 280 = i.val
              omega
            simpa only [he] using cofacet0280
          ·
            have he : (⟨281, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 281 = i.val
              omega
            simpa only [he] using cofacet0281
        ·
          by_cases h283 : i.val < 283
          ·
            have he : (⟨282, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 282 = i.val
              omega
            simpa only [he] using cofacet0282
          ·
            have he : (⟨283, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 283 = i.val
              omega
            simpa only [he] using cofacet0283
      ·
        by_cases h286 : i.val < 286
        ·
          by_cases h285 : i.val < 285
          ·
            have he : (⟨284, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 284 = i.val
              omega
            simpa only [he] using cofacet0284
          ·
            have he : (⟨285, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 285 = i.val
              omega
            simpa only [he] using cofacet0285
        ·
          by_cases h287 : i.val < 287
          ·
            have he : (⟨286, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 286 = i.val
              omega
            simpa only [he] using cofacet0286
          ·
            have he : (⟨287, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 287 = i.val
              omega
            simpa only [he] using cofacet0287

private theorem cofacetGroup0009 (i : Fin 1069)
    (hlo : 288 ≤ i.val) (hhi : i.val < 320) :
    cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h304 : i.val < 304
  ·
    by_cases h296 : i.val < 296
    ·
      by_cases h292 : i.val < 292
      ·
        by_cases h290 : i.val < 290
        ·
          by_cases h289 : i.val < 289
          ·
            have he : (⟨288, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 288 = i.val
              omega
            simpa only [he] using cofacet0288
          ·
            have he : (⟨289, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 289 = i.val
              omega
            simpa only [he] using cofacet0289
        ·
          by_cases h291 : i.val < 291
          ·
            have he : (⟨290, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 290 = i.val
              omega
            simpa only [he] using cofacet0290
          ·
            have he : (⟨291, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 291 = i.val
              omega
            simpa only [he] using cofacet0291
      ·
        by_cases h294 : i.val < 294
        ·
          by_cases h293 : i.val < 293
          ·
            have he : (⟨292, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 292 = i.val
              omega
            simpa only [he] using cofacet0292
          ·
            have he : (⟨293, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 293 = i.val
              omega
            simpa only [he] using cofacet0293
        ·
          by_cases h295 : i.val < 295
          ·
            have he : (⟨294, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 294 = i.val
              omega
            simpa only [he] using cofacet0294
          ·
            have he : (⟨295, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 295 = i.val
              omega
            simpa only [he] using cofacet0295
    ·
      by_cases h300 : i.val < 300
      ·
        by_cases h298 : i.val < 298
        ·
          by_cases h297 : i.val < 297
          ·
            have he : (⟨296, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 296 = i.val
              omega
            simpa only [he] using cofacet0296
          ·
            have he : (⟨297, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 297 = i.val
              omega
            simpa only [he] using cofacet0297
        ·
          by_cases h299 : i.val < 299
          ·
            have he : (⟨298, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 298 = i.val
              omega
            simpa only [he] using cofacet0298
          ·
            have he : (⟨299, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 299 = i.val
              omega
            simpa only [he] using cofacet0299
      ·
        by_cases h302 : i.val < 302
        ·
          by_cases h301 : i.val < 301
          ·
            have he : (⟨300, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 300 = i.val
              omega
            simpa only [he] using cofacet0300
          ·
            have he : (⟨301, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 301 = i.val
              omega
            simpa only [he] using cofacet0301
        ·
          by_cases h303 : i.val < 303
          ·
            have he : (⟨302, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 302 = i.val
              omega
            simpa only [he] using cofacet0302
          ·
            have he : (⟨303, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 303 = i.val
              omega
            simpa only [he] using cofacet0303
  ·
    by_cases h312 : i.val < 312
    ·
      by_cases h308 : i.val < 308
      ·
        by_cases h306 : i.val < 306
        ·
          by_cases h305 : i.val < 305
          ·
            have he : (⟨304, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 304 = i.val
              omega
            simpa only [he] using cofacet0304
          ·
            have he : (⟨305, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 305 = i.val
              omega
            simpa only [he] using cofacet0305
        ·
          by_cases h307 : i.val < 307
          ·
            have he : (⟨306, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 306 = i.val
              omega
            simpa only [he] using cofacet0306
          ·
            have he : (⟨307, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 307 = i.val
              omega
            simpa only [he] using cofacet0307
      ·
        by_cases h310 : i.val < 310
        ·
          by_cases h309 : i.val < 309
          ·
            have he : (⟨308, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 308 = i.val
              omega
            simpa only [he] using cofacet0308
          ·
            have he : (⟨309, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 309 = i.val
              omega
            simpa only [he] using cofacet0309
        ·
          by_cases h311 : i.val < 311
          ·
            have he : (⟨310, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 310 = i.val
              omega
            simpa only [he] using cofacet0310
          ·
            have he : (⟨311, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 311 = i.val
              omega
            simpa only [he] using cofacet0311
    ·
      by_cases h316 : i.val < 316
      ·
        by_cases h314 : i.val < 314
        ·
          by_cases h313 : i.val < 313
          ·
            have he : (⟨312, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 312 = i.val
              omega
            simpa only [he] using cofacet0312
          ·
            have he : (⟨313, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 313 = i.val
              omega
            simpa only [he] using cofacet0313
        ·
          by_cases h315 : i.val < 315
          ·
            have he : (⟨314, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 314 = i.val
              omega
            simpa only [he] using cofacet0314
          ·
            have he : (⟨315, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 315 = i.val
              omega
            simpa only [he] using cofacet0315
      ·
        by_cases h318 : i.val < 318
        ·
          by_cases h317 : i.val < 317
          ·
            have he : (⟨316, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 316 = i.val
              omega
            simpa only [he] using cofacet0316
          ·
            have he : (⟨317, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 317 = i.val
              omega
            simpa only [he] using cofacet0317
        ·
          by_cases h319 : i.val < 319
          ·
            have he : (⟨318, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 318 = i.val
              omega
            simpa only [he] using cofacet0318
          ·
            have he : (⟨319, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 319 = i.val
              omega
            simpa only [he] using cofacet0319

private theorem cofacetGroup0010 (i : Fin 1069)
    (hlo : 320 ≤ i.val) (hhi : i.val < 352) :
    cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h336 : i.val < 336
  ·
    by_cases h328 : i.val < 328
    ·
      by_cases h324 : i.val < 324
      ·
        by_cases h322 : i.val < 322
        ·
          by_cases h321 : i.val < 321
          ·
            have he : (⟨320, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 320 = i.val
              omega
            simpa only [he] using cofacet0320
          ·
            have he : (⟨321, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 321 = i.val
              omega
            simpa only [he] using cofacet0321
        ·
          by_cases h323 : i.val < 323
          ·
            have he : (⟨322, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 322 = i.val
              omega
            simpa only [he] using cofacet0322
          ·
            have he : (⟨323, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 323 = i.val
              omega
            simpa only [he] using cofacet0323
      ·
        by_cases h326 : i.val < 326
        ·
          by_cases h325 : i.val < 325
          ·
            have he : (⟨324, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 324 = i.val
              omega
            simpa only [he] using cofacet0324
          ·
            have he : (⟨325, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 325 = i.val
              omega
            simpa only [he] using cofacet0325
        ·
          by_cases h327 : i.val < 327
          ·
            have he : (⟨326, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 326 = i.val
              omega
            simpa only [he] using cofacet0326
          ·
            have he : (⟨327, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 327 = i.val
              omega
            simpa only [he] using cofacet0327
    ·
      by_cases h332 : i.val < 332
      ·
        by_cases h330 : i.val < 330
        ·
          by_cases h329 : i.val < 329
          ·
            have he : (⟨328, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 328 = i.val
              omega
            simpa only [he] using cofacet0328
          ·
            have he : (⟨329, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 329 = i.val
              omega
            simpa only [he] using cofacet0329
        ·
          by_cases h331 : i.val < 331
          ·
            have he : (⟨330, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 330 = i.val
              omega
            simpa only [he] using cofacet0330
          ·
            have he : (⟨331, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 331 = i.val
              omega
            simpa only [he] using cofacet0331
      ·
        by_cases h334 : i.val < 334
        ·
          by_cases h333 : i.val < 333
          ·
            have he : (⟨332, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 332 = i.val
              omega
            simpa only [he] using cofacet0332
          ·
            have he : (⟨333, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 333 = i.val
              omega
            simpa only [he] using cofacet0333
        ·
          by_cases h335 : i.val < 335
          ·
            have he : (⟨334, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 334 = i.val
              omega
            simpa only [he] using cofacet0334
          ·
            have he : (⟨335, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 335 = i.val
              omega
            simpa only [he] using cofacet0335
  ·
    by_cases h344 : i.val < 344
    ·
      by_cases h340 : i.val < 340
      ·
        by_cases h338 : i.val < 338
        ·
          by_cases h337 : i.val < 337
          ·
            have he : (⟨336, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 336 = i.val
              omega
            simpa only [he] using cofacet0336
          ·
            have he : (⟨337, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 337 = i.val
              omega
            simpa only [he] using cofacet0337
        ·
          by_cases h339 : i.val < 339
          ·
            have he : (⟨338, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 338 = i.val
              omega
            simpa only [he] using cofacet0338
          ·
            have he : (⟨339, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 339 = i.val
              omega
            simpa only [he] using cofacet0339
      ·
        by_cases h342 : i.val < 342
        ·
          by_cases h341 : i.val < 341
          ·
            have he : (⟨340, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 340 = i.val
              omega
            simpa only [he] using cofacet0340
          ·
            have he : (⟨341, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 341 = i.val
              omega
            simpa only [he] using cofacet0341
        ·
          by_cases h343 : i.val < 343
          ·
            have he : (⟨342, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 342 = i.val
              omega
            simpa only [he] using cofacet0342
          ·
            have he : (⟨343, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 343 = i.val
              omega
            simpa only [he] using cofacet0343
    ·
      by_cases h348 : i.val < 348
      ·
        by_cases h346 : i.val < 346
        ·
          by_cases h345 : i.val < 345
          ·
            have he : (⟨344, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 344 = i.val
              omega
            simpa only [he] using cofacet0344
          ·
            have he : (⟨345, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 345 = i.val
              omega
            simpa only [he] using cofacet0345
        ·
          by_cases h347 : i.val < 347
          ·
            have he : (⟨346, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 346 = i.val
              omega
            simpa only [he] using cofacet0346
          ·
            have he : (⟨347, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 347 = i.val
              omega
            simpa only [he] using cofacet0347
      ·
        by_cases h350 : i.val < 350
        ·
          by_cases h349 : i.val < 349
          ·
            have he : (⟨348, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 348 = i.val
              omega
            simpa only [he] using cofacet0348
          ·
            have he : (⟨349, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 349 = i.val
              omega
            simpa only [he] using cofacet0349
        ·
          by_cases h351 : i.val < 351
          ·
            have he : (⟨350, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 350 = i.val
              omega
            simpa only [he] using cofacet0350
          ·
            have he : (⟨351, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 351 = i.val
              omega
            simpa only [he] using cofacet0351

private theorem cofacetGroup0011 (i : Fin 1069)
    (hlo : 352 ≤ i.val) (hhi : i.val < 384) :
    cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h368 : i.val < 368
  ·
    by_cases h360 : i.val < 360
    ·
      by_cases h356 : i.val < 356
      ·
        by_cases h354 : i.val < 354
        ·
          by_cases h353 : i.val < 353
          ·
            have he : (⟨352, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 352 = i.val
              omega
            simpa only [he] using cofacet0352
          ·
            have he : (⟨353, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 353 = i.val
              omega
            simpa only [he] using cofacet0353
        ·
          by_cases h355 : i.val < 355
          ·
            have he : (⟨354, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 354 = i.val
              omega
            simpa only [he] using cofacet0354
          ·
            have he : (⟨355, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 355 = i.val
              omega
            simpa only [he] using cofacet0355
      ·
        by_cases h358 : i.val < 358
        ·
          by_cases h357 : i.val < 357
          ·
            have he : (⟨356, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 356 = i.val
              omega
            simpa only [he] using cofacet0356
          ·
            have he : (⟨357, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 357 = i.val
              omega
            simpa only [he] using cofacet0357
        ·
          by_cases h359 : i.val < 359
          ·
            have he : (⟨358, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 358 = i.val
              omega
            simpa only [he] using cofacet0358
          ·
            have he : (⟨359, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 359 = i.val
              omega
            simpa only [he] using cofacet0359
    ·
      by_cases h364 : i.val < 364
      ·
        by_cases h362 : i.val < 362
        ·
          by_cases h361 : i.val < 361
          ·
            have he : (⟨360, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 360 = i.val
              omega
            simpa only [he] using cofacet0360
          ·
            have he : (⟨361, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 361 = i.val
              omega
            simpa only [he] using cofacet0361
        ·
          by_cases h363 : i.val < 363
          ·
            have he : (⟨362, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 362 = i.val
              omega
            simpa only [he] using cofacet0362
          ·
            have he : (⟨363, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 363 = i.val
              omega
            simpa only [he] using cofacet0363
      ·
        by_cases h366 : i.val < 366
        ·
          by_cases h365 : i.val < 365
          ·
            have he : (⟨364, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 364 = i.val
              omega
            simpa only [he] using cofacet0364
          ·
            have he : (⟨365, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 365 = i.val
              omega
            simpa only [he] using cofacet0365
        ·
          by_cases h367 : i.val < 367
          ·
            have he : (⟨366, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 366 = i.val
              omega
            simpa only [he] using cofacet0366
          ·
            have he : (⟨367, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 367 = i.val
              omega
            simpa only [he] using cofacet0367
  ·
    by_cases h376 : i.val < 376
    ·
      by_cases h372 : i.val < 372
      ·
        by_cases h370 : i.val < 370
        ·
          by_cases h369 : i.val < 369
          ·
            have he : (⟨368, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 368 = i.val
              omega
            simpa only [he] using cofacet0368
          ·
            have he : (⟨369, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 369 = i.val
              omega
            simpa only [he] using cofacet0369
        ·
          by_cases h371 : i.val < 371
          ·
            have he : (⟨370, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 370 = i.val
              omega
            simpa only [he] using cofacet0370
          ·
            have he : (⟨371, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 371 = i.val
              omega
            simpa only [he] using cofacet0371
      ·
        by_cases h374 : i.val < 374
        ·
          by_cases h373 : i.val < 373
          ·
            have he : (⟨372, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 372 = i.val
              omega
            simpa only [he] using cofacet0372
          ·
            have he : (⟨373, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 373 = i.val
              omega
            simpa only [he] using cofacet0373
        ·
          by_cases h375 : i.val < 375
          ·
            have he : (⟨374, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 374 = i.val
              omega
            simpa only [he] using cofacet0374
          ·
            have he : (⟨375, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 375 = i.val
              omega
            simpa only [he] using cofacet0375
    ·
      by_cases h380 : i.val < 380
      ·
        by_cases h378 : i.val < 378
        ·
          by_cases h377 : i.val < 377
          ·
            have he : (⟨376, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 376 = i.val
              omega
            simpa only [he] using cofacet0376
          ·
            have he : (⟨377, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 377 = i.val
              omega
            simpa only [he] using cofacet0377
        ·
          by_cases h379 : i.val < 379
          ·
            have he : (⟨378, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 378 = i.val
              omega
            simpa only [he] using cofacet0378
          ·
            have he : (⟨379, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 379 = i.val
              omega
            simpa only [he] using cofacet0379
      ·
        by_cases h382 : i.val < 382
        ·
          by_cases h381 : i.val < 381
          ·
            have he : (⟨380, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 380 = i.val
              omega
            simpa only [he] using cofacet0380
          ·
            have he : (⟨381, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 381 = i.val
              omega
            simpa only [he] using cofacet0381
        ·
          by_cases h383 : i.val < 383
          ·
            have he : (⟨382, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 382 = i.val
              omega
            simpa only [he] using cofacet0382
          ·
            have he : (⟨383, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 383 = i.val
              omega
            simpa only [he] using cofacet0383

private theorem cofacetGroup0012 (i : Fin 1069)
    (hlo : 384 ≤ i.val) (hhi : i.val < 416) :
    cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h400 : i.val < 400
  ·
    by_cases h392 : i.val < 392
    ·
      by_cases h388 : i.val < 388
      ·
        by_cases h386 : i.val < 386
        ·
          by_cases h385 : i.val < 385
          ·
            have he : (⟨384, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 384 = i.val
              omega
            simpa only [he] using cofacet0384
          ·
            have he : (⟨385, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 385 = i.val
              omega
            simpa only [he] using cofacet0385
        ·
          by_cases h387 : i.val < 387
          ·
            have he : (⟨386, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 386 = i.val
              omega
            simpa only [he] using cofacet0386
          ·
            have he : (⟨387, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 387 = i.val
              omega
            simpa only [he] using cofacet0387
      ·
        by_cases h390 : i.val < 390
        ·
          by_cases h389 : i.val < 389
          ·
            have he : (⟨388, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 388 = i.val
              omega
            simpa only [he] using cofacet0388
          ·
            have he : (⟨389, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 389 = i.val
              omega
            simpa only [he] using cofacet0389
        ·
          by_cases h391 : i.val < 391
          ·
            have he : (⟨390, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 390 = i.val
              omega
            simpa only [he] using cofacet0390
          ·
            have he : (⟨391, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 391 = i.val
              omega
            simpa only [he] using cofacet0391
    ·
      by_cases h396 : i.val < 396
      ·
        by_cases h394 : i.val < 394
        ·
          by_cases h393 : i.val < 393
          ·
            have he : (⟨392, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 392 = i.val
              omega
            simpa only [he] using cofacet0392
          ·
            have he : (⟨393, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 393 = i.val
              omega
            simpa only [he] using cofacet0393
        ·
          by_cases h395 : i.val < 395
          ·
            have he : (⟨394, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 394 = i.val
              omega
            simpa only [he] using cofacet0394
          ·
            have he : (⟨395, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 395 = i.val
              omega
            simpa only [he] using cofacet0395
      ·
        by_cases h398 : i.val < 398
        ·
          by_cases h397 : i.val < 397
          ·
            have he : (⟨396, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 396 = i.val
              omega
            simpa only [he] using cofacet0396
          ·
            have he : (⟨397, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 397 = i.val
              omega
            simpa only [he] using cofacet0397
        ·
          by_cases h399 : i.val < 399
          ·
            have he : (⟨398, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 398 = i.val
              omega
            simpa only [he] using cofacet0398
          ·
            have he : (⟨399, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 399 = i.val
              omega
            simpa only [he] using cofacet0399
  ·
    by_cases h408 : i.val < 408
    ·
      by_cases h404 : i.val < 404
      ·
        by_cases h402 : i.val < 402
        ·
          by_cases h401 : i.val < 401
          ·
            have he : (⟨400, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 400 = i.val
              omega
            simpa only [he] using cofacet0400
          ·
            have he : (⟨401, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 401 = i.val
              omega
            simpa only [he] using cofacet0401
        ·
          by_cases h403 : i.val < 403
          ·
            have he : (⟨402, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 402 = i.val
              omega
            simpa only [he] using cofacet0402
          ·
            have he : (⟨403, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 403 = i.val
              omega
            simpa only [he] using cofacet0403
      ·
        by_cases h406 : i.val < 406
        ·
          by_cases h405 : i.val < 405
          ·
            have he : (⟨404, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 404 = i.val
              omega
            simpa only [he] using cofacet0404
          ·
            have he : (⟨405, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 405 = i.val
              omega
            simpa only [he] using cofacet0405
        ·
          by_cases h407 : i.val < 407
          ·
            have he : (⟨406, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 406 = i.val
              omega
            simpa only [he] using cofacet0406
          ·
            have he : (⟨407, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 407 = i.val
              omega
            simpa only [he] using cofacet0407
    ·
      by_cases h412 : i.val < 412
      ·
        by_cases h410 : i.val < 410
        ·
          by_cases h409 : i.val < 409
          ·
            have he : (⟨408, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 408 = i.val
              omega
            simpa only [he] using cofacet0408
          ·
            have he : (⟨409, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 409 = i.val
              omega
            simpa only [he] using cofacet0409
        ·
          by_cases h411 : i.val < 411
          ·
            have he : (⟨410, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 410 = i.val
              omega
            simpa only [he] using cofacet0410
          ·
            have he : (⟨411, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 411 = i.val
              omega
            simpa only [he] using cofacet0411
      ·
        by_cases h414 : i.val < 414
        ·
          by_cases h413 : i.val < 413
          ·
            have he : (⟨412, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 412 = i.val
              omega
            simpa only [he] using cofacet0412
          ·
            have he : (⟨413, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 413 = i.val
              omega
            simpa only [he] using cofacet0413
        ·
          by_cases h415 : i.val < 415
          ·
            have he : (⟨414, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 414 = i.val
              omega
            simpa only [he] using cofacet0414
          ·
            have he : (⟨415, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 415 = i.val
              omega
            simpa only [he] using cofacet0415

private theorem cofacetGroup0013 (i : Fin 1069)
    (hlo : 416 ≤ i.val) (hhi : i.val < 448) :
    cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h432 : i.val < 432
  ·
    by_cases h424 : i.val < 424
    ·
      by_cases h420 : i.val < 420
      ·
        by_cases h418 : i.val < 418
        ·
          by_cases h417 : i.val < 417
          ·
            have he : (⟨416, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 416 = i.val
              omega
            simpa only [he] using cofacet0416
          ·
            have he : (⟨417, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 417 = i.val
              omega
            simpa only [he] using cofacet0417
        ·
          by_cases h419 : i.val < 419
          ·
            have he : (⟨418, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 418 = i.val
              omega
            simpa only [he] using cofacet0418
          ·
            have he : (⟨419, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 419 = i.val
              omega
            simpa only [he] using cofacet0419
      ·
        by_cases h422 : i.val < 422
        ·
          by_cases h421 : i.val < 421
          ·
            have he : (⟨420, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 420 = i.val
              omega
            simpa only [he] using cofacet0420
          ·
            have he : (⟨421, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 421 = i.val
              omega
            simpa only [he] using cofacet0421
        ·
          by_cases h423 : i.val < 423
          ·
            have he : (⟨422, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 422 = i.val
              omega
            simpa only [he] using cofacet0422
          ·
            have he : (⟨423, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 423 = i.val
              omega
            simpa only [he] using cofacet0423
    ·
      by_cases h428 : i.val < 428
      ·
        by_cases h426 : i.val < 426
        ·
          by_cases h425 : i.val < 425
          ·
            have he : (⟨424, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 424 = i.val
              omega
            simpa only [he] using cofacet0424
          ·
            have he : (⟨425, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 425 = i.val
              omega
            simpa only [he] using cofacet0425
        ·
          by_cases h427 : i.val < 427
          ·
            have he : (⟨426, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 426 = i.val
              omega
            simpa only [he] using cofacet0426
          ·
            have he : (⟨427, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 427 = i.val
              omega
            simpa only [he] using cofacet0427
      ·
        by_cases h430 : i.val < 430
        ·
          by_cases h429 : i.val < 429
          ·
            have he : (⟨428, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 428 = i.val
              omega
            simpa only [he] using cofacet0428
          ·
            have he : (⟨429, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 429 = i.val
              omega
            simpa only [he] using cofacet0429
        ·
          by_cases h431 : i.val < 431
          ·
            have he : (⟨430, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 430 = i.val
              omega
            simpa only [he] using cofacet0430
          ·
            have he : (⟨431, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 431 = i.val
              omega
            simpa only [he] using cofacet0431
  ·
    by_cases h440 : i.val < 440
    ·
      by_cases h436 : i.val < 436
      ·
        by_cases h434 : i.val < 434
        ·
          by_cases h433 : i.val < 433
          ·
            have he : (⟨432, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 432 = i.val
              omega
            simpa only [he] using cofacet0432
          ·
            have he : (⟨433, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 433 = i.val
              omega
            simpa only [he] using cofacet0433
        ·
          by_cases h435 : i.val < 435
          ·
            have he : (⟨434, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 434 = i.val
              omega
            simpa only [he] using cofacet0434
          ·
            have he : (⟨435, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 435 = i.val
              omega
            simpa only [he] using cofacet0435
      ·
        by_cases h438 : i.val < 438
        ·
          by_cases h437 : i.val < 437
          ·
            have he : (⟨436, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 436 = i.val
              omega
            simpa only [he] using cofacet0436
          ·
            have he : (⟨437, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 437 = i.val
              omega
            simpa only [he] using cofacet0437
        ·
          by_cases h439 : i.val < 439
          ·
            have he : (⟨438, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 438 = i.val
              omega
            simpa only [he] using cofacet0438
          ·
            have he : (⟨439, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 439 = i.val
              omega
            simpa only [he] using cofacet0439
    ·
      by_cases h444 : i.val < 444
      ·
        by_cases h442 : i.val < 442
        ·
          by_cases h441 : i.val < 441
          ·
            have he : (⟨440, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 440 = i.val
              omega
            simpa only [he] using cofacet0440
          ·
            have he : (⟨441, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 441 = i.val
              omega
            simpa only [he] using cofacet0441
        ·
          by_cases h443 : i.val < 443
          ·
            have he : (⟨442, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 442 = i.val
              omega
            simpa only [he] using cofacet0442
          ·
            have he : (⟨443, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 443 = i.val
              omega
            simpa only [he] using cofacet0443
      ·
        by_cases h446 : i.val < 446
        ·
          by_cases h445 : i.val < 445
          ·
            have he : (⟨444, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 444 = i.val
              omega
            simpa only [he] using cofacet0444
          ·
            have he : (⟨445, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 445 = i.val
              omega
            simpa only [he] using cofacet0445
        ·
          by_cases h447 : i.val < 447
          ·
            have he : (⟨446, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 446 = i.val
              omega
            simpa only [he] using cofacet0446
          ·
            have he : (⟨447, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 447 = i.val
              omega
            simpa only [he] using cofacet0447

private theorem cofacetGroup0014 (i : Fin 1069)
    (hlo : 448 ≤ i.val) (hhi : i.val < 480) :
    cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h464 : i.val < 464
  ·
    by_cases h456 : i.val < 456
    ·
      by_cases h452 : i.val < 452
      ·
        by_cases h450 : i.val < 450
        ·
          by_cases h449 : i.val < 449
          ·
            have he : (⟨448, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 448 = i.val
              omega
            simpa only [he] using cofacet0448
          ·
            have he : (⟨449, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 449 = i.val
              omega
            simpa only [he] using cofacet0449
        ·
          by_cases h451 : i.val < 451
          ·
            have he : (⟨450, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 450 = i.val
              omega
            simpa only [he] using cofacet0450
          ·
            have he : (⟨451, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 451 = i.val
              omega
            simpa only [he] using cofacet0451
      ·
        by_cases h454 : i.val < 454
        ·
          by_cases h453 : i.val < 453
          ·
            have he : (⟨452, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 452 = i.val
              omega
            simpa only [he] using cofacet0452
          ·
            have he : (⟨453, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 453 = i.val
              omega
            simpa only [he] using cofacet0453
        ·
          by_cases h455 : i.val < 455
          ·
            have he : (⟨454, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 454 = i.val
              omega
            simpa only [he] using cofacet0454
          ·
            have he : (⟨455, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 455 = i.val
              omega
            simpa only [he] using cofacet0455
    ·
      by_cases h460 : i.val < 460
      ·
        by_cases h458 : i.val < 458
        ·
          by_cases h457 : i.val < 457
          ·
            have he : (⟨456, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 456 = i.val
              omega
            simpa only [he] using cofacet0456
          ·
            have he : (⟨457, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 457 = i.val
              omega
            simpa only [he] using cofacet0457
        ·
          by_cases h459 : i.val < 459
          ·
            have he : (⟨458, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 458 = i.val
              omega
            simpa only [he] using cofacet0458
          ·
            have he : (⟨459, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 459 = i.val
              omega
            simpa only [he] using cofacet0459
      ·
        by_cases h462 : i.val < 462
        ·
          by_cases h461 : i.val < 461
          ·
            have he : (⟨460, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 460 = i.val
              omega
            simpa only [he] using cofacet0460
          ·
            have he : (⟨461, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 461 = i.val
              omega
            simpa only [he] using cofacet0461
        ·
          by_cases h463 : i.val < 463
          ·
            have he : (⟨462, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 462 = i.val
              omega
            simpa only [he] using cofacet0462
          ·
            have he : (⟨463, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 463 = i.val
              omega
            simpa only [he] using cofacet0463
  ·
    by_cases h472 : i.val < 472
    ·
      by_cases h468 : i.val < 468
      ·
        by_cases h466 : i.val < 466
        ·
          by_cases h465 : i.val < 465
          ·
            have he : (⟨464, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 464 = i.val
              omega
            simpa only [he] using cofacet0464
          ·
            have he : (⟨465, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 465 = i.val
              omega
            simpa only [he] using cofacet0465
        ·
          by_cases h467 : i.val < 467
          ·
            have he : (⟨466, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 466 = i.val
              omega
            simpa only [he] using cofacet0466
          ·
            have he : (⟨467, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 467 = i.val
              omega
            simpa only [he] using cofacet0467
      ·
        by_cases h470 : i.val < 470
        ·
          by_cases h469 : i.val < 469
          ·
            have he : (⟨468, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 468 = i.val
              omega
            simpa only [he] using cofacet0468
          ·
            have he : (⟨469, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 469 = i.val
              omega
            simpa only [he] using cofacet0469
        ·
          by_cases h471 : i.val < 471
          ·
            have he : (⟨470, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 470 = i.val
              omega
            simpa only [he] using cofacet0470
          ·
            have he : (⟨471, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 471 = i.val
              omega
            simpa only [he] using cofacet0471
    ·
      by_cases h476 : i.val < 476
      ·
        by_cases h474 : i.val < 474
        ·
          by_cases h473 : i.val < 473
          ·
            have he : (⟨472, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 472 = i.val
              omega
            simpa only [he] using cofacet0472
          ·
            have he : (⟨473, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 473 = i.val
              omega
            simpa only [he] using cofacet0473
        ·
          by_cases h475 : i.val < 475
          ·
            have he : (⟨474, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 474 = i.val
              omega
            simpa only [he] using cofacet0474
          ·
            have he : (⟨475, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 475 = i.val
              omega
            simpa only [he] using cofacet0475
      ·
        by_cases h478 : i.val < 478
        ·
          by_cases h477 : i.val < 477
          ·
            have he : (⟨476, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 476 = i.val
              omega
            simpa only [he] using cofacet0476
          ·
            have he : (⟨477, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 477 = i.val
              omega
            simpa only [he] using cofacet0477
        ·
          by_cases h479 : i.val < 479
          ·
            have he : (⟨478, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 478 = i.val
              omega
            simpa only [he] using cofacet0478
          ·
            have he : (⟨479, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 479 = i.val
              omega
            simpa only [he] using cofacet0479

private theorem cofacetGroup0015 (i : Fin 1069)
    (hlo : 480 ≤ i.val) (hhi : i.val < 512) :
    cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h496 : i.val < 496
  ·
    by_cases h488 : i.val < 488
    ·
      by_cases h484 : i.val < 484
      ·
        by_cases h482 : i.val < 482
        ·
          by_cases h481 : i.val < 481
          ·
            have he : (⟨480, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 480 = i.val
              omega
            simpa only [he] using cofacet0480
          ·
            have he : (⟨481, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 481 = i.val
              omega
            simpa only [he] using cofacet0481
        ·
          by_cases h483 : i.val < 483
          ·
            have he : (⟨482, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 482 = i.val
              omega
            simpa only [he] using cofacet0482
          ·
            have he : (⟨483, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 483 = i.val
              omega
            simpa only [he] using cofacet0483
      ·
        by_cases h486 : i.val < 486
        ·
          by_cases h485 : i.val < 485
          ·
            have he : (⟨484, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 484 = i.val
              omega
            simpa only [he] using cofacet0484
          ·
            have he : (⟨485, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 485 = i.val
              omega
            simpa only [he] using cofacet0485
        ·
          by_cases h487 : i.val < 487
          ·
            have he : (⟨486, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 486 = i.val
              omega
            simpa only [he] using cofacet0486
          ·
            have he : (⟨487, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 487 = i.val
              omega
            simpa only [he] using cofacet0487
    ·
      by_cases h492 : i.val < 492
      ·
        by_cases h490 : i.val < 490
        ·
          by_cases h489 : i.val < 489
          ·
            have he : (⟨488, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 488 = i.val
              omega
            simpa only [he] using cofacet0488
          ·
            have he : (⟨489, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 489 = i.val
              omega
            simpa only [he] using cofacet0489
        ·
          by_cases h491 : i.val < 491
          ·
            have he : (⟨490, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 490 = i.val
              omega
            simpa only [he] using cofacet0490
          ·
            have he : (⟨491, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 491 = i.val
              omega
            simpa only [he] using cofacet0491
      ·
        by_cases h494 : i.val < 494
        ·
          by_cases h493 : i.val < 493
          ·
            have he : (⟨492, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 492 = i.val
              omega
            simpa only [he] using cofacet0492
          ·
            have he : (⟨493, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 493 = i.val
              omega
            simpa only [he] using cofacet0493
        ·
          by_cases h495 : i.val < 495
          ·
            have he : (⟨494, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 494 = i.val
              omega
            simpa only [he] using cofacet0494
          ·
            have he : (⟨495, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 495 = i.val
              omega
            simpa only [he] using cofacet0495
  ·
    by_cases h504 : i.val < 504
    ·
      by_cases h500 : i.val < 500
      ·
        by_cases h498 : i.val < 498
        ·
          by_cases h497 : i.val < 497
          ·
            have he : (⟨496, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 496 = i.val
              omega
            simpa only [he] using cofacet0496
          ·
            have he : (⟨497, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 497 = i.val
              omega
            simpa only [he] using cofacet0497
        ·
          by_cases h499 : i.val < 499
          ·
            have he : (⟨498, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 498 = i.val
              omega
            simpa only [he] using cofacet0498
          ·
            have he : (⟨499, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 499 = i.val
              omega
            simpa only [he] using cofacet0499
      ·
        by_cases h502 : i.val < 502
        ·
          by_cases h501 : i.val < 501
          ·
            have he : (⟨500, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 500 = i.val
              omega
            simpa only [he] using cofacet0500
          ·
            have he : (⟨501, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 501 = i.val
              omega
            simpa only [he] using cofacet0501
        ·
          by_cases h503 : i.val < 503
          ·
            have he : (⟨502, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 502 = i.val
              omega
            simpa only [he] using cofacet0502
          ·
            have he : (⟨503, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 503 = i.val
              omega
            simpa only [he] using cofacet0503
    ·
      by_cases h508 : i.val < 508
      ·
        by_cases h506 : i.val < 506
        ·
          by_cases h505 : i.val < 505
          ·
            have he : (⟨504, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 504 = i.val
              omega
            simpa only [he] using cofacet0504
          ·
            have he : (⟨505, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 505 = i.val
              omega
            simpa only [he] using cofacet0505
        ·
          by_cases h507 : i.val < 507
          ·
            have he : (⟨506, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 506 = i.val
              omega
            simpa only [he] using cofacet0506
          ·
            have he : (⟨507, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 507 = i.val
              omega
            simpa only [he] using cofacet0507
      ·
        by_cases h510 : i.val < 510
        ·
          by_cases h509 : i.val < 509
          ·
            have he : (⟨508, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 508 = i.val
              omega
            simpa only [he] using cofacet0508
          ·
            have he : (⟨509, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 509 = i.val
              omega
            simpa only [he] using cofacet0509
        ·
          by_cases h511 : i.val < 511
          ·
            have he : (⟨510, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 510 = i.val
              omega
            simpa only [he] using cofacet0510
          ·
            have he : (⟨511, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 511 = i.val
              omega
            simpa only [he] using cofacet0511

private theorem cofacetGroup0016 (i : Fin 1069)
    (hlo : 512 ≤ i.val) (hhi : i.val < 544) :
    cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h528 : i.val < 528
  ·
    by_cases h520 : i.val < 520
    ·
      by_cases h516 : i.val < 516
      ·
        by_cases h514 : i.val < 514
        ·
          by_cases h513 : i.val < 513
          ·
            have he : (⟨512, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 512 = i.val
              omega
            simpa only [he] using cofacet0512
          ·
            have he : (⟨513, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 513 = i.val
              omega
            simpa only [he] using cofacet0513
        ·
          by_cases h515 : i.val < 515
          ·
            have he : (⟨514, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 514 = i.val
              omega
            simpa only [he] using cofacet0514
          ·
            have he : (⟨515, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 515 = i.val
              omega
            simpa only [he] using cofacet0515
      ·
        by_cases h518 : i.val < 518
        ·
          by_cases h517 : i.val < 517
          ·
            have he : (⟨516, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 516 = i.val
              omega
            simpa only [he] using cofacet0516
          ·
            have he : (⟨517, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 517 = i.val
              omega
            simpa only [he] using cofacet0517
        ·
          by_cases h519 : i.val < 519
          ·
            have he : (⟨518, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 518 = i.val
              omega
            simpa only [he] using cofacet0518
          ·
            have he : (⟨519, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 519 = i.val
              omega
            simpa only [he] using cofacet0519
    ·
      by_cases h524 : i.val < 524
      ·
        by_cases h522 : i.val < 522
        ·
          by_cases h521 : i.val < 521
          ·
            have he : (⟨520, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 520 = i.val
              omega
            simpa only [he] using cofacet0520
          ·
            have he : (⟨521, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 521 = i.val
              omega
            simpa only [he] using cofacet0521
        ·
          by_cases h523 : i.val < 523
          ·
            have he : (⟨522, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 522 = i.val
              omega
            simpa only [he] using cofacet0522
          ·
            have he : (⟨523, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 523 = i.val
              omega
            simpa only [he] using cofacet0523
      ·
        by_cases h526 : i.val < 526
        ·
          by_cases h525 : i.val < 525
          ·
            have he : (⟨524, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 524 = i.val
              omega
            simpa only [he] using cofacet0524
          ·
            have he : (⟨525, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 525 = i.val
              omega
            simpa only [he] using cofacet0525
        ·
          by_cases h527 : i.val < 527
          ·
            have he : (⟨526, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 526 = i.val
              omega
            simpa only [he] using cofacet0526
          ·
            have he : (⟨527, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 527 = i.val
              omega
            simpa only [he] using cofacet0527
  ·
    by_cases h536 : i.val < 536
    ·
      by_cases h532 : i.val < 532
      ·
        by_cases h530 : i.val < 530
        ·
          by_cases h529 : i.val < 529
          ·
            have he : (⟨528, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 528 = i.val
              omega
            simpa only [he] using cofacet0528
          ·
            have he : (⟨529, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 529 = i.val
              omega
            simpa only [he] using cofacet0529
        ·
          by_cases h531 : i.val < 531
          ·
            have he : (⟨530, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 530 = i.val
              omega
            simpa only [he] using cofacet0530
          ·
            have he : (⟨531, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 531 = i.val
              omega
            simpa only [he] using cofacet0531
      ·
        by_cases h534 : i.val < 534
        ·
          by_cases h533 : i.val < 533
          ·
            have he : (⟨532, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 532 = i.val
              omega
            simpa only [he] using cofacet0532
          ·
            have he : (⟨533, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 533 = i.val
              omega
            simpa only [he] using cofacet0533
        ·
          by_cases h535 : i.val < 535
          ·
            have he : (⟨534, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 534 = i.val
              omega
            simpa only [he] using cofacet0534
          ·
            have he : (⟨535, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 535 = i.val
              omega
            simpa only [he] using cofacet0535
    ·
      by_cases h540 : i.val < 540
      ·
        by_cases h538 : i.val < 538
        ·
          by_cases h537 : i.val < 537
          ·
            have he : (⟨536, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 536 = i.val
              omega
            simpa only [he] using cofacet0536
          ·
            have he : (⟨537, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 537 = i.val
              omega
            simpa only [he] using cofacet0537
        ·
          by_cases h539 : i.val < 539
          ·
            have he : (⟨538, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 538 = i.val
              omega
            simpa only [he] using cofacet0538
          ·
            have he : (⟨539, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 539 = i.val
              omega
            simpa only [he] using cofacet0539
      ·
        by_cases h542 : i.val < 542
        ·
          by_cases h541 : i.val < 541
          ·
            have he : (⟨540, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 540 = i.val
              omega
            simpa only [he] using cofacet0540
          ·
            have he : (⟨541, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 541 = i.val
              omega
            simpa only [he] using cofacet0541
        ·
          by_cases h543 : i.val < 543
          ·
            have he : (⟨542, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 542 = i.val
              omega
            simpa only [he] using cofacet0542
          ·
            have he : (⟨543, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 543 = i.val
              omega
            simpa only [he] using cofacet0543

private theorem cofacetGroup0017 (i : Fin 1069)
    (hlo : 544 ≤ i.val) (hhi : i.val < 576) :
    cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h560 : i.val < 560
  ·
    by_cases h552 : i.val < 552
    ·
      by_cases h548 : i.val < 548
      ·
        by_cases h546 : i.val < 546
        ·
          by_cases h545 : i.val < 545
          ·
            have he : (⟨544, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 544 = i.val
              omega
            simpa only [he] using cofacet0544
          ·
            have he : (⟨545, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 545 = i.val
              omega
            simpa only [he] using cofacet0545
        ·
          by_cases h547 : i.val < 547
          ·
            have he : (⟨546, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 546 = i.val
              omega
            simpa only [he] using cofacet0546
          ·
            have he : (⟨547, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 547 = i.val
              omega
            simpa only [he] using cofacet0547
      ·
        by_cases h550 : i.val < 550
        ·
          by_cases h549 : i.val < 549
          ·
            have he : (⟨548, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 548 = i.val
              omega
            simpa only [he] using cofacet0548
          ·
            have he : (⟨549, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 549 = i.val
              omega
            simpa only [he] using cofacet0549
        ·
          by_cases h551 : i.val < 551
          ·
            have he : (⟨550, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 550 = i.val
              omega
            simpa only [he] using cofacet0550
          ·
            have he : (⟨551, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 551 = i.val
              omega
            simpa only [he] using cofacet0551
    ·
      by_cases h556 : i.val < 556
      ·
        by_cases h554 : i.val < 554
        ·
          by_cases h553 : i.val < 553
          ·
            have he : (⟨552, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 552 = i.val
              omega
            simpa only [he] using cofacet0552
          ·
            have he : (⟨553, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 553 = i.val
              omega
            simpa only [he] using cofacet0553
        ·
          by_cases h555 : i.val < 555
          ·
            have he : (⟨554, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 554 = i.val
              omega
            simpa only [he] using cofacet0554
          ·
            have he : (⟨555, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 555 = i.val
              omega
            simpa only [he] using cofacet0555
      ·
        by_cases h558 : i.val < 558
        ·
          by_cases h557 : i.val < 557
          ·
            have he : (⟨556, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 556 = i.val
              omega
            simpa only [he] using cofacet0556
          ·
            have he : (⟨557, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 557 = i.val
              omega
            simpa only [he] using cofacet0557
        ·
          by_cases h559 : i.val < 559
          ·
            have he : (⟨558, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 558 = i.val
              omega
            simpa only [he] using cofacet0558
          ·
            have he : (⟨559, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 559 = i.val
              omega
            simpa only [he] using cofacet0559
  ·
    by_cases h568 : i.val < 568
    ·
      by_cases h564 : i.val < 564
      ·
        by_cases h562 : i.val < 562
        ·
          by_cases h561 : i.val < 561
          ·
            have he : (⟨560, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 560 = i.val
              omega
            simpa only [he] using cofacet0560
          ·
            have he : (⟨561, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 561 = i.val
              omega
            simpa only [he] using cofacet0561
        ·
          by_cases h563 : i.val < 563
          ·
            have he : (⟨562, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 562 = i.val
              omega
            simpa only [he] using cofacet0562
          ·
            have he : (⟨563, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 563 = i.val
              omega
            simpa only [he] using cofacet0563
      ·
        by_cases h566 : i.val < 566
        ·
          by_cases h565 : i.val < 565
          ·
            have he : (⟨564, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 564 = i.val
              omega
            simpa only [he] using cofacet0564
          ·
            have he : (⟨565, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 565 = i.val
              omega
            simpa only [he] using cofacet0565
        ·
          by_cases h567 : i.val < 567
          ·
            have he : (⟨566, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 566 = i.val
              omega
            simpa only [he] using cofacet0566
          ·
            have he : (⟨567, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 567 = i.val
              omega
            simpa only [he] using cofacet0567
    ·
      by_cases h572 : i.val < 572
      ·
        by_cases h570 : i.val < 570
        ·
          by_cases h569 : i.val < 569
          ·
            have he : (⟨568, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 568 = i.val
              omega
            simpa only [he] using cofacet0568
          ·
            have he : (⟨569, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 569 = i.val
              omega
            simpa only [he] using cofacet0569
        ·
          by_cases h571 : i.val < 571
          ·
            have he : (⟨570, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 570 = i.val
              omega
            simpa only [he] using cofacet0570
          ·
            have he : (⟨571, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 571 = i.val
              omega
            simpa only [he] using cofacet0571
      ·
        by_cases h574 : i.val < 574
        ·
          by_cases h573 : i.val < 573
          ·
            have he : (⟨572, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 572 = i.val
              omega
            simpa only [he] using cofacet0572
          ·
            have he : (⟨573, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 573 = i.val
              omega
            simpa only [he] using cofacet0573
        ·
          by_cases h575 : i.val < 575
          ·
            have he : (⟨574, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 574 = i.val
              omega
            simpa only [he] using cofacet0574
          ·
            have he : (⟨575, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 575 = i.val
              omega
            simpa only [he] using cofacet0575

private theorem cofacetGroup0018 (i : Fin 1069)
    (hlo : 576 ≤ i.val) (hhi : i.val < 608) :
    cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h592 : i.val < 592
  ·
    by_cases h584 : i.val < 584
    ·
      by_cases h580 : i.val < 580
      ·
        by_cases h578 : i.val < 578
        ·
          by_cases h577 : i.val < 577
          ·
            have he : (⟨576, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 576 = i.val
              omega
            simpa only [he] using cofacet0576
          ·
            have he : (⟨577, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 577 = i.val
              omega
            simpa only [he] using cofacet0577
        ·
          by_cases h579 : i.val < 579
          ·
            have he : (⟨578, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 578 = i.val
              omega
            simpa only [he] using cofacet0578
          ·
            have he : (⟨579, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 579 = i.val
              omega
            simpa only [he] using cofacet0579
      ·
        by_cases h582 : i.val < 582
        ·
          by_cases h581 : i.val < 581
          ·
            have he : (⟨580, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 580 = i.val
              omega
            simpa only [he] using cofacet0580
          ·
            have he : (⟨581, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 581 = i.val
              omega
            simpa only [he] using cofacet0581
        ·
          by_cases h583 : i.val < 583
          ·
            have he : (⟨582, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 582 = i.val
              omega
            simpa only [he] using cofacet0582
          ·
            have he : (⟨583, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 583 = i.val
              omega
            simpa only [he] using cofacet0583
    ·
      by_cases h588 : i.val < 588
      ·
        by_cases h586 : i.val < 586
        ·
          by_cases h585 : i.val < 585
          ·
            have he : (⟨584, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 584 = i.val
              omega
            simpa only [he] using cofacet0584
          ·
            have he : (⟨585, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 585 = i.val
              omega
            simpa only [he] using cofacet0585
        ·
          by_cases h587 : i.val < 587
          ·
            have he : (⟨586, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 586 = i.val
              omega
            simpa only [he] using cofacet0586
          ·
            have he : (⟨587, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 587 = i.val
              omega
            simpa only [he] using cofacet0587
      ·
        by_cases h590 : i.val < 590
        ·
          by_cases h589 : i.val < 589
          ·
            have he : (⟨588, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 588 = i.val
              omega
            simpa only [he] using cofacet0588
          ·
            have he : (⟨589, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 589 = i.val
              omega
            simpa only [he] using cofacet0589
        ·
          by_cases h591 : i.val < 591
          ·
            have he : (⟨590, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 590 = i.val
              omega
            simpa only [he] using cofacet0590
          ·
            have he : (⟨591, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 591 = i.val
              omega
            simpa only [he] using cofacet0591
  ·
    by_cases h600 : i.val < 600
    ·
      by_cases h596 : i.val < 596
      ·
        by_cases h594 : i.val < 594
        ·
          by_cases h593 : i.val < 593
          ·
            have he : (⟨592, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 592 = i.val
              omega
            simpa only [he] using cofacet0592
          ·
            have he : (⟨593, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 593 = i.val
              omega
            simpa only [he] using cofacet0593
        ·
          by_cases h595 : i.val < 595
          ·
            have he : (⟨594, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 594 = i.val
              omega
            simpa only [he] using cofacet0594
          ·
            have he : (⟨595, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 595 = i.val
              omega
            simpa only [he] using cofacet0595
      ·
        by_cases h598 : i.val < 598
        ·
          by_cases h597 : i.val < 597
          ·
            have he : (⟨596, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 596 = i.val
              omega
            simpa only [he] using cofacet0596
          ·
            have he : (⟨597, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 597 = i.val
              omega
            simpa only [he] using cofacet0597
        ·
          by_cases h599 : i.val < 599
          ·
            have he : (⟨598, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 598 = i.val
              omega
            simpa only [he] using cofacet0598
          ·
            have he : (⟨599, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 599 = i.val
              omega
            simpa only [he] using cofacet0599
    ·
      by_cases h604 : i.val < 604
      ·
        by_cases h602 : i.val < 602
        ·
          by_cases h601 : i.val < 601
          ·
            have he : (⟨600, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 600 = i.val
              omega
            simpa only [he] using cofacet0600
          ·
            have he : (⟨601, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 601 = i.val
              omega
            simpa only [he] using cofacet0601
        ·
          by_cases h603 : i.val < 603
          ·
            have he : (⟨602, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 602 = i.val
              omega
            simpa only [he] using cofacet0602
          ·
            have he : (⟨603, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 603 = i.val
              omega
            simpa only [he] using cofacet0603
      ·
        by_cases h606 : i.val < 606
        ·
          by_cases h605 : i.val < 605
          ·
            have he : (⟨604, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 604 = i.val
              omega
            simpa only [he] using cofacet0604
          ·
            have he : (⟨605, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 605 = i.val
              omega
            simpa only [he] using cofacet0605
        ·
          by_cases h607 : i.val < 607
          ·
            have he : (⟨606, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 606 = i.val
              omega
            simpa only [he] using cofacet0606
          ·
            have he : (⟨607, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 607 = i.val
              omega
            simpa only [he] using cofacet0607

private theorem cofacetGroup0019 (i : Fin 1069)
    (hlo : 608 ≤ i.val) (hhi : i.val < 640) :
    cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h624 : i.val < 624
  ·
    by_cases h616 : i.val < 616
    ·
      by_cases h612 : i.val < 612
      ·
        by_cases h610 : i.val < 610
        ·
          by_cases h609 : i.val < 609
          ·
            have he : (⟨608, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 608 = i.val
              omega
            simpa only [he] using cofacet0608
          ·
            have he : (⟨609, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 609 = i.val
              omega
            simpa only [he] using cofacet0609
        ·
          by_cases h611 : i.val < 611
          ·
            have he : (⟨610, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 610 = i.val
              omega
            simpa only [he] using cofacet0610
          ·
            have he : (⟨611, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 611 = i.val
              omega
            simpa only [he] using cofacet0611
      ·
        by_cases h614 : i.val < 614
        ·
          by_cases h613 : i.val < 613
          ·
            have he : (⟨612, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 612 = i.val
              omega
            simpa only [he] using cofacet0612
          ·
            have he : (⟨613, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 613 = i.val
              omega
            simpa only [he] using cofacet0613
        ·
          by_cases h615 : i.val < 615
          ·
            have he : (⟨614, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 614 = i.val
              omega
            simpa only [he] using cofacet0614
          ·
            have he : (⟨615, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 615 = i.val
              omega
            simpa only [he] using cofacet0615
    ·
      by_cases h620 : i.val < 620
      ·
        by_cases h618 : i.val < 618
        ·
          by_cases h617 : i.val < 617
          ·
            have he : (⟨616, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 616 = i.val
              omega
            simpa only [he] using cofacet0616
          ·
            have he : (⟨617, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 617 = i.val
              omega
            simpa only [he] using cofacet0617
        ·
          by_cases h619 : i.val < 619
          ·
            have he : (⟨618, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 618 = i.val
              omega
            simpa only [he] using cofacet0618
          ·
            have he : (⟨619, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 619 = i.val
              omega
            simpa only [he] using cofacet0619
      ·
        by_cases h622 : i.val < 622
        ·
          by_cases h621 : i.val < 621
          ·
            have he : (⟨620, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 620 = i.val
              omega
            simpa only [he] using cofacet0620
          ·
            have he : (⟨621, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 621 = i.val
              omega
            simpa only [he] using cofacet0621
        ·
          by_cases h623 : i.val < 623
          ·
            have he : (⟨622, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 622 = i.val
              omega
            simpa only [he] using cofacet0622
          ·
            have he : (⟨623, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 623 = i.val
              omega
            simpa only [he] using cofacet0623
  ·
    by_cases h632 : i.val < 632
    ·
      by_cases h628 : i.val < 628
      ·
        by_cases h626 : i.val < 626
        ·
          by_cases h625 : i.val < 625
          ·
            have he : (⟨624, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 624 = i.val
              omega
            simpa only [he] using cofacet0624
          ·
            have he : (⟨625, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 625 = i.val
              omega
            simpa only [he] using cofacet0625
        ·
          by_cases h627 : i.val < 627
          ·
            have he : (⟨626, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 626 = i.val
              omega
            simpa only [he] using cofacet0626
          ·
            have he : (⟨627, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 627 = i.val
              omega
            simpa only [he] using cofacet0627
      ·
        by_cases h630 : i.val < 630
        ·
          by_cases h629 : i.val < 629
          ·
            have he : (⟨628, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 628 = i.val
              omega
            simpa only [he] using cofacet0628
          ·
            have he : (⟨629, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 629 = i.val
              omega
            simpa only [he] using cofacet0629
        ·
          by_cases h631 : i.val < 631
          ·
            have he : (⟨630, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 630 = i.val
              omega
            simpa only [he] using cofacet0630
          ·
            have he : (⟨631, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 631 = i.val
              omega
            simpa only [he] using cofacet0631
    ·
      by_cases h636 : i.val < 636
      ·
        by_cases h634 : i.val < 634
        ·
          by_cases h633 : i.val < 633
          ·
            have he : (⟨632, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 632 = i.val
              omega
            simpa only [he] using cofacet0632
          ·
            have he : (⟨633, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 633 = i.val
              omega
            simpa only [he] using cofacet0633
        ·
          by_cases h635 : i.val < 635
          ·
            have he : (⟨634, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 634 = i.val
              omega
            simpa only [he] using cofacet0634
          ·
            have he : (⟨635, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 635 = i.val
              omega
            simpa only [he] using cofacet0635
      ·
        by_cases h638 : i.val < 638
        ·
          by_cases h637 : i.val < 637
          ·
            have he : (⟨636, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 636 = i.val
              omega
            simpa only [he] using cofacet0636
          ·
            have he : (⟨637, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 637 = i.val
              omega
            simpa only [he] using cofacet0637
        ·
          by_cases h639 : i.val < 639
          ·
            have he : (⟨638, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 638 = i.val
              omega
            simpa only [he] using cofacet0638
          ·
            have he : (⟨639, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 639 = i.val
              omega
            simpa only [he] using cofacet0639

private theorem cofacetGroup0020 (i : Fin 1069)
    (hlo : 640 ≤ i.val) (hhi : i.val < 672) :
    cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h656 : i.val < 656
  ·
    by_cases h648 : i.val < 648
    ·
      by_cases h644 : i.val < 644
      ·
        by_cases h642 : i.val < 642
        ·
          by_cases h641 : i.val < 641
          ·
            have he : (⟨640, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 640 = i.val
              omega
            simpa only [he] using cofacet0640
          ·
            have he : (⟨641, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 641 = i.val
              omega
            simpa only [he] using cofacet0641
        ·
          by_cases h643 : i.val < 643
          ·
            have he : (⟨642, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 642 = i.val
              omega
            simpa only [he] using cofacet0642
          ·
            have he : (⟨643, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 643 = i.val
              omega
            simpa only [he] using cofacet0643
      ·
        by_cases h646 : i.val < 646
        ·
          by_cases h645 : i.val < 645
          ·
            have he : (⟨644, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 644 = i.val
              omega
            simpa only [he] using cofacet0644
          ·
            have he : (⟨645, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 645 = i.val
              omega
            simpa only [he] using cofacet0645
        ·
          by_cases h647 : i.val < 647
          ·
            have he : (⟨646, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 646 = i.val
              omega
            simpa only [he] using cofacet0646
          ·
            have he : (⟨647, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 647 = i.val
              omega
            simpa only [he] using cofacet0647
    ·
      by_cases h652 : i.val < 652
      ·
        by_cases h650 : i.val < 650
        ·
          by_cases h649 : i.val < 649
          ·
            have he : (⟨648, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 648 = i.val
              omega
            simpa only [he] using cofacet0648
          ·
            have he : (⟨649, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 649 = i.val
              omega
            simpa only [he] using cofacet0649
        ·
          by_cases h651 : i.val < 651
          ·
            have he : (⟨650, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 650 = i.val
              omega
            simpa only [he] using cofacet0650
          ·
            have he : (⟨651, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 651 = i.val
              omega
            simpa only [he] using cofacet0651
      ·
        by_cases h654 : i.val < 654
        ·
          by_cases h653 : i.val < 653
          ·
            have he : (⟨652, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 652 = i.val
              omega
            simpa only [he] using cofacet0652
          ·
            have he : (⟨653, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 653 = i.val
              omega
            simpa only [he] using cofacet0653
        ·
          by_cases h655 : i.val < 655
          ·
            have he : (⟨654, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 654 = i.val
              omega
            simpa only [he] using cofacet0654
          ·
            have he : (⟨655, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 655 = i.val
              omega
            simpa only [he] using cofacet0655
  ·
    by_cases h664 : i.val < 664
    ·
      by_cases h660 : i.val < 660
      ·
        by_cases h658 : i.val < 658
        ·
          by_cases h657 : i.val < 657
          ·
            have he : (⟨656, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 656 = i.val
              omega
            simpa only [he] using cofacet0656
          ·
            have he : (⟨657, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 657 = i.val
              omega
            simpa only [he] using cofacet0657
        ·
          by_cases h659 : i.val < 659
          ·
            have he : (⟨658, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 658 = i.val
              omega
            simpa only [he] using cofacet0658
          ·
            have he : (⟨659, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 659 = i.val
              omega
            simpa only [he] using cofacet0659
      ·
        by_cases h662 : i.val < 662
        ·
          by_cases h661 : i.val < 661
          ·
            have he : (⟨660, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 660 = i.val
              omega
            simpa only [he] using cofacet0660
          ·
            have he : (⟨661, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 661 = i.val
              omega
            simpa only [he] using cofacet0661
        ·
          by_cases h663 : i.val < 663
          ·
            have he : (⟨662, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 662 = i.val
              omega
            simpa only [he] using cofacet0662
          ·
            have he : (⟨663, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 663 = i.val
              omega
            simpa only [he] using cofacet0663
    ·
      by_cases h668 : i.val < 668
      ·
        by_cases h666 : i.val < 666
        ·
          by_cases h665 : i.val < 665
          ·
            have he : (⟨664, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 664 = i.val
              omega
            simpa only [he] using cofacet0664
          ·
            have he : (⟨665, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 665 = i.val
              omega
            simpa only [he] using cofacet0665
        ·
          by_cases h667 : i.val < 667
          ·
            have he : (⟨666, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 666 = i.val
              omega
            simpa only [he] using cofacet0666
          ·
            have he : (⟨667, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 667 = i.val
              omega
            simpa only [he] using cofacet0667
      ·
        by_cases h670 : i.val < 670
        ·
          by_cases h669 : i.val < 669
          ·
            have he : (⟨668, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 668 = i.val
              omega
            simpa only [he] using cofacet0668
          ·
            have he : (⟨669, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 669 = i.val
              omega
            simpa only [he] using cofacet0669
        ·
          by_cases h671 : i.val < 671
          ·
            have he : (⟨670, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 670 = i.val
              omega
            simpa only [he] using cofacet0670
          ·
            have he : (⟨671, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 671 = i.val
              omega
            simpa only [he] using cofacet0671

private theorem cofacetGroup0021 (i : Fin 1069)
    (hlo : 672 ≤ i.val) (hhi : i.val < 704) :
    cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h688 : i.val < 688
  ·
    by_cases h680 : i.val < 680
    ·
      by_cases h676 : i.val < 676
      ·
        by_cases h674 : i.val < 674
        ·
          by_cases h673 : i.val < 673
          ·
            have he : (⟨672, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 672 = i.val
              omega
            simpa only [he] using cofacet0672
          ·
            have he : (⟨673, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 673 = i.val
              omega
            simpa only [he] using cofacet0673
        ·
          by_cases h675 : i.val < 675
          ·
            have he : (⟨674, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 674 = i.val
              omega
            simpa only [he] using cofacet0674
          ·
            have he : (⟨675, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 675 = i.val
              omega
            simpa only [he] using cofacet0675
      ·
        by_cases h678 : i.val < 678
        ·
          by_cases h677 : i.val < 677
          ·
            have he : (⟨676, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 676 = i.val
              omega
            simpa only [he] using cofacet0676
          ·
            have he : (⟨677, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 677 = i.val
              omega
            simpa only [he] using cofacet0677
        ·
          by_cases h679 : i.val < 679
          ·
            have he : (⟨678, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 678 = i.val
              omega
            simpa only [he] using cofacet0678
          ·
            have he : (⟨679, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 679 = i.val
              omega
            simpa only [he] using cofacet0679
    ·
      by_cases h684 : i.val < 684
      ·
        by_cases h682 : i.val < 682
        ·
          by_cases h681 : i.val < 681
          ·
            have he : (⟨680, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 680 = i.val
              omega
            simpa only [he] using cofacet0680
          ·
            have he : (⟨681, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 681 = i.val
              omega
            simpa only [he] using cofacet0681
        ·
          by_cases h683 : i.val < 683
          ·
            have he : (⟨682, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 682 = i.val
              omega
            simpa only [he] using cofacet0682
          ·
            have he : (⟨683, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 683 = i.val
              omega
            simpa only [he] using cofacet0683
      ·
        by_cases h686 : i.val < 686
        ·
          by_cases h685 : i.val < 685
          ·
            have he : (⟨684, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 684 = i.val
              omega
            simpa only [he] using cofacet0684
          ·
            have he : (⟨685, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 685 = i.val
              omega
            simpa only [he] using cofacet0685
        ·
          by_cases h687 : i.val < 687
          ·
            have he : (⟨686, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 686 = i.val
              omega
            simpa only [he] using cofacet0686
          ·
            have he : (⟨687, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 687 = i.val
              omega
            simpa only [he] using cofacet0687
  ·
    by_cases h696 : i.val < 696
    ·
      by_cases h692 : i.val < 692
      ·
        by_cases h690 : i.val < 690
        ·
          by_cases h689 : i.val < 689
          ·
            have he : (⟨688, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 688 = i.val
              omega
            simpa only [he] using cofacet0688
          ·
            have he : (⟨689, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 689 = i.val
              omega
            simpa only [he] using cofacet0689
        ·
          by_cases h691 : i.val < 691
          ·
            have he : (⟨690, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 690 = i.val
              omega
            simpa only [he] using cofacet0690
          ·
            have he : (⟨691, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 691 = i.val
              omega
            simpa only [he] using cofacet0691
      ·
        by_cases h694 : i.val < 694
        ·
          by_cases h693 : i.val < 693
          ·
            have he : (⟨692, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 692 = i.val
              omega
            simpa only [he] using cofacet0692
          ·
            have he : (⟨693, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 693 = i.val
              omega
            simpa only [he] using cofacet0693
        ·
          by_cases h695 : i.val < 695
          ·
            have he : (⟨694, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 694 = i.val
              omega
            simpa only [he] using cofacet0694
          ·
            have he : (⟨695, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 695 = i.val
              omega
            simpa only [he] using cofacet0695
    ·
      by_cases h700 : i.val < 700
      ·
        by_cases h698 : i.val < 698
        ·
          by_cases h697 : i.val < 697
          ·
            have he : (⟨696, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 696 = i.val
              omega
            simpa only [he] using cofacet0696
          ·
            have he : (⟨697, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 697 = i.val
              omega
            simpa only [he] using cofacet0697
        ·
          by_cases h699 : i.val < 699
          ·
            have he : (⟨698, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 698 = i.val
              omega
            simpa only [he] using cofacet0698
          ·
            have he : (⟨699, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 699 = i.val
              omega
            simpa only [he] using cofacet0699
      ·
        by_cases h702 : i.val < 702
        ·
          by_cases h701 : i.val < 701
          ·
            have he : (⟨700, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 700 = i.val
              omega
            simpa only [he] using cofacet0700
          ·
            have he : (⟨701, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 701 = i.val
              omega
            simpa only [he] using cofacet0701
        ·
          by_cases h703 : i.val < 703
          ·
            have he : (⟨702, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 702 = i.val
              omega
            simpa only [he] using cofacet0702
          ·
            have he : (⟨703, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 703 = i.val
              omega
            simpa only [he] using cofacet0703

private theorem cofacetGroup0022 (i : Fin 1069)
    (hlo : 704 ≤ i.val) (hhi : i.val < 736) :
    cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h720 : i.val < 720
  ·
    by_cases h712 : i.val < 712
    ·
      by_cases h708 : i.val < 708
      ·
        by_cases h706 : i.val < 706
        ·
          by_cases h705 : i.val < 705
          ·
            have he : (⟨704, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 704 = i.val
              omega
            simpa only [he] using cofacet0704
          ·
            have he : (⟨705, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 705 = i.val
              omega
            simpa only [he] using cofacet0705
        ·
          by_cases h707 : i.val < 707
          ·
            have he : (⟨706, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 706 = i.val
              omega
            simpa only [he] using cofacet0706
          ·
            have he : (⟨707, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 707 = i.val
              omega
            simpa only [he] using cofacet0707
      ·
        by_cases h710 : i.val < 710
        ·
          by_cases h709 : i.val < 709
          ·
            have he : (⟨708, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 708 = i.val
              omega
            simpa only [he] using cofacet0708
          ·
            have he : (⟨709, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 709 = i.val
              omega
            simpa only [he] using cofacet0709
        ·
          by_cases h711 : i.val < 711
          ·
            have he : (⟨710, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 710 = i.val
              omega
            simpa only [he] using cofacet0710
          ·
            have he : (⟨711, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 711 = i.val
              omega
            simpa only [he] using cofacet0711
    ·
      by_cases h716 : i.val < 716
      ·
        by_cases h714 : i.val < 714
        ·
          by_cases h713 : i.val < 713
          ·
            have he : (⟨712, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 712 = i.val
              omega
            simpa only [he] using cofacet0712
          ·
            have he : (⟨713, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 713 = i.val
              omega
            simpa only [he] using cofacet0713
        ·
          by_cases h715 : i.val < 715
          ·
            have he : (⟨714, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 714 = i.val
              omega
            simpa only [he] using cofacet0714
          ·
            have he : (⟨715, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 715 = i.val
              omega
            simpa only [he] using cofacet0715
      ·
        by_cases h718 : i.val < 718
        ·
          by_cases h717 : i.val < 717
          ·
            have he : (⟨716, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 716 = i.val
              omega
            simpa only [he] using cofacet0716
          ·
            have he : (⟨717, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 717 = i.val
              omega
            simpa only [he] using cofacet0717
        ·
          by_cases h719 : i.val < 719
          ·
            have he : (⟨718, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 718 = i.val
              omega
            simpa only [he] using cofacet0718
          ·
            have he : (⟨719, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 719 = i.val
              omega
            simpa only [he] using cofacet0719
  ·
    by_cases h728 : i.val < 728
    ·
      by_cases h724 : i.val < 724
      ·
        by_cases h722 : i.val < 722
        ·
          by_cases h721 : i.val < 721
          ·
            have he : (⟨720, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 720 = i.val
              omega
            simpa only [he] using cofacet0720
          ·
            have he : (⟨721, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 721 = i.val
              omega
            simpa only [he] using cofacet0721
        ·
          by_cases h723 : i.val < 723
          ·
            have he : (⟨722, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 722 = i.val
              omega
            simpa only [he] using cofacet0722
          ·
            have he : (⟨723, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 723 = i.val
              omega
            simpa only [he] using cofacet0723
      ·
        by_cases h726 : i.val < 726
        ·
          by_cases h725 : i.val < 725
          ·
            have he : (⟨724, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 724 = i.val
              omega
            simpa only [he] using cofacet0724
          ·
            have he : (⟨725, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 725 = i.val
              omega
            simpa only [he] using cofacet0725
        ·
          by_cases h727 : i.val < 727
          ·
            have he : (⟨726, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 726 = i.val
              omega
            simpa only [he] using cofacet0726
          ·
            have he : (⟨727, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 727 = i.val
              omega
            simpa only [he] using cofacet0727
    ·
      by_cases h732 : i.val < 732
      ·
        by_cases h730 : i.val < 730
        ·
          by_cases h729 : i.val < 729
          ·
            have he : (⟨728, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 728 = i.val
              omega
            simpa only [he] using cofacet0728
          ·
            have he : (⟨729, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 729 = i.val
              omega
            simpa only [he] using cofacet0729
        ·
          by_cases h731 : i.val < 731
          ·
            have he : (⟨730, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 730 = i.val
              omega
            simpa only [he] using cofacet0730
          ·
            have he : (⟨731, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 731 = i.val
              omega
            simpa only [he] using cofacet0731
      ·
        by_cases h734 : i.val < 734
        ·
          by_cases h733 : i.val < 733
          ·
            have he : (⟨732, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 732 = i.val
              omega
            simpa only [he] using cofacet0732
          ·
            have he : (⟨733, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 733 = i.val
              omega
            simpa only [he] using cofacet0733
        ·
          by_cases h735 : i.val < 735
          ·
            have he : (⟨734, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 734 = i.val
              omega
            simpa only [he] using cofacet0734
          ·
            have he : (⟨735, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 735 = i.val
              omega
            simpa only [he] using cofacet0735

private theorem cofacetGroup0023 (i : Fin 1069)
    (hlo : 736 ≤ i.val) (hhi : i.val < 768) :
    cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h752 : i.val < 752
  ·
    by_cases h744 : i.val < 744
    ·
      by_cases h740 : i.val < 740
      ·
        by_cases h738 : i.val < 738
        ·
          by_cases h737 : i.val < 737
          ·
            have he : (⟨736, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 736 = i.val
              omega
            simpa only [he] using cofacet0736
          ·
            have he : (⟨737, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 737 = i.val
              omega
            simpa only [he] using cofacet0737
        ·
          by_cases h739 : i.val < 739
          ·
            have he : (⟨738, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 738 = i.val
              omega
            simpa only [he] using cofacet0738
          ·
            have he : (⟨739, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 739 = i.val
              omega
            simpa only [he] using cofacet0739
      ·
        by_cases h742 : i.val < 742
        ·
          by_cases h741 : i.val < 741
          ·
            have he : (⟨740, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 740 = i.val
              omega
            simpa only [he] using cofacet0740
          ·
            have he : (⟨741, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 741 = i.val
              omega
            simpa only [he] using cofacet0741
        ·
          by_cases h743 : i.val < 743
          ·
            have he : (⟨742, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 742 = i.val
              omega
            simpa only [he] using cofacet0742
          ·
            have he : (⟨743, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 743 = i.val
              omega
            simpa only [he] using cofacet0743
    ·
      by_cases h748 : i.val < 748
      ·
        by_cases h746 : i.val < 746
        ·
          by_cases h745 : i.val < 745
          ·
            have he : (⟨744, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 744 = i.val
              omega
            simpa only [he] using cofacet0744
          ·
            have he : (⟨745, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 745 = i.val
              omega
            simpa only [he] using cofacet0745
        ·
          by_cases h747 : i.val < 747
          ·
            have he : (⟨746, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 746 = i.val
              omega
            simpa only [he] using cofacet0746
          ·
            have he : (⟨747, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 747 = i.val
              omega
            simpa only [he] using cofacet0747
      ·
        by_cases h750 : i.val < 750
        ·
          by_cases h749 : i.val < 749
          ·
            have he : (⟨748, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 748 = i.val
              omega
            simpa only [he] using cofacet0748
          ·
            have he : (⟨749, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 749 = i.val
              omega
            simpa only [he] using cofacet0749
        ·
          by_cases h751 : i.val < 751
          ·
            have he : (⟨750, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 750 = i.val
              omega
            simpa only [he] using cofacet0750
          ·
            have he : (⟨751, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 751 = i.val
              omega
            simpa only [he] using cofacet0751
  ·
    by_cases h760 : i.val < 760
    ·
      by_cases h756 : i.val < 756
      ·
        by_cases h754 : i.val < 754
        ·
          by_cases h753 : i.val < 753
          ·
            have he : (⟨752, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 752 = i.val
              omega
            simpa only [he] using cofacet0752
          ·
            have he : (⟨753, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 753 = i.val
              omega
            simpa only [he] using cofacet0753
        ·
          by_cases h755 : i.val < 755
          ·
            have he : (⟨754, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 754 = i.val
              omega
            simpa only [he] using cofacet0754
          ·
            have he : (⟨755, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 755 = i.val
              omega
            simpa only [he] using cofacet0755
      ·
        by_cases h758 : i.val < 758
        ·
          by_cases h757 : i.val < 757
          ·
            have he : (⟨756, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 756 = i.val
              omega
            simpa only [he] using cofacet0756
          ·
            have he : (⟨757, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 757 = i.val
              omega
            simpa only [he] using cofacet0757
        ·
          by_cases h759 : i.val < 759
          ·
            have he : (⟨758, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 758 = i.val
              omega
            simpa only [he] using cofacet0758
          ·
            have he : (⟨759, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 759 = i.val
              omega
            simpa only [he] using cofacet0759
    ·
      by_cases h764 : i.val < 764
      ·
        by_cases h762 : i.val < 762
        ·
          by_cases h761 : i.val < 761
          ·
            have he : (⟨760, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 760 = i.val
              omega
            simpa only [he] using cofacet0760
          ·
            have he : (⟨761, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 761 = i.val
              omega
            simpa only [he] using cofacet0761
        ·
          by_cases h763 : i.val < 763
          ·
            have he : (⟨762, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 762 = i.val
              omega
            simpa only [he] using cofacet0762
          ·
            have he : (⟨763, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 763 = i.val
              omega
            simpa only [he] using cofacet0763
      ·
        by_cases h766 : i.val < 766
        ·
          by_cases h765 : i.val < 765
          ·
            have he : (⟨764, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 764 = i.val
              omega
            simpa only [he] using cofacet0764
          ·
            have he : (⟨765, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 765 = i.val
              omega
            simpa only [he] using cofacet0765
        ·
          by_cases h767 : i.val < 767
          ·
            have he : (⟨766, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 766 = i.val
              omega
            simpa only [he] using cofacet0766
          ·
            have he : (⟨767, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 767 = i.val
              omega
            simpa only [he] using cofacet0767

private theorem cofacetGroup0024 (i : Fin 1069)
    (hlo : 768 ≤ i.val) (hhi : i.val < 800) :
    cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h784 : i.val < 784
  ·
    by_cases h776 : i.val < 776
    ·
      by_cases h772 : i.val < 772
      ·
        by_cases h770 : i.val < 770
        ·
          by_cases h769 : i.val < 769
          ·
            have he : (⟨768, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 768 = i.val
              omega
            simpa only [he] using cofacet0768
          ·
            have he : (⟨769, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 769 = i.val
              omega
            simpa only [he] using cofacet0769
        ·
          by_cases h771 : i.val < 771
          ·
            have he : (⟨770, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 770 = i.val
              omega
            simpa only [he] using cofacet0770
          ·
            have he : (⟨771, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 771 = i.val
              omega
            simpa only [he] using cofacet0771
      ·
        by_cases h774 : i.val < 774
        ·
          by_cases h773 : i.val < 773
          ·
            have he : (⟨772, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 772 = i.val
              omega
            simpa only [he] using cofacet0772
          ·
            have he : (⟨773, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 773 = i.val
              omega
            simpa only [he] using cofacet0773
        ·
          by_cases h775 : i.val < 775
          ·
            have he : (⟨774, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 774 = i.val
              omega
            simpa only [he] using cofacet0774
          ·
            have he : (⟨775, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 775 = i.val
              omega
            simpa only [he] using cofacet0775
    ·
      by_cases h780 : i.val < 780
      ·
        by_cases h778 : i.val < 778
        ·
          by_cases h777 : i.val < 777
          ·
            have he : (⟨776, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 776 = i.val
              omega
            simpa only [he] using cofacet0776
          ·
            have he : (⟨777, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 777 = i.val
              omega
            simpa only [he] using cofacet0777
        ·
          by_cases h779 : i.val < 779
          ·
            have he : (⟨778, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 778 = i.val
              omega
            simpa only [he] using cofacet0778
          ·
            have he : (⟨779, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 779 = i.val
              omega
            simpa only [he] using cofacet0779
      ·
        by_cases h782 : i.val < 782
        ·
          by_cases h781 : i.val < 781
          ·
            have he : (⟨780, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 780 = i.val
              omega
            simpa only [he] using cofacet0780
          ·
            have he : (⟨781, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 781 = i.val
              omega
            simpa only [he] using cofacet0781
        ·
          by_cases h783 : i.val < 783
          ·
            have he : (⟨782, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 782 = i.val
              omega
            simpa only [he] using cofacet0782
          ·
            have he : (⟨783, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 783 = i.val
              omega
            simpa only [he] using cofacet0783
  ·
    by_cases h792 : i.val < 792
    ·
      by_cases h788 : i.val < 788
      ·
        by_cases h786 : i.val < 786
        ·
          by_cases h785 : i.val < 785
          ·
            have he : (⟨784, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 784 = i.val
              omega
            simpa only [he] using cofacet0784
          ·
            have he : (⟨785, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 785 = i.val
              omega
            simpa only [he] using cofacet0785
        ·
          by_cases h787 : i.val < 787
          ·
            have he : (⟨786, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 786 = i.val
              omega
            simpa only [he] using cofacet0786
          ·
            have he : (⟨787, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 787 = i.val
              omega
            simpa only [he] using cofacet0787
      ·
        by_cases h790 : i.val < 790
        ·
          by_cases h789 : i.val < 789
          ·
            have he : (⟨788, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 788 = i.val
              omega
            simpa only [he] using cofacet0788
          ·
            have he : (⟨789, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 789 = i.val
              omega
            simpa only [he] using cofacet0789
        ·
          by_cases h791 : i.val < 791
          ·
            have he : (⟨790, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 790 = i.val
              omega
            simpa only [he] using cofacet0790
          ·
            have he : (⟨791, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 791 = i.val
              omega
            simpa only [he] using cofacet0791
    ·
      by_cases h796 : i.val < 796
      ·
        by_cases h794 : i.val < 794
        ·
          by_cases h793 : i.val < 793
          ·
            have he : (⟨792, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 792 = i.val
              omega
            simpa only [he] using cofacet0792
          ·
            have he : (⟨793, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 793 = i.val
              omega
            simpa only [he] using cofacet0793
        ·
          by_cases h795 : i.val < 795
          ·
            have he : (⟨794, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 794 = i.val
              omega
            simpa only [he] using cofacet0794
          ·
            have he : (⟨795, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 795 = i.val
              omega
            simpa only [he] using cofacet0795
      ·
        by_cases h798 : i.val < 798
        ·
          by_cases h797 : i.val < 797
          ·
            have he : (⟨796, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 796 = i.val
              omega
            simpa only [he] using cofacet0796
          ·
            have he : (⟨797, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 797 = i.val
              omega
            simpa only [he] using cofacet0797
        ·
          by_cases h799 : i.val < 799
          ·
            have he : (⟨798, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 798 = i.val
              omega
            simpa only [he] using cofacet0798
          ·
            have he : (⟨799, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 799 = i.val
              omega
            simpa only [he] using cofacet0799

private theorem cofacetGroup0025 (i : Fin 1069)
    (hlo : 800 ≤ i.val) (hhi : i.val < 832) :
    cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h816 : i.val < 816
  ·
    by_cases h808 : i.val < 808
    ·
      by_cases h804 : i.val < 804
      ·
        by_cases h802 : i.val < 802
        ·
          by_cases h801 : i.val < 801
          ·
            have he : (⟨800, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 800 = i.val
              omega
            simpa only [he] using cofacet0800
          ·
            have he : (⟨801, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 801 = i.val
              omega
            simpa only [he] using cofacet0801
        ·
          by_cases h803 : i.val < 803
          ·
            have he : (⟨802, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 802 = i.val
              omega
            simpa only [he] using cofacet0802
          ·
            have he : (⟨803, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 803 = i.val
              omega
            simpa only [he] using cofacet0803
      ·
        by_cases h806 : i.val < 806
        ·
          by_cases h805 : i.val < 805
          ·
            have he : (⟨804, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 804 = i.val
              omega
            simpa only [he] using cofacet0804
          ·
            have he : (⟨805, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 805 = i.val
              omega
            simpa only [he] using cofacet0805
        ·
          by_cases h807 : i.val < 807
          ·
            have he : (⟨806, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 806 = i.val
              omega
            simpa only [he] using cofacet0806
          ·
            have he : (⟨807, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 807 = i.val
              omega
            simpa only [he] using cofacet0807
    ·
      by_cases h812 : i.val < 812
      ·
        by_cases h810 : i.val < 810
        ·
          by_cases h809 : i.val < 809
          ·
            have he : (⟨808, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 808 = i.val
              omega
            simpa only [he] using cofacet0808
          ·
            have he : (⟨809, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 809 = i.val
              omega
            simpa only [he] using cofacet0809
        ·
          by_cases h811 : i.val < 811
          ·
            have he : (⟨810, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 810 = i.val
              omega
            simpa only [he] using cofacet0810
          ·
            have he : (⟨811, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 811 = i.val
              omega
            simpa only [he] using cofacet0811
      ·
        by_cases h814 : i.val < 814
        ·
          by_cases h813 : i.val < 813
          ·
            have he : (⟨812, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 812 = i.val
              omega
            simpa only [he] using cofacet0812
          ·
            have he : (⟨813, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 813 = i.val
              omega
            simpa only [he] using cofacet0813
        ·
          by_cases h815 : i.val < 815
          ·
            have he : (⟨814, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 814 = i.val
              omega
            simpa only [he] using cofacet0814
          ·
            have he : (⟨815, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 815 = i.val
              omega
            simpa only [he] using cofacet0815
  ·
    by_cases h824 : i.val < 824
    ·
      by_cases h820 : i.val < 820
      ·
        by_cases h818 : i.val < 818
        ·
          by_cases h817 : i.val < 817
          ·
            have he : (⟨816, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 816 = i.val
              omega
            simpa only [he] using cofacet0816
          ·
            have he : (⟨817, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 817 = i.val
              omega
            simpa only [he] using cofacet0817
        ·
          by_cases h819 : i.val < 819
          ·
            have he : (⟨818, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 818 = i.val
              omega
            simpa only [he] using cofacet0818
          ·
            have he : (⟨819, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 819 = i.val
              omega
            simpa only [he] using cofacet0819
      ·
        by_cases h822 : i.val < 822
        ·
          by_cases h821 : i.val < 821
          ·
            have he : (⟨820, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 820 = i.val
              omega
            simpa only [he] using cofacet0820
          ·
            have he : (⟨821, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 821 = i.val
              omega
            simpa only [he] using cofacet0821
        ·
          by_cases h823 : i.val < 823
          ·
            have he : (⟨822, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 822 = i.val
              omega
            simpa only [he] using cofacet0822
          ·
            have he : (⟨823, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 823 = i.val
              omega
            simpa only [he] using cofacet0823
    ·
      by_cases h828 : i.val < 828
      ·
        by_cases h826 : i.val < 826
        ·
          by_cases h825 : i.val < 825
          ·
            have he : (⟨824, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 824 = i.val
              omega
            simpa only [he] using cofacet0824
          ·
            have he : (⟨825, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 825 = i.val
              omega
            simpa only [he] using cofacet0825
        ·
          by_cases h827 : i.val < 827
          ·
            have he : (⟨826, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 826 = i.val
              omega
            simpa only [he] using cofacet0826
          ·
            have he : (⟨827, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 827 = i.val
              omega
            simpa only [he] using cofacet0827
      ·
        by_cases h830 : i.val < 830
        ·
          by_cases h829 : i.val < 829
          ·
            have he : (⟨828, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 828 = i.val
              omega
            simpa only [he] using cofacet0828
          ·
            have he : (⟨829, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 829 = i.val
              omega
            simpa only [he] using cofacet0829
        ·
          by_cases h831 : i.val < 831
          ·
            have he : (⟨830, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 830 = i.val
              omega
            simpa only [he] using cofacet0830
          ·
            have he : (⟨831, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 831 = i.val
              omega
            simpa only [he] using cofacet0831

private theorem cofacetGroup0026 (i : Fin 1069)
    (hlo : 832 ≤ i.val) (hhi : i.val < 864) :
    cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h848 : i.val < 848
  ·
    by_cases h840 : i.val < 840
    ·
      by_cases h836 : i.val < 836
      ·
        by_cases h834 : i.val < 834
        ·
          by_cases h833 : i.val < 833
          ·
            have he : (⟨832, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 832 = i.val
              omega
            simpa only [he] using cofacet0832
          ·
            have he : (⟨833, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 833 = i.val
              omega
            simpa only [he] using cofacet0833
        ·
          by_cases h835 : i.val < 835
          ·
            have he : (⟨834, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 834 = i.val
              omega
            simpa only [he] using cofacet0834
          ·
            have he : (⟨835, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 835 = i.val
              omega
            simpa only [he] using cofacet0835
      ·
        by_cases h838 : i.val < 838
        ·
          by_cases h837 : i.val < 837
          ·
            have he : (⟨836, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 836 = i.val
              omega
            simpa only [he] using cofacet0836
          ·
            have he : (⟨837, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 837 = i.val
              omega
            simpa only [he] using cofacet0837
        ·
          by_cases h839 : i.val < 839
          ·
            have he : (⟨838, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 838 = i.val
              omega
            simpa only [he] using cofacet0838
          ·
            have he : (⟨839, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 839 = i.val
              omega
            simpa only [he] using cofacet0839
    ·
      by_cases h844 : i.val < 844
      ·
        by_cases h842 : i.val < 842
        ·
          by_cases h841 : i.val < 841
          ·
            have he : (⟨840, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 840 = i.val
              omega
            simpa only [he] using cofacet0840
          ·
            have he : (⟨841, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 841 = i.val
              omega
            simpa only [he] using cofacet0841
        ·
          by_cases h843 : i.val < 843
          ·
            have he : (⟨842, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 842 = i.val
              omega
            simpa only [he] using cofacet0842
          ·
            have he : (⟨843, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 843 = i.val
              omega
            simpa only [he] using cofacet0843
      ·
        by_cases h846 : i.val < 846
        ·
          by_cases h845 : i.val < 845
          ·
            have he : (⟨844, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 844 = i.val
              omega
            simpa only [he] using cofacet0844
          ·
            have he : (⟨845, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 845 = i.val
              omega
            simpa only [he] using cofacet0845
        ·
          by_cases h847 : i.val < 847
          ·
            have he : (⟨846, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 846 = i.val
              omega
            simpa only [he] using cofacet0846
          ·
            have he : (⟨847, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 847 = i.val
              omega
            simpa only [he] using cofacet0847
  ·
    by_cases h856 : i.val < 856
    ·
      by_cases h852 : i.val < 852
      ·
        by_cases h850 : i.val < 850
        ·
          by_cases h849 : i.val < 849
          ·
            have he : (⟨848, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 848 = i.val
              omega
            simpa only [he] using cofacet0848
          ·
            have he : (⟨849, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 849 = i.val
              omega
            simpa only [he] using cofacet0849
        ·
          by_cases h851 : i.val < 851
          ·
            have he : (⟨850, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 850 = i.val
              omega
            simpa only [he] using cofacet0850
          ·
            have he : (⟨851, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 851 = i.val
              omega
            simpa only [he] using cofacet0851
      ·
        by_cases h854 : i.val < 854
        ·
          by_cases h853 : i.val < 853
          ·
            have he : (⟨852, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 852 = i.val
              omega
            simpa only [he] using cofacet0852
          ·
            have he : (⟨853, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 853 = i.val
              omega
            simpa only [he] using cofacet0853
        ·
          by_cases h855 : i.val < 855
          ·
            have he : (⟨854, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 854 = i.val
              omega
            simpa only [he] using cofacet0854
          ·
            have he : (⟨855, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 855 = i.val
              omega
            simpa only [he] using cofacet0855
    ·
      by_cases h860 : i.val < 860
      ·
        by_cases h858 : i.val < 858
        ·
          by_cases h857 : i.val < 857
          ·
            have he : (⟨856, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 856 = i.val
              omega
            simpa only [he] using cofacet0856
          ·
            have he : (⟨857, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 857 = i.val
              omega
            simpa only [he] using cofacet0857
        ·
          by_cases h859 : i.val < 859
          ·
            have he : (⟨858, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 858 = i.val
              omega
            simpa only [he] using cofacet0858
          ·
            have he : (⟨859, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 859 = i.val
              omega
            simpa only [he] using cofacet0859
      ·
        by_cases h862 : i.val < 862
        ·
          by_cases h861 : i.val < 861
          ·
            have he : (⟨860, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 860 = i.val
              omega
            simpa only [he] using cofacet0860
          ·
            have he : (⟨861, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 861 = i.val
              omega
            simpa only [he] using cofacet0861
        ·
          by_cases h863 : i.val < 863
          ·
            have he : (⟨862, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 862 = i.val
              omega
            simpa only [he] using cofacet0862
          ·
            have he : (⟨863, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 863 = i.val
              omega
            simpa only [he] using cofacet0863

private theorem cofacetGroup0027 (i : Fin 1069)
    (hlo : 864 ≤ i.val) (hhi : i.val < 896) :
    cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h880 : i.val < 880
  ·
    by_cases h872 : i.val < 872
    ·
      by_cases h868 : i.val < 868
      ·
        by_cases h866 : i.val < 866
        ·
          by_cases h865 : i.val < 865
          ·
            have he : (⟨864, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 864 = i.val
              omega
            simpa only [he] using cofacet0864
          ·
            have he : (⟨865, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 865 = i.val
              omega
            simpa only [he] using cofacet0865
        ·
          by_cases h867 : i.val < 867
          ·
            have he : (⟨866, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 866 = i.val
              omega
            simpa only [he] using cofacet0866
          ·
            have he : (⟨867, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 867 = i.val
              omega
            simpa only [he] using cofacet0867
      ·
        by_cases h870 : i.val < 870
        ·
          by_cases h869 : i.val < 869
          ·
            have he : (⟨868, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 868 = i.val
              omega
            simpa only [he] using cofacet0868
          ·
            have he : (⟨869, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 869 = i.val
              omega
            simpa only [he] using cofacet0869
        ·
          by_cases h871 : i.val < 871
          ·
            have he : (⟨870, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 870 = i.val
              omega
            simpa only [he] using cofacet0870
          ·
            have he : (⟨871, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 871 = i.val
              omega
            simpa only [he] using cofacet0871
    ·
      by_cases h876 : i.val < 876
      ·
        by_cases h874 : i.val < 874
        ·
          by_cases h873 : i.val < 873
          ·
            have he : (⟨872, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 872 = i.val
              omega
            simpa only [he] using cofacet0872
          ·
            have he : (⟨873, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 873 = i.val
              omega
            simpa only [he] using cofacet0873
        ·
          by_cases h875 : i.val < 875
          ·
            have he : (⟨874, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 874 = i.val
              omega
            simpa only [he] using cofacet0874
          ·
            have he : (⟨875, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 875 = i.val
              omega
            simpa only [he] using cofacet0875
      ·
        by_cases h878 : i.val < 878
        ·
          by_cases h877 : i.val < 877
          ·
            have he : (⟨876, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 876 = i.val
              omega
            simpa only [he] using cofacet0876
          ·
            have he : (⟨877, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 877 = i.val
              omega
            simpa only [he] using cofacet0877
        ·
          by_cases h879 : i.val < 879
          ·
            have he : (⟨878, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 878 = i.val
              omega
            simpa only [he] using cofacet0878
          ·
            have he : (⟨879, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 879 = i.val
              omega
            simpa only [he] using cofacet0879
  ·
    by_cases h888 : i.val < 888
    ·
      by_cases h884 : i.val < 884
      ·
        by_cases h882 : i.val < 882
        ·
          by_cases h881 : i.val < 881
          ·
            have he : (⟨880, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 880 = i.val
              omega
            simpa only [he] using cofacet0880
          ·
            have he : (⟨881, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 881 = i.val
              omega
            simpa only [he] using cofacet0881
        ·
          by_cases h883 : i.val < 883
          ·
            have he : (⟨882, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 882 = i.val
              omega
            simpa only [he] using cofacet0882
          ·
            have he : (⟨883, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 883 = i.val
              omega
            simpa only [he] using cofacet0883
      ·
        by_cases h886 : i.val < 886
        ·
          by_cases h885 : i.val < 885
          ·
            have he : (⟨884, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 884 = i.val
              omega
            simpa only [he] using cofacet0884
          ·
            have he : (⟨885, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 885 = i.val
              omega
            simpa only [he] using cofacet0885
        ·
          by_cases h887 : i.val < 887
          ·
            have he : (⟨886, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 886 = i.val
              omega
            simpa only [he] using cofacet0886
          ·
            have he : (⟨887, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 887 = i.val
              omega
            simpa only [he] using cofacet0887
    ·
      by_cases h892 : i.val < 892
      ·
        by_cases h890 : i.val < 890
        ·
          by_cases h889 : i.val < 889
          ·
            have he : (⟨888, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 888 = i.val
              omega
            simpa only [he] using cofacet0888
          ·
            have he : (⟨889, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 889 = i.val
              omega
            simpa only [he] using cofacet0889
        ·
          by_cases h891 : i.val < 891
          ·
            have he : (⟨890, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 890 = i.val
              omega
            simpa only [he] using cofacet0890
          ·
            have he : (⟨891, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 891 = i.val
              omega
            simpa only [he] using cofacet0891
      ·
        by_cases h894 : i.val < 894
        ·
          by_cases h893 : i.val < 893
          ·
            have he : (⟨892, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 892 = i.val
              omega
            simpa only [he] using cofacet0892
          ·
            have he : (⟨893, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 893 = i.val
              omega
            simpa only [he] using cofacet0893
        ·
          by_cases h895 : i.val < 895
          ·
            have he : (⟨894, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 894 = i.val
              omega
            simpa only [he] using cofacet0894
          ·
            have he : (⟨895, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 895 = i.val
              omega
            simpa only [he] using cofacet0895

private theorem cofacetGroup0028 (i : Fin 1069)
    (hlo : 896 ≤ i.val) (hhi : i.val < 928) :
    cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h912 : i.val < 912
  ·
    by_cases h904 : i.val < 904
    ·
      by_cases h900 : i.val < 900
      ·
        by_cases h898 : i.val < 898
        ·
          by_cases h897 : i.val < 897
          ·
            have he : (⟨896, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 896 = i.val
              omega
            simpa only [he] using cofacet0896
          ·
            have he : (⟨897, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 897 = i.val
              omega
            simpa only [he] using cofacet0897
        ·
          by_cases h899 : i.val < 899
          ·
            have he : (⟨898, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 898 = i.val
              omega
            simpa only [he] using cofacet0898
          ·
            have he : (⟨899, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 899 = i.val
              omega
            simpa only [he] using cofacet0899
      ·
        by_cases h902 : i.val < 902
        ·
          by_cases h901 : i.val < 901
          ·
            have he : (⟨900, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 900 = i.val
              omega
            simpa only [he] using cofacet0900
          ·
            have he : (⟨901, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 901 = i.val
              omega
            simpa only [he] using cofacet0901
        ·
          by_cases h903 : i.val < 903
          ·
            have he : (⟨902, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 902 = i.val
              omega
            simpa only [he] using cofacet0902
          ·
            have he : (⟨903, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 903 = i.val
              omega
            simpa only [he] using cofacet0903
    ·
      by_cases h908 : i.val < 908
      ·
        by_cases h906 : i.val < 906
        ·
          by_cases h905 : i.val < 905
          ·
            have he : (⟨904, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 904 = i.val
              omega
            simpa only [he] using cofacet0904
          ·
            have he : (⟨905, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 905 = i.val
              omega
            simpa only [he] using cofacet0905
        ·
          by_cases h907 : i.val < 907
          ·
            have he : (⟨906, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 906 = i.val
              omega
            simpa only [he] using cofacet0906
          ·
            have he : (⟨907, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 907 = i.val
              omega
            simpa only [he] using cofacet0907
      ·
        by_cases h910 : i.val < 910
        ·
          by_cases h909 : i.val < 909
          ·
            have he : (⟨908, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 908 = i.val
              omega
            simpa only [he] using cofacet0908
          ·
            have he : (⟨909, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 909 = i.val
              omega
            simpa only [he] using cofacet0909
        ·
          by_cases h911 : i.val < 911
          ·
            have he : (⟨910, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 910 = i.val
              omega
            simpa only [he] using cofacet0910
          ·
            have he : (⟨911, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 911 = i.val
              omega
            simpa only [he] using cofacet0911
  ·
    by_cases h920 : i.val < 920
    ·
      by_cases h916 : i.val < 916
      ·
        by_cases h914 : i.val < 914
        ·
          by_cases h913 : i.val < 913
          ·
            have he : (⟨912, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 912 = i.val
              omega
            simpa only [he] using cofacet0912
          ·
            have he : (⟨913, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 913 = i.val
              omega
            simpa only [he] using cofacet0913
        ·
          by_cases h915 : i.val < 915
          ·
            have he : (⟨914, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 914 = i.val
              omega
            simpa only [he] using cofacet0914
          ·
            have he : (⟨915, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 915 = i.val
              omega
            simpa only [he] using cofacet0915
      ·
        by_cases h918 : i.val < 918
        ·
          by_cases h917 : i.val < 917
          ·
            have he : (⟨916, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 916 = i.val
              omega
            simpa only [he] using cofacet0916
          ·
            have he : (⟨917, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 917 = i.val
              omega
            simpa only [he] using cofacet0917
        ·
          by_cases h919 : i.val < 919
          ·
            have he : (⟨918, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 918 = i.val
              omega
            simpa only [he] using cofacet0918
          ·
            have he : (⟨919, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 919 = i.val
              omega
            simpa only [he] using cofacet0919
    ·
      by_cases h924 : i.val < 924
      ·
        by_cases h922 : i.val < 922
        ·
          by_cases h921 : i.val < 921
          ·
            have he : (⟨920, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 920 = i.val
              omega
            simpa only [he] using cofacet0920
          ·
            have he : (⟨921, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 921 = i.val
              omega
            simpa only [he] using cofacet0921
        ·
          by_cases h923 : i.val < 923
          ·
            have he : (⟨922, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 922 = i.val
              omega
            simpa only [he] using cofacet0922
          ·
            have he : (⟨923, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 923 = i.val
              omega
            simpa only [he] using cofacet0923
      ·
        by_cases h926 : i.val < 926
        ·
          by_cases h925 : i.val < 925
          ·
            have he : (⟨924, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 924 = i.val
              omega
            simpa only [he] using cofacet0924
          ·
            have he : (⟨925, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 925 = i.val
              omega
            simpa only [he] using cofacet0925
        ·
          by_cases h927 : i.val < 927
          ·
            have he : (⟨926, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 926 = i.val
              omega
            simpa only [he] using cofacet0926
          ·
            have he : (⟨927, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 927 = i.val
              omega
            simpa only [he] using cofacet0927

private theorem cofacetGroup0029 (i : Fin 1069)
    (hlo : 928 ≤ i.val) (hhi : i.val < 960) :
    cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h944 : i.val < 944
  ·
    by_cases h936 : i.val < 936
    ·
      by_cases h932 : i.val < 932
      ·
        by_cases h930 : i.val < 930
        ·
          by_cases h929 : i.val < 929
          ·
            have he : (⟨928, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 928 = i.val
              omega
            simpa only [he] using cofacet0928
          ·
            have he : (⟨929, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 929 = i.val
              omega
            simpa only [he] using cofacet0929
        ·
          by_cases h931 : i.val < 931
          ·
            have he : (⟨930, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 930 = i.val
              omega
            simpa only [he] using cofacet0930
          ·
            have he : (⟨931, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 931 = i.val
              omega
            simpa only [he] using cofacet0931
      ·
        by_cases h934 : i.val < 934
        ·
          by_cases h933 : i.val < 933
          ·
            have he : (⟨932, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 932 = i.val
              omega
            simpa only [he] using cofacet0932
          ·
            have he : (⟨933, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 933 = i.val
              omega
            simpa only [he] using cofacet0933
        ·
          by_cases h935 : i.val < 935
          ·
            have he : (⟨934, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 934 = i.val
              omega
            simpa only [he] using cofacet0934
          ·
            have he : (⟨935, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 935 = i.val
              omega
            simpa only [he] using cofacet0935
    ·
      by_cases h940 : i.val < 940
      ·
        by_cases h938 : i.val < 938
        ·
          by_cases h937 : i.val < 937
          ·
            have he : (⟨936, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 936 = i.val
              omega
            simpa only [he] using cofacet0936
          ·
            have he : (⟨937, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 937 = i.val
              omega
            simpa only [he] using cofacet0937
        ·
          by_cases h939 : i.val < 939
          ·
            have he : (⟨938, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 938 = i.val
              omega
            simpa only [he] using cofacet0938
          ·
            have he : (⟨939, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 939 = i.val
              omega
            simpa only [he] using cofacet0939
      ·
        by_cases h942 : i.val < 942
        ·
          by_cases h941 : i.val < 941
          ·
            have he : (⟨940, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 940 = i.val
              omega
            simpa only [he] using cofacet0940
          ·
            have he : (⟨941, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 941 = i.val
              omega
            simpa only [he] using cofacet0941
        ·
          by_cases h943 : i.val < 943
          ·
            have he : (⟨942, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 942 = i.val
              omega
            simpa only [he] using cofacet0942
          ·
            have he : (⟨943, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 943 = i.val
              omega
            simpa only [he] using cofacet0943
  ·
    by_cases h952 : i.val < 952
    ·
      by_cases h948 : i.val < 948
      ·
        by_cases h946 : i.val < 946
        ·
          by_cases h945 : i.val < 945
          ·
            have he : (⟨944, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 944 = i.val
              omega
            simpa only [he] using cofacet0944
          ·
            have he : (⟨945, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 945 = i.val
              omega
            simpa only [he] using cofacet0945
        ·
          by_cases h947 : i.val < 947
          ·
            have he : (⟨946, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 946 = i.val
              omega
            simpa only [he] using cofacet0946
          ·
            have he : (⟨947, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 947 = i.val
              omega
            simpa only [he] using cofacet0947
      ·
        by_cases h950 : i.val < 950
        ·
          by_cases h949 : i.val < 949
          ·
            have he : (⟨948, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 948 = i.val
              omega
            simpa only [he] using cofacet0948
          ·
            have he : (⟨949, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 949 = i.val
              omega
            simpa only [he] using cofacet0949
        ·
          by_cases h951 : i.val < 951
          ·
            have he : (⟨950, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 950 = i.val
              omega
            simpa only [he] using cofacet0950
          ·
            have he : (⟨951, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 951 = i.val
              omega
            simpa only [he] using cofacet0951
    ·
      by_cases h956 : i.val < 956
      ·
        by_cases h954 : i.val < 954
        ·
          by_cases h953 : i.val < 953
          ·
            have he : (⟨952, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 952 = i.val
              omega
            simpa only [he] using cofacet0952
          ·
            have he : (⟨953, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 953 = i.val
              omega
            simpa only [he] using cofacet0953
        ·
          by_cases h955 : i.val < 955
          ·
            have he : (⟨954, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 954 = i.val
              omega
            simpa only [he] using cofacet0954
          ·
            have he : (⟨955, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 955 = i.val
              omega
            simpa only [he] using cofacet0955
      ·
        by_cases h958 : i.val < 958
        ·
          by_cases h957 : i.val < 957
          ·
            have he : (⟨956, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 956 = i.val
              omega
            simpa only [he] using cofacet0956
          ·
            have he : (⟨957, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 957 = i.val
              omega
            simpa only [he] using cofacet0957
        ·
          by_cases h959 : i.val < 959
          ·
            have he : (⟨958, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 958 = i.val
              omega
            simpa only [he] using cofacet0958
          ·
            have he : (⟨959, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 959 = i.val
              omega
            simpa only [he] using cofacet0959

private theorem cofacetGroup0030 (i : Fin 1069)
    (hlo : 960 ≤ i.val) (hhi : i.val < 992) :
    cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h976 : i.val < 976
  ·
    by_cases h968 : i.val < 968
    ·
      by_cases h964 : i.val < 964
      ·
        by_cases h962 : i.val < 962
        ·
          by_cases h961 : i.val < 961
          ·
            have he : (⟨960, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 960 = i.val
              omega
            simpa only [he] using cofacet0960
          ·
            have he : (⟨961, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 961 = i.val
              omega
            simpa only [he] using cofacet0961
        ·
          by_cases h963 : i.val < 963
          ·
            have he : (⟨962, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 962 = i.val
              omega
            simpa only [he] using cofacet0962
          ·
            have he : (⟨963, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 963 = i.val
              omega
            simpa only [he] using cofacet0963
      ·
        by_cases h966 : i.val < 966
        ·
          by_cases h965 : i.val < 965
          ·
            have he : (⟨964, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 964 = i.val
              omega
            simpa only [he] using cofacet0964
          ·
            have he : (⟨965, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 965 = i.val
              omega
            simpa only [he] using cofacet0965
        ·
          by_cases h967 : i.val < 967
          ·
            have he : (⟨966, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 966 = i.val
              omega
            simpa only [he] using cofacet0966
          ·
            have he : (⟨967, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 967 = i.val
              omega
            simpa only [he] using cofacet0967
    ·
      by_cases h972 : i.val < 972
      ·
        by_cases h970 : i.val < 970
        ·
          by_cases h969 : i.val < 969
          ·
            have he : (⟨968, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 968 = i.val
              omega
            simpa only [he] using cofacet0968
          ·
            have he : (⟨969, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 969 = i.val
              omega
            simpa only [he] using cofacet0969
        ·
          by_cases h971 : i.val < 971
          ·
            have he : (⟨970, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 970 = i.val
              omega
            simpa only [he] using cofacet0970
          ·
            have he : (⟨971, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 971 = i.val
              omega
            simpa only [he] using cofacet0971
      ·
        by_cases h974 : i.val < 974
        ·
          by_cases h973 : i.val < 973
          ·
            have he : (⟨972, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 972 = i.val
              omega
            simpa only [he] using cofacet0972
          ·
            have he : (⟨973, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 973 = i.val
              omega
            simpa only [he] using cofacet0973
        ·
          by_cases h975 : i.val < 975
          ·
            have he : (⟨974, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 974 = i.val
              omega
            simpa only [he] using cofacet0974
          ·
            have he : (⟨975, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 975 = i.val
              omega
            simpa only [he] using cofacet0975
  ·
    by_cases h984 : i.val < 984
    ·
      by_cases h980 : i.val < 980
      ·
        by_cases h978 : i.val < 978
        ·
          by_cases h977 : i.val < 977
          ·
            have he : (⟨976, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 976 = i.val
              omega
            simpa only [he] using cofacet0976
          ·
            have he : (⟨977, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 977 = i.val
              omega
            simpa only [he] using cofacet0977
        ·
          by_cases h979 : i.val < 979
          ·
            have he : (⟨978, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 978 = i.val
              omega
            simpa only [he] using cofacet0978
          ·
            have he : (⟨979, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 979 = i.val
              omega
            simpa only [he] using cofacet0979
      ·
        by_cases h982 : i.val < 982
        ·
          by_cases h981 : i.val < 981
          ·
            have he : (⟨980, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 980 = i.val
              omega
            simpa only [he] using cofacet0980
          ·
            have he : (⟨981, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 981 = i.val
              omega
            simpa only [he] using cofacet0981
        ·
          by_cases h983 : i.val < 983
          ·
            have he : (⟨982, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 982 = i.val
              omega
            simpa only [he] using cofacet0982
          ·
            have he : (⟨983, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 983 = i.val
              omega
            simpa only [he] using cofacet0983
    ·
      by_cases h988 : i.val < 988
      ·
        by_cases h986 : i.val < 986
        ·
          by_cases h985 : i.val < 985
          ·
            have he : (⟨984, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 984 = i.val
              omega
            simpa only [he] using cofacet0984
          ·
            have he : (⟨985, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 985 = i.val
              omega
            simpa only [he] using cofacet0985
        ·
          by_cases h987 : i.val < 987
          ·
            have he : (⟨986, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 986 = i.val
              omega
            simpa only [he] using cofacet0986
          ·
            have he : (⟨987, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 987 = i.val
              omega
            simpa only [he] using cofacet0987
      ·
        by_cases h990 : i.val < 990
        ·
          by_cases h989 : i.val < 989
          ·
            have he : (⟨988, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 988 = i.val
              omega
            simpa only [he] using cofacet0988
          ·
            have he : (⟨989, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 989 = i.val
              omega
            simpa only [he] using cofacet0989
        ·
          by_cases h991 : i.val < 991
          ·
            have he : (⟨990, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 990 = i.val
              omega
            simpa only [he] using cofacet0990
          ·
            have he : (⟨991, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 991 = i.val
              omega
            simpa only [he] using cofacet0991

private theorem cofacetGroup0031 (i : Fin 1069)
    (hlo : 992 ≤ i.val) (hhi : i.val < 1024) :
    cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h1008 : i.val < 1008
  ·
    by_cases h1000 : i.val < 1000
    ·
      by_cases h996 : i.val < 996
      ·
        by_cases h994 : i.val < 994
        ·
          by_cases h993 : i.val < 993
          ·
            have he : (⟨992, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 992 = i.val
              omega
            simpa only [he] using cofacet0992
          ·
            have he : (⟨993, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 993 = i.val
              omega
            simpa only [he] using cofacet0993
        ·
          by_cases h995 : i.val < 995
          ·
            have he : (⟨994, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 994 = i.val
              omega
            simpa only [he] using cofacet0994
          ·
            have he : (⟨995, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 995 = i.val
              omega
            simpa only [he] using cofacet0995
      ·
        by_cases h998 : i.val < 998
        ·
          by_cases h997 : i.val < 997
          ·
            have he : (⟨996, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 996 = i.val
              omega
            simpa only [he] using cofacet0996
          ·
            have he : (⟨997, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 997 = i.val
              omega
            simpa only [he] using cofacet0997
        ·
          by_cases h999 : i.val < 999
          ·
            have he : (⟨998, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 998 = i.val
              omega
            simpa only [he] using cofacet0998
          ·
            have he : (⟨999, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 999 = i.val
              omega
            simpa only [he] using cofacet0999
    ·
      by_cases h1004 : i.val < 1004
      ·
        by_cases h1002 : i.val < 1002
        ·
          by_cases h1001 : i.val < 1001
          ·
            have he : (⟨1000, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1000 = i.val
              omega
            simpa only [he] using cofacet1000
          ·
            have he : (⟨1001, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1001 = i.val
              omega
            simpa only [he] using cofacet1001
        ·
          by_cases h1003 : i.val < 1003
          ·
            have he : (⟨1002, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1002 = i.val
              omega
            simpa only [he] using cofacet1002
          ·
            have he : (⟨1003, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1003 = i.val
              omega
            simpa only [he] using cofacet1003
      ·
        by_cases h1006 : i.val < 1006
        ·
          by_cases h1005 : i.val < 1005
          ·
            have he : (⟨1004, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1004 = i.val
              omega
            simpa only [he] using cofacet1004
          ·
            have he : (⟨1005, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1005 = i.val
              omega
            simpa only [he] using cofacet1005
        ·
          by_cases h1007 : i.val < 1007
          ·
            have he : (⟨1006, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1006 = i.val
              omega
            simpa only [he] using cofacet1006
          ·
            have he : (⟨1007, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1007 = i.val
              omega
            simpa only [he] using cofacet1007
  ·
    by_cases h1016 : i.val < 1016
    ·
      by_cases h1012 : i.val < 1012
      ·
        by_cases h1010 : i.val < 1010
        ·
          by_cases h1009 : i.val < 1009
          ·
            have he : (⟨1008, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1008 = i.val
              omega
            simpa only [he] using cofacet1008
          ·
            have he : (⟨1009, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1009 = i.val
              omega
            simpa only [he] using cofacet1009
        ·
          by_cases h1011 : i.val < 1011
          ·
            have he : (⟨1010, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1010 = i.val
              omega
            simpa only [he] using cofacet1010
          ·
            have he : (⟨1011, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1011 = i.val
              omega
            simpa only [he] using cofacet1011
      ·
        by_cases h1014 : i.val < 1014
        ·
          by_cases h1013 : i.val < 1013
          ·
            have he : (⟨1012, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1012 = i.val
              omega
            simpa only [he] using cofacet1012
          ·
            have he : (⟨1013, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1013 = i.val
              omega
            simpa only [he] using cofacet1013
        ·
          by_cases h1015 : i.val < 1015
          ·
            have he : (⟨1014, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1014 = i.val
              omega
            simpa only [he] using cofacet1014
          ·
            have he : (⟨1015, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1015 = i.val
              omega
            simpa only [he] using cofacet1015
    ·
      by_cases h1020 : i.val < 1020
      ·
        by_cases h1018 : i.val < 1018
        ·
          by_cases h1017 : i.val < 1017
          ·
            have he : (⟨1016, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1016 = i.val
              omega
            simpa only [he] using cofacet1016
          ·
            have he : (⟨1017, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1017 = i.val
              omega
            simpa only [he] using cofacet1017
        ·
          by_cases h1019 : i.val < 1019
          ·
            have he : (⟨1018, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1018 = i.val
              omega
            simpa only [he] using cofacet1018
          ·
            have he : (⟨1019, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1019 = i.val
              omega
            simpa only [he] using cofacet1019
      ·
        by_cases h1022 : i.val < 1022
        ·
          by_cases h1021 : i.val < 1021
          ·
            have he : (⟨1020, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1020 = i.val
              omega
            simpa only [he] using cofacet1020
          ·
            have he : (⟨1021, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1021 = i.val
              omega
            simpa only [he] using cofacet1021
        ·
          by_cases h1023 : i.val < 1023
          ·
            have he : (⟨1022, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1022 = i.val
              omega
            simpa only [he] using cofacet1022
          ·
            have he : (⟨1023, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1023 = i.val
              omega
            simpa only [he] using cofacet1023

private theorem cofacetGroup0032 (i : Fin 1069)
    (hlo : 1024 ≤ i.val) (hhi : i.val < 1056) :
    cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h1040 : i.val < 1040
  ·
    by_cases h1032 : i.val < 1032
    ·
      by_cases h1028 : i.val < 1028
      ·
        by_cases h1026 : i.val < 1026
        ·
          by_cases h1025 : i.val < 1025
          ·
            have he : (⟨1024, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1024 = i.val
              omega
            simpa only [he] using cofacet1024
          ·
            have he : (⟨1025, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1025 = i.val
              omega
            simpa only [he] using cofacet1025
        ·
          by_cases h1027 : i.val < 1027
          ·
            have he : (⟨1026, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1026 = i.val
              omega
            simpa only [he] using cofacet1026
          ·
            have he : (⟨1027, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1027 = i.val
              omega
            simpa only [he] using cofacet1027
      ·
        by_cases h1030 : i.val < 1030
        ·
          by_cases h1029 : i.val < 1029
          ·
            have he : (⟨1028, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1028 = i.val
              omega
            simpa only [he] using cofacet1028
          ·
            have he : (⟨1029, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1029 = i.val
              omega
            simpa only [he] using cofacet1029
        ·
          by_cases h1031 : i.val < 1031
          ·
            have he : (⟨1030, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1030 = i.val
              omega
            simpa only [he] using cofacet1030
          ·
            have he : (⟨1031, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1031 = i.val
              omega
            simpa only [he] using cofacet1031
    ·
      by_cases h1036 : i.val < 1036
      ·
        by_cases h1034 : i.val < 1034
        ·
          by_cases h1033 : i.val < 1033
          ·
            have he : (⟨1032, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1032 = i.val
              omega
            simpa only [he] using cofacet1032
          ·
            have he : (⟨1033, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1033 = i.val
              omega
            simpa only [he] using cofacet1033
        ·
          by_cases h1035 : i.val < 1035
          ·
            have he : (⟨1034, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1034 = i.val
              omega
            simpa only [he] using cofacet1034
          ·
            have he : (⟨1035, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1035 = i.val
              omega
            simpa only [he] using cofacet1035
      ·
        by_cases h1038 : i.val < 1038
        ·
          by_cases h1037 : i.val < 1037
          ·
            have he : (⟨1036, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1036 = i.val
              omega
            simpa only [he] using cofacet1036
          ·
            have he : (⟨1037, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1037 = i.val
              omega
            simpa only [he] using cofacet1037
        ·
          by_cases h1039 : i.val < 1039
          ·
            have he : (⟨1038, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1038 = i.val
              omega
            simpa only [he] using cofacet1038
          ·
            have he : (⟨1039, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1039 = i.val
              omega
            simpa only [he] using cofacet1039
  ·
    by_cases h1048 : i.val < 1048
    ·
      by_cases h1044 : i.val < 1044
      ·
        by_cases h1042 : i.val < 1042
        ·
          by_cases h1041 : i.val < 1041
          ·
            have he : (⟨1040, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1040 = i.val
              omega
            simpa only [he] using cofacet1040
          ·
            have he : (⟨1041, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1041 = i.val
              omega
            simpa only [he] using cofacet1041
        ·
          by_cases h1043 : i.val < 1043
          ·
            have he : (⟨1042, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1042 = i.val
              omega
            simpa only [he] using cofacet1042
          ·
            have he : (⟨1043, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1043 = i.val
              omega
            simpa only [he] using cofacet1043
      ·
        by_cases h1046 : i.val < 1046
        ·
          by_cases h1045 : i.val < 1045
          ·
            have he : (⟨1044, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1044 = i.val
              omega
            simpa only [he] using cofacet1044
          ·
            have he : (⟨1045, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1045 = i.val
              omega
            simpa only [he] using cofacet1045
        ·
          by_cases h1047 : i.val < 1047
          ·
            have he : (⟨1046, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1046 = i.val
              omega
            simpa only [he] using cofacet1046
          ·
            have he : (⟨1047, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1047 = i.val
              omega
            simpa only [he] using cofacet1047
    ·
      by_cases h1052 : i.val < 1052
      ·
        by_cases h1050 : i.val < 1050
        ·
          by_cases h1049 : i.val < 1049
          ·
            have he : (⟨1048, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1048 = i.val
              omega
            simpa only [he] using cofacet1048
          ·
            have he : (⟨1049, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1049 = i.val
              omega
            simpa only [he] using cofacet1049
        ·
          by_cases h1051 : i.val < 1051
          ·
            have he : (⟨1050, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1050 = i.val
              omega
            simpa only [he] using cofacet1050
          ·
            have he : (⟨1051, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1051 = i.val
              omega
            simpa only [he] using cofacet1051
      ·
        by_cases h1054 : i.val < 1054
        ·
          by_cases h1053 : i.val < 1053
          ·
            have he : (⟨1052, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1052 = i.val
              omega
            simpa only [he] using cofacet1052
          ·
            have he : (⟨1053, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1053 = i.val
              omega
            simpa only [he] using cofacet1053
        ·
          by_cases h1055 : i.val < 1055
          ·
            have he : (⟨1054, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1054 = i.val
              omega
            simpa only [he] using cofacet1054
          ·
            have he : (⟨1055, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1055 = i.val
              omega
            simpa only [he] using cofacet1055

private theorem cofacetGroup0033 (i : Fin 1069)
    (hlo : 1056 ≤ i.val) (hhi : i.val < 1069) :
    cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h1062 : i.val < 1062
  ·
    by_cases h1059 : i.val < 1059
    ·
      by_cases h1057 : i.val < 1057
      ·
        have he : (⟨1056, by decide⟩ : Fin 1069) = i := by
          apply Fin.ext
          change 1056 = i.val
          omega
        simpa only [he] using cofacet1056
      ·
        by_cases h1058 : i.val < 1058
        ·
          have he : (⟨1057, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1057 = i.val
            omega
          simpa only [he] using cofacet1057
        ·
          have he : (⟨1058, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1058 = i.val
            omega
          simpa only [he] using cofacet1058
    ·
      by_cases h1060 : i.val < 1060
      ·
        have he : (⟨1059, by decide⟩ : Fin 1069) = i := by
          apply Fin.ext
          change 1059 = i.val
          omega
        simpa only [he] using cofacet1059
      ·
        by_cases h1061 : i.val < 1061
        ·
          have he : (⟨1060, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1060 = i.val
            omega
          simpa only [he] using cofacet1060
        ·
          have he : (⟨1061, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1061 = i.val
            omega
          simpa only [he] using cofacet1061
  ·
    by_cases h1065 : i.val < 1065
    ·
      by_cases h1063 : i.val < 1063
      ·
        have he : (⟨1062, by decide⟩ : Fin 1069) = i := by
          apply Fin.ext
          change 1062 = i.val
          omega
        simpa only [he] using cofacet1062
      ·
        by_cases h1064 : i.val < 1064
        ·
          have he : (⟨1063, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1063 = i.val
            omega
          simpa only [he] using cofacet1063
        ·
          have he : (⟨1064, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1064 = i.val
            omega
          simpa only [he] using cofacet1064
    ·
      by_cases h1067 : i.val < 1067
      ·
        by_cases h1066 : i.val < 1066
        ·
          have he : (⟨1065, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1065 = i.val
            omega
          simpa only [he] using cofacet1065
        ·
          have he : (⟨1066, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1066 = i.val
            omega
          simpa only [he] using cofacet1066
      ·
        by_cases h1068 : i.val < 1068
        ·
          have he : (⟨1067, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1067 = i.val
            omega
          simpa only [he] using cofacet1067
        ·
          have he : (⟨1068, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1068 = i.val
            omega
          simpa only [he] using cofacet1068

private theorem cubeCofacetCertificate_all : ∀ i : Fin 1069,
    cubeCofacetCertificate i := by
  intro i
  have hi_bound := i.isLt
  by_cases h544 : i.val < 544
  ·
    by_cases h256 : i.val < 256
    ·
      by_cases h128 : i.val < 128
      ·
        by_cases h64 : i.val < 64
        ·
          by_cases h32 : i.val < 32
          ·
            exact cofacetGroup0000 i (by omega) (by omega)
          ·
            exact cofacetGroup0001 i (by omega) (by omega)
        ·
          by_cases h96 : i.val < 96
          ·
            exact cofacetGroup0002 i (by omega) (by omega)
          ·
            exact cofacetGroup0003 i (by omega) (by omega)
      ·
        by_cases h192 : i.val < 192
        ·
          by_cases h160 : i.val < 160
          ·
            exact cofacetGroup0004 i (by omega) (by omega)
          ·
            exact cofacetGroup0005 i (by omega) (by omega)
        ·
          by_cases h224 : i.val < 224
          ·
            exact cofacetGroup0006 i (by omega) (by omega)
          ·
            exact cofacetGroup0007 i (by omega) (by omega)
    ·
      by_cases h384 : i.val < 384
      ·
        by_cases h320 : i.val < 320
        ·
          by_cases h288 : i.val < 288
          ·
            exact cofacetGroup0008 i (by omega) (by omega)
          ·
            exact cofacetGroup0009 i (by omega) (by omega)
        ·
          by_cases h352 : i.val < 352
          ·
            exact cofacetGroup0010 i (by omega) (by omega)
          ·
            exact cofacetGroup0011 i (by omega) (by omega)
      ·
        by_cases h448 : i.val < 448
        ·
          by_cases h416 : i.val < 416
          ·
            exact cofacetGroup0012 i (by omega) (by omega)
          ·
            exact cofacetGroup0013 i (by omega) (by omega)
        ·
          by_cases h480 : i.val < 480
          ·
            exact cofacetGroup0014 i (by omega) (by omega)
          ·
            by_cases h512 : i.val < 512
            ·
              exact cofacetGroup0015 i (by omega) (by omega)
            ·
              exact cofacetGroup0016 i (by omega) (by omega)
  ·
    by_cases h800 : i.val < 800
    ·
      by_cases h672 : i.val < 672
      ·
        by_cases h608 : i.val < 608
        ·
          by_cases h576 : i.val < 576
          ·
            exact cofacetGroup0017 i (by omega) (by omega)
          ·
            exact cofacetGroup0018 i (by omega) (by omega)
        ·
          by_cases h640 : i.val < 640
          ·
            exact cofacetGroup0019 i (by omega) (by omega)
          ·
            exact cofacetGroup0020 i (by omega) (by omega)
      ·
        by_cases h736 : i.val < 736
        ·
          by_cases h704 : i.val < 704
          ·
            exact cofacetGroup0021 i (by omega) (by omega)
          ·
            exact cofacetGroup0022 i (by omega) (by omega)
        ·
          by_cases h768 : i.val < 768
          ·
            exact cofacetGroup0023 i (by omega) (by omega)
          ·
            exact cofacetGroup0024 i (by omega) (by omega)
    ·
      by_cases h928 : i.val < 928
      ·
        by_cases h864 : i.val < 864
        ·
          by_cases h832 : i.val < 832
          ·
            exact cofacetGroup0025 i (by omega) (by omega)
          ·
            exact cofacetGroup0026 i (by omega) (by omega)
        ·
          by_cases h896 : i.val < 896
          ·
            exact cofacetGroup0027 i (by omega) (by omega)
          ·
            exact cofacetGroup0028 i (by omega) (by omega)
      ·
        by_cases h992 : i.val < 992
        ·
          by_cases h960 : i.val < 960
          ·
            exact cofacetGroup0029 i (by omega) (by omega)
          ·
            exact cofacetGroup0030 i (by omega) (by omega)
        ·
          by_cases h1024 : i.val < 1024
          ·
            exact cofacetGroup0031 i (by omega) (by omega)
          ·
            by_cases h1056 : i.val < 1056
            ·
              exact cofacetGroup0032 i (by omega) (by omega)
            ·
              exact cofacetGroup0033 i (by omega) (by omega)

/-- All catalogue faces contained in a facet occur among that facet's
27 nonempty standard cube-face codes. No geometric condition is assumed. -/
theorem codeFace_complete : ∀ (f : Fin 130) (i : Fin 1069),
    faceMask i ⊆ facetLabels f → ∃ c : Fin 27, codeFace f c = i := by
  intro f i h
  apply Exists.intro (cubeCofacetCode i f)
  exact cubeCofacetCertificate_all i f ((cubeCofacets_iff i f).mpr h)

end CubicalIndecomposability
