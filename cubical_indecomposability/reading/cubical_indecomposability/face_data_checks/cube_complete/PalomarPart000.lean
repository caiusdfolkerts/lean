module

public import cubical_indecomposability.face_data_checks.anchors
public import Lean.Elab.Tactic.Omega

@[expose] public section

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

end CubicalIndecomposability
