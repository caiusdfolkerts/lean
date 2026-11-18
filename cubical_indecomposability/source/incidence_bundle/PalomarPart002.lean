module
public import incidence_bundle.PalomarPart001
import all incidence_bundle.PalomarPart001
public import foundation_bundle
public import Lean.Elab.Tactic.Omega
@[expose] public section

noncomputable section

/-!
# Consolidated verification sources

Generated only to avoid repeatedly loading the same pinned Mathlib files.
Public theorem statements and proofs preserve their original content.
See IncidenceBundle.sources.json for exact source ranges, hashes, and private
helper alpha-renamings, topological source order, and scope adjustments.
-/

/- Original source: CubicalIndecomposability/FaceDataChecks/Anchors.lean -/
section VerificationSource001



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

def bundle_64ff450e75_cubeIncidentFacetsTable : ℕ → Finset (Fin 130) :=
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

def bundle_64ff450e75_cubeIncidentFacets (v : Fin 144) : Finset (Fin 130) :=
  bundle_64ff450e75_cubeIncidentFacetsTable v.val

theorem bundle_64ff450e75_transpose0000 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨0, by decide⟩ : Fin 144) ↔ (⟨0, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0001 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨1, by decide⟩ : Fin 144) ↔ (⟨1, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0002 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨2, by decide⟩ : Fin 144) ↔ (⟨2, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0003 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨3, by decide⟩ : Fin 144) ↔ (⟨3, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0004 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨4, by decide⟩ : Fin 144) ↔ (⟨4, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0005 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨5, by decide⟩ : Fin 144) ↔ (⟨5, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0006 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨6, by decide⟩ : Fin 144) ↔ (⟨6, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0007 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨7, by decide⟩ : Fin 144) ↔ (⟨7, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0008 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨8, by decide⟩ : Fin 144) ↔ (⟨8, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0009 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨9, by decide⟩ : Fin 144) ↔ (⟨9, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0010 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨10, by decide⟩ : Fin 144) ↔ (⟨10, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0011 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨11, by decide⟩ : Fin 144) ↔ (⟨11, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0012 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨12, by decide⟩ : Fin 144) ↔ (⟨12, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0013 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨13, by decide⟩ : Fin 144) ↔ (⟨13, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0014 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨14, by decide⟩ : Fin 144) ↔ (⟨14, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0015 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨15, by decide⟩ : Fin 144) ↔ (⟨15, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0016 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨16, by decide⟩ : Fin 144) ↔ (⟨16, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0017 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨17, by decide⟩ : Fin 144) ↔ (⟨17, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0018 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨18, by decide⟩ : Fin 144) ↔ (⟨18, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0019 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨19, by decide⟩ : Fin 144) ↔ (⟨19, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0020 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨20, by decide⟩ : Fin 144) ↔ (⟨20, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0021 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨21, by decide⟩ : Fin 144) ↔ (⟨21, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0022 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨22, by decide⟩ : Fin 144) ↔ (⟨22, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0023 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨23, by decide⟩ : Fin 144) ↔ (⟨23, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0024 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨24, by decide⟩ : Fin 144) ↔ (⟨24, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0025 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨25, by decide⟩ : Fin 144) ↔ (⟨25, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0026 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨26, by decide⟩ : Fin 144) ↔ (⟨26, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0027 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨27, by decide⟩ : Fin 144) ↔ (⟨27, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0028 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨28, by decide⟩ : Fin 144) ↔ (⟨28, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0029 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨29, by decide⟩ : Fin 144) ↔ (⟨29, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0030 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨30, by decide⟩ : Fin 144) ↔ (⟨30, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0031 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨31, by decide⟩ : Fin 144) ↔ (⟨31, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0032 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨32, by decide⟩ : Fin 144) ↔ (⟨32, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0033 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨33, by decide⟩ : Fin 144) ↔ (⟨33, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0034 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨34, by decide⟩ : Fin 144) ↔ (⟨34, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0035 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨35, by decide⟩ : Fin 144) ↔ (⟨35, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0036 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨36, by decide⟩ : Fin 144) ↔ (⟨36, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0037 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨37, by decide⟩ : Fin 144) ↔ (⟨37, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0038 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨38, by decide⟩ : Fin 144) ↔ (⟨38, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0039 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨39, by decide⟩ : Fin 144) ↔ (⟨39, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0040 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨40, by decide⟩ : Fin 144) ↔ (⟨40, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0041 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨41, by decide⟩ : Fin 144) ↔ (⟨41, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0042 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨42, by decide⟩ : Fin 144) ↔ (⟨42, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0043 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨43, by decide⟩ : Fin 144) ↔ (⟨43, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0044 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨44, by decide⟩ : Fin 144) ↔ (⟨44, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0045 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨45, by decide⟩ : Fin 144) ↔ (⟨45, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0046 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨46, by decide⟩ : Fin 144) ↔ (⟨46, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0047 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨47, by decide⟩ : Fin 144) ↔ (⟨47, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0048 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨48, by decide⟩ : Fin 144) ↔ (⟨48, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0049 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨49, by decide⟩ : Fin 144) ↔ (⟨49, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0050 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨50, by decide⟩ : Fin 144) ↔ (⟨50, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0051 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨51, by decide⟩ : Fin 144) ↔ (⟨51, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0052 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨52, by decide⟩ : Fin 144) ↔ (⟨52, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0053 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨53, by decide⟩ : Fin 144) ↔ (⟨53, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0054 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨54, by decide⟩ : Fin 144) ↔ (⟨54, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0055 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨55, by decide⟩ : Fin 144) ↔ (⟨55, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0056 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨56, by decide⟩ : Fin 144) ↔ (⟨56, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0057 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨57, by decide⟩ : Fin 144) ↔ (⟨57, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0058 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨58, by decide⟩ : Fin 144) ↔ (⟨58, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0059 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨59, by decide⟩ : Fin 144) ↔ (⟨59, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0060 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨60, by decide⟩ : Fin 144) ↔ (⟨60, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0061 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨61, by decide⟩ : Fin 144) ↔ (⟨61, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0062 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨62, by decide⟩ : Fin 144) ↔ (⟨62, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0063 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨63, by decide⟩ : Fin 144) ↔ (⟨63, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0064 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨64, by decide⟩ : Fin 144) ↔ (⟨64, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0065 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨65, by decide⟩ : Fin 144) ↔ (⟨65, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0066 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨66, by decide⟩ : Fin 144) ↔ (⟨66, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0067 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨67, by decide⟩ : Fin 144) ↔ (⟨67, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0068 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨68, by decide⟩ : Fin 144) ↔ (⟨68, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0069 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨69, by decide⟩ : Fin 144) ↔ (⟨69, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0070 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨70, by decide⟩ : Fin 144) ↔ (⟨70, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0071 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨71, by decide⟩ : Fin 144) ↔ (⟨71, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0072 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨72, by decide⟩ : Fin 144) ↔ (⟨72, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0073 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨73, by decide⟩ : Fin 144) ↔ (⟨73, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0074 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨74, by decide⟩ : Fin 144) ↔ (⟨74, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0075 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨75, by decide⟩ : Fin 144) ↔ (⟨75, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0076 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨76, by decide⟩ : Fin 144) ↔ (⟨76, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0077 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨77, by decide⟩ : Fin 144) ↔ (⟨77, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0078 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨78, by decide⟩ : Fin 144) ↔ (⟨78, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0079 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨79, by decide⟩ : Fin 144) ↔ (⟨79, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0080 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨80, by decide⟩ : Fin 144) ↔ (⟨80, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0081 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨81, by decide⟩ : Fin 144) ↔ (⟨81, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0082 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨82, by decide⟩ : Fin 144) ↔ (⟨82, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0083 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨83, by decide⟩ : Fin 144) ↔ (⟨83, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0084 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨84, by decide⟩ : Fin 144) ↔ (⟨84, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0085 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨85, by decide⟩ : Fin 144) ↔ (⟨85, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0086 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨86, by decide⟩ : Fin 144) ↔ (⟨86, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0087 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨87, by decide⟩ : Fin 144) ↔ (⟨87, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0088 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨88, by decide⟩ : Fin 144) ↔ (⟨88, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0089 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨89, by decide⟩ : Fin 144) ↔ (⟨89, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0090 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨90, by decide⟩ : Fin 144) ↔ (⟨90, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0091 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨91, by decide⟩ : Fin 144) ↔ (⟨91, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0092 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨92, by decide⟩ : Fin 144) ↔ (⟨92, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0093 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨93, by decide⟩ : Fin 144) ↔ (⟨93, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0094 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨94, by decide⟩ : Fin 144) ↔ (⟨94, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0095 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨95, by decide⟩ : Fin 144) ↔ (⟨95, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0096 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨96, by decide⟩ : Fin 144) ↔ (⟨96, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0097 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨97, by decide⟩ : Fin 144) ↔ (⟨97, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0098 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨98, by decide⟩ : Fin 144) ↔ (⟨98, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0099 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨99, by decide⟩ : Fin 144) ↔ (⟨99, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0100 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨100, by decide⟩ : Fin 144) ↔ (⟨100, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0101 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨101, by decide⟩ : Fin 144) ↔ (⟨101, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0102 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨102, by decide⟩ : Fin 144) ↔ (⟨102, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0103 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨103, by decide⟩ : Fin 144) ↔ (⟨103, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0104 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨104, by decide⟩ : Fin 144) ↔ (⟨104, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0105 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨105, by decide⟩ : Fin 144) ↔ (⟨105, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0106 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨106, by decide⟩ : Fin 144) ↔ (⟨106, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0107 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨107, by decide⟩ : Fin 144) ↔ (⟨107, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0108 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨108, by decide⟩ : Fin 144) ↔ (⟨108, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0109 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨109, by decide⟩ : Fin 144) ↔ (⟨109, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0110 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨110, by decide⟩ : Fin 144) ↔ (⟨110, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0111 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨111, by decide⟩ : Fin 144) ↔ (⟨111, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0112 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨112, by decide⟩ : Fin 144) ↔ (⟨112, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0113 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨113, by decide⟩ : Fin 144) ↔ (⟨113, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0114 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨114, by decide⟩ : Fin 144) ↔ (⟨114, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0115 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨115, by decide⟩ : Fin 144) ↔ (⟨115, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0116 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨116, by decide⟩ : Fin 144) ↔ (⟨116, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0117 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨117, by decide⟩ : Fin 144) ↔ (⟨117, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0118 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨118, by decide⟩ : Fin 144) ↔ (⟨118, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0119 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨119, by decide⟩ : Fin 144) ↔ (⟨119, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0120 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨120, by decide⟩ : Fin 144) ↔ (⟨120, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0121 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨121, by decide⟩ : Fin 144) ↔ (⟨121, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0122 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨122, by decide⟩ : Fin 144) ↔ (⟨122, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0123 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨123, by decide⟩ : Fin 144) ↔ (⟨123, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0124 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨124, by decide⟩ : Fin 144) ↔ (⟨124, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0125 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨125, by decide⟩ : Fin 144) ↔ (⟨125, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0126 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨126, by decide⟩ : Fin 144) ↔ (⟨126, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0127 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨127, by decide⟩ : Fin 144) ↔ (⟨127, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0128 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨128, by decide⟩ : Fin 144) ↔ (⟨128, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0129 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨129, by decide⟩ : Fin 144) ↔ (⟨129, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0130 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨130, by decide⟩ : Fin 144) ↔ (⟨130, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0131 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨131, by decide⟩ : Fin 144) ↔ (⟨131, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0132 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨132, by decide⟩ : Fin 144) ↔ (⟨132, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0133 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨133, by decide⟩ : Fin 144) ↔ (⟨133, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0134 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨134, by decide⟩ : Fin 144) ↔ (⟨134, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0135 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨135, by decide⟩ : Fin 144) ↔ (⟨135, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0136 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨136, by decide⟩ : Fin 144) ↔ (⟨136, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0137 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨137, by decide⟩ : Fin 144) ↔ (⟨137, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0138 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨138, by decide⟩ : Fin 144) ↔ (⟨138, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0139 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨139, by decide⟩ : Fin 144) ↔ (⟨139, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0140 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨140, by decide⟩ : Fin 144) ↔ (⟨140, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0141 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨141, by decide⟩ : Fin 144) ↔ (⟨141, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0142 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨142, by decide⟩ : Fin 144) ↔ (⟨142, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transpose0143 : ∀ f : Fin 130,
    f ∈ bundle_64ff450e75_cubeIncidentFacets (⟨143, by decide⟩ : Fin 144) ↔ (⟨143, by decide⟩ : Fin 144) ∈ facetLabels f := by
  decide +kernel

theorem bundle_64ff450e75_transposeGroup0000 (i : Fin 144)
    (hlo : 0 ≤ i.val) (hhi : i.val < 32) :
    ∀ f : Fin 130, f ∈ bundle_64ff450e75_cubeIncidentFacets i ↔ i ∈ facetLabels f := by
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
            simpa only [he] using bundle_64ff450e75_transpose0000
          ·
            have he : (⟨1, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 1 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0001
        ·
          by_cases h3 : i.val < 3
          ·
            have he : (⟨2, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 2 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0002
          ·
            have he : (⟨3, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 3 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0003
      ·
        by_cases h6 : i.val < 6
        ·
          by_cases h5 : i.val < 5
          ·
            have he : (⟨4, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 4 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0004
          ·
            have he : (⟨5, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 5 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0005
        ·
          by_cases h7 : i.val < 7
          ·
            have he : (⟨6, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 6 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0006
          ·
            have he : (⟨7, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 7 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0007
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
            simpa only [he] using bundle_64ff450e75_transpose0008
          ·
            have he : (⟨9, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 9 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0009
        ·
          by_cases h11 : i.val < 11
          ·
            have he : (⟨10, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 10 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0010
          ·
            have he : (⟨11, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 11 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0011
      ·
        by_cases h14 : i.val < 14
        ·
          by_cases h13 : i.val < 13
          ·
            have he : (⟨12, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 12 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0012
          ·
            have he : (⟨13, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 13 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0013
        ·
          by_cases h15 : i.val < 15
          ·
            have he : (⟨14, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 14 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0014
          ·
            have he : (⟨15, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 15 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0015
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
            simpa only [he] using bundle_64ff450e75_transpose0016
          ·
            have he : (⟨17, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 17 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0017
        ·
          by_cases h19 : i.val < 19
          ·
            have he : (⟨18, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 18 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0018
          ·
            have he : (⟨19, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 19 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0019
      ·
        by_cases h22 : i.val < 22
        ·
          by_cases h21 : i.val < 21
          ·
            have he : (⟨20, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 20 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0020
          ·
            have he : (⟨21, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 21 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0021
        ·
          by_cases h23 : i.val < 23
          ·
            have he : (⟨22, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 22 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0022
          ·
            have he : (⟨23, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 23 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0023
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
            simpa only [he] using bundle_64ff450e75_transpose0024
          ·
            have he : (⟨25, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 25 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0025
        ·
          by_cases h27 : i.val < 27
          ·
            have he : (⟨26, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 26 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0026
          ·
            have he : (⟨27, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 27 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0027
      ·
        by_cases h30 : i.val < 30
        ·
          by_cases h29 : i.val < 29
          ·
            have he : (⟨28, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 28 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0028
          ·
            have he : (⟨29, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 29 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0029
        ·
          by_cases h31 : i.val < 31
          ·
            have he : (⟨30, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 30 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0030
          ·
            have he : (⟨31, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 31 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0031

theorem bundle_64ff450e75_transposeGroup0001 (i : Fin 144)
    (hlo : 32 ≤ i.val) (hhi : i.val < 64) :
    ∀ f : Fin 130, f ∈ bundle_64ff450e75_cubeIncidentFacets i ↔ i ∈ facetLabels f := by
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
            simpa only [he] using bundle_64ff450e75_transpose0032
          ·
            have he : (⟨33, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 33 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0033
        ·
          by_cases h35 : i.val < 35
          ·
            have he : (⟨34, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 34 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0034
          ·
            have he : (⟨35, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 35 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0035
      ·
        by_cases h38 : i.val < 38
        ·
          by_cases h37 : i.val < 37
          ·
            have he : (⟨36, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 36 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0036
          ·
            have he : (⟨37, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 37 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0037
        ·
          by_cases h39 : i.val < 39
          ·
            have he : (⟨38, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 38 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0038
          ·
            have he : (⟨39, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 39 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0039
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
            simpa only [he] using bundle_64ff450e75_transpose0040
          ·
            have he : (⟨41, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 41 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0041
        ·
          by_cases h43 : i.val < 43
          ·
            have he : (⟨42, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 42 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0042
          ·
            have he : (⟨43, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 43 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0043
      ·
        by_cases h46 : i.val < 46
        ·
          by_cases h45 : i.val < 45
          ·
            have he : (⟨44, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 44 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0044
          ·
            have he : (⟨45, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 45 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0045
        ·
          by_cases h47 : i.val < 47
          ·
            have he : (⟨46, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 46 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0046
          ·
            have he : (⟨47, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 47 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0047
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
            simpa only [he] using bundle_64ff450e75_transpose0048
          ·
            have he : (⟨49, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 49 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0049
        ·
          by_cases h51 : i.val < 51
          ·
            have he : (⟨50, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 50 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0050
          ·
            have he : (⟨51, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 51 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0051
      ·
        by_cases h54 : i.val < 54
        ·
          by_cases h53 : i.val < 53
          ·
            have he : (⟨52, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 52 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0052
          ·
            have he : (⟨53, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 53 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0053
        ·
          by_cases h55 : i.val < 55
          ·
            have he : (⟨54, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 54 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0054
          ·
            have he : (⟨55, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 55 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0055
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
            simpa only [he] using bundle_64ff450e75_transpose0056
          ·
            have he : (⟨57, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 57 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0057
        ·
          by_cases h59 : i.val < 59
          ·
            have he : (⟨58, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 58 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0058
          ·
            have he : (⟨59, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 59 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0059
      ·
        by_cases h62 : i.val < 62
        ·
          by_cases h61 : i.val < 61
          ·
            have he : (⟨60, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 60 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0060
          ·
            have he : (⟨61, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 61 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0061
        ·
          by_cases h63 : i.val < 63
          ·
            have he : (⟨62, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 62 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0062
          ·
            have he : (⟨63, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 63 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0063

theorem bundle_64ff450e75_transposeGroup0002 (i : Fin 144)
    (hlo : 64 ≤ i.val) (hhi : i.val < 96) :
    ∀ f : Fin 130, f ∈ bundle_64ff450e75_cubeIncidentFacets i ↔ i ∈ facetLabels f := by
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
            simpa only [he] using bundle_64ff450e75_transpose0064
          ·
            have he : (⟨65, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 65 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0065
        ·
          by_cases h67 : i.val < 67
          ·
            have he : (⟨66, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 66 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0066
          ·
            have he : (⟨67, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 67 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0067
      ·
        by_cases h70 : i.val < 70
        ·
          by_cases h69 : i.val < 69
          ·
            have he : (⟨68, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 68 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0068
          ·
            have he : (⟨69, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 69 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0069
        ·
          by_cases h71 : i.val < 71
          ·
            have he : (⟨70, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 70 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0070
          ·
            have he : (⟨71, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 71 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0071
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
            simpa only [he] using bundle_64ff450e75_transpose0072
          ·
            have he : (⟨73, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 73 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0073
        ·
          by_cases h75 : i.val < 75
          ·
            have he : (⟨74, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 74 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0074
          ·
            have he : (⟨75, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 75 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0075
      ·
        by_cases h78 : i.val < 78
        ·
          by_cases h77 : i.val < 77
          ·
            have he : (⟨76, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 76 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0076
          ·
            have he : (⟨77, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 77 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0077
        ·
          by_cases h79 : i.val < 79
          ·
            have he : (⟨78, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 78 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0078
          ·
            have he : (⟨79, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 79 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0079
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
            simpa only [he] using bundle_64ff450e75_transpose0080
          ·
            have he : (⟨81, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 81 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0081
        ·
          by_cases h83 : i.val < 83
          ·
            have he : (⟨82, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 82 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0082
          ·
            have he : (⟨83, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 83 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0083
      ·
        by_cases h86 : i.val < 86
        ·
          by_cases h85 : i.val < 85
          ·
            have he : (⟨84, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 84 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0084
          ·
            have he : (⟨85, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 85 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0085
        ·
          by_cases h87 : i.val < 87
          ·
            have he : (⟨86, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 86 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0086
          ·
            have he : (⟨87, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 87 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0087
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
            simpa only [he] using bundle_64ff450e75_transpose0088
          ·
            have he : (⟨89, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 89 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0089
        ·
          by_cases h91 : i.val < 91
          ·
            have he : (⟨90, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 90 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0090
          ·
            have he : (⟨91, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 91 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0091
      ·
        by_cases h94 : i.val < 94
        ·
          by_cases h93 : i.val < 93
          ·
            have he : (⟨92, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 92 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0092
          ·
            have he : (⟨93, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 93 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0093
        ·
          by_cases h95 : i.val < 95
          ·
            have he : (⟨94, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 94 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0094
          ·
            have he : (⟨95, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 95 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0095

theorem bundle_64ff450e75_transposeGroup0003 (i : Fin 144)
    (hlo : 96 ≤ i.val) (hhi : i.val < 128) :
    ∀ f : Fin 130, f ∈ bundle_64ff450e75_cubeIncidentFacets i ↔ i ∈ facetLabels f := by
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
            simpa only [he] using bundle_64ff450e75_transpose0096
          ·
            have he : (⟨97, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 97 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0097
        ·
          by_cases h99 : i.val < 99
          ·
            have he : (⟨98, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 98 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0098
          ·
            have he : (⟨99, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 99 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0099
      ·
        by_cases h102 : i.val < 102
        ·
          by_cases h101 : i.val < 101
          ·
            have he : (⟨100, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 100 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0100
          ·
            have he : (⟨101, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 101 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0101
        ·
          by_cases h103 : i.val < 103
          ·
            have he : (⟨102, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 102 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0102
          ·
            have he : (⟨103, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 103 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0103
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
            simpa only [he] using bundle_64ff450e75_transpose0104
          ·
            have he : (⟨105, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 105 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0105
        ·
          by_cases h107 : i.val < 107
          ·
            have he : (⟨106, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 106 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0106
          ·
            have he : (⟨107, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 107 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0107
      ·
        by_cases h110 : i.val < 110
        ·
          by_cases h109 : i.val < 109
          ·
            have he : (⟨108, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 108 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0108
          ·
            have he : (⟨109, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 109 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0109
        ·
          by_cases h111 : i.val < 111
          ·
            have he : (⟨110, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 110 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0110
          ·
            have he : (⟨111, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 111 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0111
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
            simpa only [he] using bundle_64ff450e75_transpose0112
          ·
            have he : (⟨113, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 113 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0113
        ·
          by_cases h115 : i.val < 115
          ·
            have he : (⟨114, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 114 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0114
          ·
            have he : (⟨115, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 115 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0115
      ·
        by_cases h118 : i.val < 118
        ·
          by_cases h117 : i.val < 117
          ·
            have he : (⟨116, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 116 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0116
          ·
            have he : (⟨117, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 117 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0117
        ·
          by_cases h119 : i.val < 119
          ·
            have he : (⟨118, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 118 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0118
          ·
            have he : (⟨119, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 119 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0119
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
            simpa only [he] using bundle_64ff450e75_transpose0120
          ·
            have he : (⟨121, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 121 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0121
        ·
          by_cases h123 : i.val < 123
          ·
            have he : (⟨122, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 122 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0122
          ·
            have he : (⟨123, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 123 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0123
      ·
        by_cases h126 : i.val < 126
        ·
          by_cases h125 : i.val < 125
          ·
            have he : (⟨124, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 124 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0124
          ·
            have he : (⟨125, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 125 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0125
        ·
          by_cases h127 : i.val < 127
          ·
            have he : (⟨126, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 126 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0126
          ·
            have he : (⟨127, by decide⟩ : Fin 144) = i := by
              apply Fin.ext
              change 127 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_transpose0127

theorem bundle_64ff450e75_transposeGroup0004 (i : Fin 144)
    (hlo : 128 ≤ i.val) (hhi : i.val < 144) :
    ∀ f : Fin 130, f ∈ bundle_64ff450e75_cubeIncidentFacets i ↔ i ∈ facetLabels f := by
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
          simpa only [he] using bundle_64ff450e75_transpose0128
        ·
          have he : (⟨129, by decide⟩ : Fin 144) = i := by
            apply Fin.ext
            change 129 = i.val
            omega
          simpa only [he] using bundle_64ff450e75_transpose0129
      ·
        by_cases h131 : i.val < 131
        ·
          have he : (⟨130, by decide⟩ : Fin 144) = i := by
            apply Fin.ext
            change 130 = i.val
            omega
          simpa only [he] using bundle_64ff450e75_transpose0130
        ·
          have he : (⟨131, by decide⟩ : Fin 144) = i := by
            apply Fin.ext
            change 131 = i.val
            omega
          simpa only [he] using bundle_64ff450e75_transpose0131
    ·
      by_cases h134 : i.val < 134
      ·
        by_cases h133 : i.val < 133
        ·
          have he : (⟨132, by decide⟩ : Fin 144) = i := by
            apply Fin.ext
            change 132 = i.val
            omega
          simpa only [he] using bundle_64ff450e75_transpose0132
        ·
          have he : (⟨133, by decide⟩ : Fin 144) = i := by
            apply Fin.ext
            change 133 = i.val
            omega
          simpa only [he] using bundle_64ff450e75_transpose0133
      ·
        by_cases h135 : i.val < 135
        ·
          have he : (⟨134, by decide⟩ : Fin 144) = i := by
            apply Fin.ext
            change 134 = i.val
            omega
          simpa only [he] using bundle_64ff450e75_transpose0134
        ·
          have he : (⟨135, by decide⟩ : Fin 144) = i := by
            apply Fin.ext
            change 135 = i.val
            omega
          simpa only [he] using bundle_64ff450e75_transpose0135
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
          simpa only [he] using bundle_64ff450e75_transpose0136
        ·
          have he : (⟨137, by decide⟩ : Fin 144) = i := by
            apply Fin.ext
            change 137 = i.val
            omega
          simpa only [he] using bundle_64ff450e75_transpose0137
      ·
        by_cases h139 : i.val < 139
        ·
          have he : (⟨138, by decide⟩ : Fin 144) = i := by
            apply Fin.ext
            change 138 = i.val
            omega
          simpa only [he] using bundle_64ff450e75_transpose0138
        ·
          have he : (⟨139, by decide⟩ : Fin 144) = i := by
            apply Fin.ext
            change 139 = i.val
            omega
          simpa only [he] using bundle_64ff450e75_transpose0139
    ·
      by_cases h142 : i.val < 142
      ·
        by_cases h141 : i.val < 141
        ·
          have he : (⟨140, by decide⟩ : Fin 144) = i := by
            apply Fin.ext
            change 140 = i.val
            omega
          simpa only [he] using bundle_64ff450e75_transpose0140
        ·
          have he : (⟨141, by decide⟩ : Fin 144) = i := by
            apply Fin.ext
            change 141 = i.val
            omega
          simpa only [he] using bundle_64ff450e75_transpose0141
      ·
        by_cases h143 : i.val < 143
        ·
          have he : (⟨142, by decide⟩ : Fin 144) = i := by
            apply Fin.ext
            change 142 = i.val
            omega
          simpa only [he] using bundle_64ff450e75_transpose0142
        ·
          have he : (⟨143, by decide⟩ : Fin 144) = i := by
            apply Fin.ext
            change 143 = i.val
            omega
          simpa only [he] using bundle_64ff450e75_transpose0143

theorem bundle_64ff450e75_cubeIncidentFacets_iff : ∀ (v : Fin 144) (f : Fin 130),
    f ∈ bundle_64ff450e75_cubeIncidentFacets v ↔ v ∈ facetLabels f := by
  intro i
  have hi_bound := i.isLt
  by_cases h64 : i.val < 64
  ·
    by_cases h32 : i.val < 32
    ·
      exact bundle_64ff450e75_transposeGroup0000 i (by omega) (by omega)
    ·
      exact bundle_64ff450e75_transposeGroup0001 i (by omega) (by omega)
  ·
    by_cases h96 : i.val < 96
    ·
      exact bundle_64ff450e75_transposeGroup0002 i (by omega) (by omega)
    ·
      by_cases h128 : i.val < 128
      ·
        exact bundle_64ff450e75_transposeGroup0003 i (by omega) (by omega)
      ·
        exact bundle_64ff450e75_transposeGroup0004 i (by omega) (by omega)

def bundle_64ff450e75_cubeCofacets (i : Fin 1069) : Finset (Fin 130) :=
  (bundle_64ff450e75_cubeIncidentFacets (faceAnchor i)).filter
    (fun f => faceMask i ⊆ facetLabels f)

theorem bundle_64ff450e75_cubeCofacets_iff (i : Fin 1069) (f : Fin 130) :
    f ∈ bundle_64ff450e75_cubeCofacets i ↔ faceMask i ⊆ facetLabels f := by
  constructor
  · intro hf
    exact (Finset.mem_filter.mp hf).2
  · intro h
    apply Finset.mem_filter.mpr
    exact ⟨(bundle_64ff450e75_cubeIncidentFacets_iff (faceAnchor i) f).mpr
      (h (faceAnchor_mem i)), h⟩

def bundle_64ff450e75_cubeCofacetCodeTable : ℕ → Fin 130 → Fin 27 :=
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

def bundle_64ff450e75_cubeCofacetCode (i : Fin 1069) (f : Fin 130) : Fin 27 :=
  bundle_64ff450e75_cubeCofacetCodeTable i.val f

def bundle_64ff450e75_cubeCofacetCertificate (i : Fin 1069) : Prop :=
  ∀ f ∈ bundle_64ff450e75_cubeCofacets i, codeFace f (bundle_64ff450e75_cubeCofacetCode i f) = i

-- This instance traverses the finite set, not the ambient type `Fin 130`.
instance bundle_64ff450e75_cubeCofacetCertificate_decidable (i : Fin 1069) :
    Decidable (bundle_64ff450e75_cubeCofacetCertificate i) :=
  Finset.decidableDforallFinset

theorem bundle_64ff450e75_cubeCofacetCertificate_of_check (i : Fin 1069)
    (h : @decide (bundle_64ff450e75_cubeCofacetCertificate i)
      (bundle_64ff450e75_cubeCofacetCertificate_decidable i) = true) :
    bundle_64ff450e75_cubeCofacetCertificate i :=
  @of_decide_eq_true (bundle_64ff450e75_cubeCofacetCertificate i)
    (bundle_64ff450e75_cubeCofacetCertificate_decidable i) h

theorem bundle_64ff450e75_cofacet0000 : bundle_64ff450e75_cubeCofacetCertificate (⟨0, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0001 : bundle_64ff450e75_cubeCofacetCertificate (⟨1, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0002 : bundle_64ff450e75_cubeCofacetCertificate (⟨2, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0003 : bundle_64ff450e75_cubeCofacetCertificate (⟨3, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0004 : bundle_64ff450e75_cubeCofacetCertificate (⟨4, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0005 : bundle_64ff450e75_cubeCofacetCertificate (⟨5, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0006 : bundle_64ff450e75_cubeCofacetCertificate (⟨6, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0007 : bundle_64ff450e75_cubeCofacetCertificate (⟨7, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0008 : bundle_64ff450e75_cubeCofacetCertificate (⟨8, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0009 : bundle_64ff450e75_cubeCofacetCertificate (⟨9, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0010 : bundle_64ff450e75_cubeCofacetCertificate (⟨10, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0011 : bundle_64ff450e75_cubeCofacetCertificate (⟨11, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0012 : bundle_64ff450e75_cubeCofacetCertificate (⟨12, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0013 : bundle_64ff450e75_cubeCofacetCertificate (⟨13, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0014 : bundle_64ff450e75_cubeCofacetCertificate (⟨14, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0015 : bundle_64ff450e75_cubeCofacetCertificate (⟨15, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0016 : bundle_64ff450e75_cubeCofacetCertificate (⟨16, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0017 : bundle_64ff450e75_cubeCofacetCertificate (⟨17, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0018 : bundle_64ff450e75_cubeCofacetCertificate (⟨18, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0019 : bundle_64ff450e75_cubeCofacetCertificate (⟨19, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0020 : bundle_64ff450e75_cubeCofacetCertificate (⟨20, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0021 : bundle_64ff450e75_cubeCofacetCertificate (⟨21, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0022 : bundle_64ff450e75_cubeCofacetCertificate (⟨22, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0023 : bundle_64ff450e75_cubeCofacetCertificate (⟨23, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0024 : bundle_64ff450e75_cubeCofacetCertificate (⟨24, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0025 : bundle_64ff450e75_cubeCofacetCertificate (⟨25, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0026 : bundle_64ff450e75_cubeCofacetCertificate (⟨26, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0027 : bundle_64ff450e75_cubeCofacetCertificate (⟨27, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0028 : bundle_64ff450e75_cubeCofacetCertificate (⟨28, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0029 : bundle_64ff450e75_cubeCofacetCertificate (⟨29, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0030 : bundle_64ff450e75_cubeCofacetCertificate (⟨30, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0031 : bundle_64ff450e75_cubeCofacetCertificate (⟨31, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0032 : bundle_64ff450e75_cubeCofacetCertificate (⟨32, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0033 : bundle_64ff450e75_cubeCofacetCertificate (⟨33, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0034 : bundle_64ff450e75_cubeCofacetCertificate (⟨34, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0035 : bundle_64ff450e75_cubeCofacetCertificate (⟨35, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0036 : bundle_64ff450e75_cubeCofacetCertificate (⟨36, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0037 : bundle_64ff450e75_cubeCofacetCertificate (⟨37, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0038 : bundle_64ff450e75_cubeCofacetCertificate (⟨38, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0039 : bundle_64ff450e75_cubeCofacetCertificate (⟨39, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0040 : bundle_64ff450e75_cubeCofacetCertificate (⟨40, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0041 : bundle_64ff450e75_cubeCofacetCertificate (⟨41, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0042 : bundle_64ff450e75_cubeCofacetCertificate (⟨42, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0043 : bundle_64ff450e75_cubeCofacetCertificate (⟨43, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0044 : bundle_64ff450e75_cubeCofacetCertificate (⟨44, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0045 : bundle_64ff450e75_cubeCofacetCertificate (⟨45, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0046 : bundle_64ff450e75_cubeCofacetCertificate (⟨46, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0047 : bundle_64ff450e75_cubeCofacetCertificate (⟨47, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0048 : bundle_64ff450e75_cubeCofacetCertificate (⟨48, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0049 : bundle_64ff450e75_cubeCofacetCertificate (⟨49, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0050 : bundle_64ff450e75_cubeCofacetCertificate (⟨50, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0051 : bundle_64ff450e75_cubeCofacetCertificate (⟨51, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0052 : bundle_64ff450e75_cubeCofacetCertificate (⟨52, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0053 : bundle_64ff450e75_cubeCofacetCertificate (⟨53, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0054 : bundle_64ff450e75_cubeCofacetCertificate (⟨54, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0055 : bundle_64ff450e75_cubeCofacetCertificate (⟨55, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0056 : bundle_64ff450e75_cubeCofacetCertificate (⟨56, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0057 : bundle_64ff450e75_cubeCofacetCertificate (⟨57, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0058 : bundle_64ff450e75_cubeCofacetCertificate (⟨58, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0059 : bundle_64ff450e75_cubeCofacetCertificate (⟨59, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0060 : bundle_64ff450e75_cubeCofacetCertificate (⟨60, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0061 : bundle_64ff450e75_cubeCofacetCertificate (⟨61, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0062 : bundle_64ff450e75_cubeCofacetCertificate (⟨62, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0063 : bundle_64ff450e75_cubeCofacetCertificate (⟨63, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0064 : bundle_64ff450e75_cubeCofacetCertificate (⟨64, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0065 : bundle_64ff450e75_cubeCofacetCertificate (⟨65, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0066 : bundle_64ff450e75_cubeCofacetCertificate (⟨66, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0067 : bundle_64ff450e75_cubeCofacetCertificate (⟨67, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0068 : bundle_64ff450e75_cubeCofacetCertificate (⟨68, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0069 : bundle_64ff450e75_cubeCofacetCertificate (⟨69, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0070 : bundle_64ff450e75_cubeCofacetCertificate (⟨70, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0071 : bundle_64ff450e75_cubeCofacetCertificate (⟨71, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0072 : bundle_64ff450e75_cubeCofacetCertificate (⟨72, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0073 : bundle_64ff450e75_cubeCofacetCertificate (⟨73, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0074 : bundle_64ff450e75_cubeCofacetCertificate (⟨74, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0075 : bundle_64ff450e75_cubeCofacetCertificate (⟨75, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0076 : bundle_64ff450e75_cubeCofacetCertificate (⟨76, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0077 : bundle_64ff450e75_cubeCofacetCertificate (⟨77, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0078 : bundle_64ff450e75_cubeCofacetCertificate (⟨78, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0079 : bundle_64ff450e75_cubeCofacetCertificate (⟨79, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0080 : bundle_64ff450e75_cubeCofacetCertificate (⟨80, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0081 : bundle_64ff450e75_cubeCofacetCertificate (⟨81, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0082 : bundle_64ff450e75_cubeCofacetCertificate (⟨82, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0083 : bundle_64ff450e75_cubeCofacetCertificate (⟨83, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0084 : bundle_64ff450e75_cubeCofacetCertificate (⟨84, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0085 : bundle_64ff450e75_cubeCofacetCertificate (⟨85, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0086 : bundle_64ff450e75_cubeCofacetCertificate (⟨86, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0087 : bundle_64ff450e75_cubeCofacetCertificate (⟨87, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0088 : bundle_64ff450e75_cubeCofacetCertificate (⟨88, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0089 : bundle_64ff450e75_cubeCofacetCertificate (⟨89, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0090 : bundle_64ff450e75_cubeCofacetCertificate (⟨90, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0091 : bundle_64ff450e75_cubeCofacetCertificate (⟨91, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0092 : bundle_64ff450e75_cubeCofacetCertificate (⟨92, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0093 : bundle_64ff450e75_cubeCofacetCertificate (⟨93, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0094 : bundle_64ff450e75_cubeCofacetCertificate (⟨94, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0095 : bundle_64ff450e75_cubeCofacetCertificate (⟨95, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0096 : bundle_64ff450e75_cubeCofacetCertificate (⟨96, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0097 : bundle_64ff450e75_cubeCofacetCertificate (⟨97, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0098 : bundle_64ff450e75_cubeCofacetCertificate (⟨98, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0099 : bundle_64ff450e75_cubeCofacetCertificate (⟨99, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0100 : bundle_64ff450e75_cubeCofacetCertificate (⟨100, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0101 : bundle_64ff450e75_cubeCofacetCertificate (⟨101, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0102 : bundle_64ff450e75_cubeCofacetCertificate (⟨102, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0103 : bundle_64ff450e75_cubeCofacetCertificate (⟨103, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0104 : bundle_64ff450e75_cubeCofacetCertificate (⟨104, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0105 : bundle_64ff450e75_cubeCofacetCertificate (⟨105, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0106 : bundle_64ff450e75_cubeCofacetCertificate (⟨106, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0107 : bundle_64ff450e75_cubeCofacetCertificate (⟨107, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0108 : bundle_64ff450e75_cubeCofacetCertificate (⟨108, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0109 : bundle_64ff450e75_cubeCofacetCertificate (⟨109, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0110 : bundle_64ff450e75_cubeCofacetCertificate (⟨110, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0111 : bundle_64ff450e75_cubeCofacetCertificate (⟨111, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0112 : bundle_64ff450e75_cubeCofacetCertificate (⟨112, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0113 : bundle_64ff450e75_cubeCofacetCertificate (⟨113, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0114 : bundle_64ff450e75_cubeCofacetCertificate (⟨114, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0115 : bundle_64ff450e75_cubeCofacetCertificate (⟨115, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0116 : bundle_64ff450e75_cubeCofacetCertificate (⟨116, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0117 : bundle_64ff450e75_cubeCofacetCertificate (⟨117, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0118 : bundle_64ff450e75_cubeCofacetCertificate (⟨118, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0119 : bundle_64ff450e75_cubeCofacetCertificate (⟨119, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0120 : bundle_64ff450e75_cubeCofacetCertificate (⟨120, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0121 : bundle_64ff450e75_cubeCofacetCertificate (⟨121, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0122 : bundle_64ff450e75_cubeCofacetCertificate (⟨122, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0123 : bundle_64ff450e75_cubeCofacetCertificate (⟨123, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0124 : bundle_64ff450e75_cubeCofacetCertificate (⟨124, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0125 : bundle_64ff450e75_cubeCofacetCertificate (⟨125, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0126 : bundle_64ff450e75_cubeCofacetCertificate (⟨126, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0127 : bundle_64ff450e75_cubeCofacetCertificate (⟨127, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0128 : bundle_64ff450e75_cubeCofacetCertificate (⟨128, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0129 : bundle_64ff450e75_cubeCofacetCertificate (⟨129, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0130 : bundle_64ff450e75_cubeCofacetCertificate (⟨130, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0131 : bundle_64ff450e75_cubeCofacetCertificate (⟨131, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0132 : bundle_64ff450e75_cubeCofacetCertificate (⟨132, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0133 : bundle_64ff450e75_cubeCofacetCertificate (⟨133, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0134 : bundle_64ff450e75_cubeCofacetCertificate (⟨134, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0135 : bundle_64ff450e75_cubeCofacetCertificate (⟨135, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0136 : bundle_64ff450e75_cubeCofacetCertificate (⟨136, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0137 : bundle_64ff450e75_cubeCofacetCertificate (⟨137, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0138 : bundle_64ff450e75_cubeCofacetCertificate (⟨138, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0139 : bundle_64ff450e75_cubeCofacetCertificate (⟨139, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0140 : bundle_64ff450e75_cubeCofacetCertificate (⟨140, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0141 : bundle_64ff450e75_cubeCofacetCertificate (⟨141, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0142 : bundle_64ff450e75_cubeCofacetCertificate (⟨142, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0143 : bundle_64ff450e75_cubeCofacetCertificate (⟨143, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0144 : bundle_64ff450e75_cubeCofacetCertificate (⟨144, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0145 : bundle_64ff450e75_cubeCofacetCertificate (⟨145, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0146 : bundle_64ff450e75_cubeCofacetCertificate (⟨146, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0147 : bundle_64ff450e75_cubeCofacetCertificate (⟨147, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0148 : bundle_64ff450e75_cubeCofacetCertificate (⟨148, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0149 : bundle_64ff450e75_cubeCofacetCertificate (⟨149, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0150 : bundle_64ff450e75_cubeCofacetCertificate (⟨150, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0151 : bundle_64ff450e75_cubeCofacetCertificate (⟨151, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0152 : bundle_64ff450e75_cubeCofacetCertificate (⟨152, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0153 : bundle_64ff450e75_cubeCofacetCertificate (⟨153, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0154 : bundle_64ff450e75_cubeCofacetCertificate (⟨154, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0155 : bundle_64ff450e75_cubeCofacetCertificate (⟨155, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0156 : bundle_64ff450e75_cubeCofacetCertificate (⟨156, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0157 : bundle_64ff450e75_cubeCofacetCertificate (⟨157, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0158 : bundle_64ff450e75_cubeCofacetCertificate (⟨158, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0159 : bundle_64ff450e75_cubeCofacetCertificate (⟨159, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0160 : bundle_64ff450e75_cubeCofacetCertificate (⟨160, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0161 : bundle_64ff450e75_cubeCofacetCertificate (⟨161, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0162 : bundle_64ff450e75_cubeCofacetCertificate (⟨162, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0163 : bundle_64ff450e75_cubeCofacetCertificate (⟨163, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0164 : bundle_64ff450e75_cubeCofacetCertificate (⟨164, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0165 : bundle_64ff450e75_cubeCofacetCertificate (⟨165, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0166 : bundle_64ff450e75_cubeCofacetCertificate (⟨166, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0167 : bundle_64ff450e75_cubeCofacetCertificate (⟨167, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0168 : bundle_64ff450e75_cubeCofacetCertificate (⟨168, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0169 : bundle_64ff450e75_cubeCofacetCertificate (⟨169, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0170 : bundle_64ff450e75_cubeCofacetCertificate (⟨170, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0171 : bundle_64ff450e75_cubeCofacetCertificate (⟨171, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0172 : bundle_64ff450e75_cubeCofacetCertificate (⟨172, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0173 : bundle_64ff450e75_cubeCofacetCertificate (⟨173, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0174 : bundle_64ff450e75_cubeCofacetCertificate (⟨174, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0175 : bundle_64ff450e75_cubeCofacetCertificate (⟨175, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0176 : bundle_64ff450e75_cubeCofacetCertificate (⟨176, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0177 : bundle_64ff450e75_cubeCofacetCertificate (⟨177, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0178 : bundle_64ff450e75_cubeCofacetCertificate (⟨178, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0179 : bundle_64ff450e75_cubeCofacetCertificate (⟨179, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0180 : bundle_64ff450e75_cubeCofacetCertificate (⟨180, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0181 : bundle_64ff450e75_cubeCofacetCertificate (⟨181, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0182 : bundle_64ff450e75_cubeCofacetCertificate (⟨182, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0183 : bundle_64ff450e75_cubeCofacetCertificate (⟨183, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0184 : bundle_64ff450e75_cubeCofacetCertificate (⟨184, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0185 : bundle_64ff450e75_cubeCofacetCertificate (⟨185, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0186 : bundle_64ff450e75_cubeCofacetCertificate (⟨186, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0187 : bundle_64ff450e75_cubeCofacetCertificate (⟨187, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0188 : bundle_64ff450e75_cubeCofacetCertificate (⟨188, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0189 : bundle_64ff450e75_cubeCofacetCertificate (⟨189, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0190 : bundle_64ff450e75_cubeCofacetCertificate (⟨190, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0191 : bundle_64ff450e75_cubeCofacetCertificate (⟨191, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0192 : bundle_64ff450e75_cubeCofacetCertificate (⟨192, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0193 : bundle_64ff450e75_cubeCofacetCertificate (⟨193, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0194 : bundle_64ff450e75_cubeCofacetCertificate (⟨194, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0195 : bundle_64ff450e75_cubeCofacetCertificate (⟨195, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0196 : bundle_64ff450e75_cubeCofacetCertificate (⟨196, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0197 : bundle_64ff450e75_cubeCofacetCertificate (⟨197, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0198 : bundle_64ff450e75_cubeCofacetCertificate (⟨198, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0199 : bundle_64ff450e75_cubeCofacetCertificate (⟨199, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0200 : bundle_64ff450e75_cubeCofacetCertificate (⟨200, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0201 : bundle_64ff450e75_cubeCofacetCertificate (⟨201, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0202 : bundle_64ff450e75_cubeCofacetCertificate (⟨202, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0203 : bundle_64ff450e75_cubeCofacetCertificate (⟨203, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0204 : bundle_64ff450e75_cubeCofacetCertificate (⟨204, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0205 : bundle_64ff450e75_cubeCofacetCertificate (⟨205, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0206 : bundle_64ff450e75_cubeCofacetCertificate (⟨206, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0207 : bundle_64ff450e75_cubeCofacetCertificate (⟨207, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0208 : bundle_64ff450e75_cubeCofacetCertificate (⟨208, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0209 : bundle_64ff450e75_cubeCofacetCertificate (⟨209, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0210 : bundle_64ff450e75_cubeCofacetCertificate (⟨210, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0211 : bundle_64ff450e75_cubeCofacetCertificate (⟨211, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0212 : bundle_64ff450e75_cubeCofacetCertificate (⟨212, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0213 : bundle_64ff450e75_cubeCofacetCertificate (⟨213, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0214 : bundle_64ff450e75_cubeCofacetCertificate (⟨214, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0215 : bundle_64ff450e75_cubeCofacetCertificate (⟨215, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0216 : bundle_64ff450e75_cubeCofacetCertificate (⟨216, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0217 : bundle_64ff450e75_cubeCofacetCertificate (⟨217, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0218 : bundle_64ff450e75_cubeCofacetCertificate (⟨218, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0219 : bundle_64ff450e75_cubeCofacetCertificate (⟨219, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0220 : bundle_64ff450e75_cubeCofacetCertificate (⟨220, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0221 : bundle_64ff450e75_cubeCofacetCertificate (⟨221, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0222 : bundle_64ff450e75_cubeCofacetCertificate (⟨222, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0223 : bundle_64ff450e75_cubeCofacetCertificate (⟨223, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0224 : bundle_64ff450e75_cubeCofacetCertificate (⟨224, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0225 : bundle_64ff450e75_cubeCofacetCertificate (⟨225, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0226 : bundle_64ff450e75_cubeCofacetCertificate (⟨226, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0227 : bundle_64ff450e75_cubeCofacetCertificate (⟨227, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0228 : bundle_64ff450e75_cubeCofacetCertificate (⟨228, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0229 : bundle_64ff450e75_cubeCofacetCertificate (⟨229, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0230 : bundle_64ff450e75_cubeCofacetCertificate (⟨230, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0231 : bundle_64ff450e75_cubeCofacetCertificate (⟨231, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0232 : bundle_64ff450e75_cubeCofacetCertificate (⟨232, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0233 : bundle_64ff450e75_cubeCofacetCertificate (⟨233, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0234 : bundle_64ff450e75_cubeCofacetCertificate (⟨234, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0235 : bundle_64ff450e75_cubeCofacetCertificate (⟨235, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0236 : bundle_64ff450e75_cubeCofacetCertificate (⟨236, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0237 : bundle_64ff450e75_cubeCofacetCertificate (⟨237, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0238 : bundle_64ff450e75_cubeCofacetCertificate (⟨238, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0239 : bundle_64ff450e75_cubeCofacetCertificate (⟨239, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0240 : bundle_64ff450e75_cubeCofacetCertificate (⟨240, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0241 : bundle_64ff450e75_cubeCofacetCertificate (⟨241, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0242 : bundle_64ff450e75_cubeCofacetCertificate (⟨242, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0243 : bundle_64ff450e75_cubeCofacetCertificate (⟨243, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0244 : bundle_64ff450e75_cubeCofacetCertificate (⟨244, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0245 : bundle_64ff450e75_cubeCofacetCertificate (⟨245, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0246 : bundle_64ff450e75_cubeCofacetCertificate (⟨246, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0247 : bundle_64ff450e75_cubeCofacetCertificate (⟨247, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0248 : bundle_64ff450e75_cubeCofacetCertificate (⟨248, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0249 : bundle_64ff450e75_cubeCofacetCertificate (⟨249, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0250 : bundle_64ff450e75_cubeCofacetCertificate (⟨250, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0251 : bundle_64ff450e75_cubeCofacetCertificate (⟨251, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0252 : bundle_64ff450e75_cubeCofacetCertificate (⟨252, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0253 : bundle_64ff450e75_cubeCofacetCertificate (⟨253, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0254 : bundle_64ff450e75_cubeCofacetCertificate (⟨254, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0255 : bundle_64ff450e75_cubeCofacetCertificate (⟨255, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0256 : bundle_64ff450e75_cubeCofacetCertificate (⟨256, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0257 : bundle_64ff450e75_cubeCofacetCertificate (⟨257, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0258 : bundle_64ff450e75_cubeCofacetCertificate (⟨258, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0259 : bundle_64ff450e75_cubeCofacetCertificate (⟨259, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0260 : bundle_64ff450e75_cubeCofacetCertificate (⟨260, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0261 : bundle_64ff450e75_cubeCofacetCertificate (⟨261, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0262 : bundle_64ff450e75_cubeCofacetCertificate (⟨262, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0263 : bundle_64ff450e75_cubeCofacetCertificate (⟨263, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0264 : bundle_64ff450e75_cubeCofacetCertificate (⟨264, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0265 : bundle_64ff450e75_cubeCofacetCertificate (⟨265, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0266 : bundle_64ff450e75_cubeCofacetCertificate (⟨266, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0267 : bundle_64ff450e75_cubeCofacetCertificate (⟨267, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0268 : bundle_64ff450e75_cubeCofacetCertificate (⟨268, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0269 : bundle_64ff450e75_cubeCofacetCertificate (⟨269, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0270 : bundle_64ff450e75_cubeCofacetCertificate (⟨270, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0271 : bundle_64ff450e75_cubeCofacetCertificate (⟨271, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0272 : bundle_64ff450e75_cubeCofacetCertificate (⟨272, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0273 : bundle_64ff450e75_cubeCofacetCertificate (⟨273, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0274 : bundle_64ff450e75_cubeCofacetCertificate (⟨274, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0275 : bundle_64ff450e75_cubeCofacetCertificate (⟨275, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0276 : bundle_64ff450e75_cubeCofacetCertificate (⟨276, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0277 : bundle_64ff450e75_cubeCofacetCertificate (⟨277, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0278 : bundle_64ff450e75_cubeCofacetCertificate (⟨278, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0279 : bundle_64ff450e75_cubeCofacetCertificate (⟨279, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0280 : bundle_64ff450e75_cubeCofacetCertificate (⟨280, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0281 : bundle_64ff450e75_cubeCofacetCertificate (⟨281, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0282 : bundle_64ff450e75_cubeCofacetCertificate (⟨282, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0283 : bundle_64ff450e75_cubeCofacetCertificate (⟨283, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0284 : bundle_64ff450e75_cubeCofacetCertificate (⟨284, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0285 : bundle_64ff450e75_cubeCofacetCertificate (⟨285, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0286 : bundle_64ff450e75_cubeCofacetCertificate (⟨286, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0287 : bundle_64ff450e75_cubeCofacetCertificate (⟨287, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0288 : bundle_64ff450e75_cubeCofacetCertificate (⟨288, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0289 : bundle_64ff450e75_cubeCofacetCertificate (⟨289, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0290 : bundle_64ff450e75_cubeCofacetCertificate (⟨290, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0291 : bundle_64ff450e75_cubeCofacetCertificate (⟨291, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0292 : bundle_64ff450e75_cubeCofacetCertificate (⟨292, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0293 : bundle_64ff450e75_cubeCofacetCertificate (⟨293, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0294 : bundle_64ff450e75_cubeCofacetCertificate (⟨294, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0295 : bundle_64ff450e75_cubeCofacetCertificate (⟨295, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0296 : bundle_64ff450e75_cubeCofacetCertificate (⟨296, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0297 : bundle_64ff450e75_cubeCofacetCertificate (⟨297, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0298 : bundle_64ff450e75_cubeCofacetCertificate (⟨298, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0299 : bundle_64ff450e75_cubeCofacetCertificate (⟨299, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0300 : bundle_64ff450e75_cubeCofacetCertificate (⟨300, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0301 : bundle_64ff450e75_cubeCofacetCertificate (⟨301, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0302 : bundle_64ff450e75_cubeCofacetCertificate (⟨302, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0303 : bundle_64ff450e75_cubeCofacetCertificate (⟨303, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0304 : bundle_64ff450e75_cubeCofacetCertificate (⟨304, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0305 : bundle_64ff450e75_cubeCofacetCertificate (⟨305, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0306 : bundle_64ff450e75_cubeCofacetCertificate (⟨306, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0307 : bundle_64ff450e75_cubeCofacetCertificate (⟨307, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0308 : bundle_64ff450e75_cubeCofacetCertificate (⟨308, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0309 : bundle_64ff450e75_cubeCofacetCertificate (⟨309, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0310 : bundle_64ff450e75_cubeCofacetCertificate (⟨310, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0311 : bundle_64ff450e75_cubeCofacetCertificate (⟨311, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0312 : bundle_64ff450e75_cubeCofacetCertificate (⟨312, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0313 : bundle_64ff450e75_cubeCofacetCertificate (⟨313, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0314 : bundle_64ff450e75_cubeCofacetCertificate (⟨314, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0315 : bundle_64ff450e75_cubeCofacetCertificate (⟨315, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0316 : bundle_64ff450e75_cubeCofacetCertificate (⟨316, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0317 : bundle_64ff450e75_cubeCofacetCertificate (⟨317, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0318 : bundle_64ff450e75_cubeCofacetCertificate (⟨318, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0319 : bundle_64ff450e75_cubeCofacetCertificate (⟨319, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0320 : bundle_64ff450e75_cubeCofacetCertificate (⟨320, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0321 : bundle_64ff450e75_cubeCofacetCertificate (⟨321, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0322 : bundle_64ff450e75_cubeCofacetCertificate (⟨322, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0323 : bundle_64ff450e75_cubeCofacetCertificate (⟨323, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0324 : bundle_64ff450e75_cubeCofacetCertificate (⟨324, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0325 : bundle_64ff450e75_cubeCofacetCertificate (⟨325, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0326 : bundle_64ff450e75_cubeCofacetCertificate (⟨326, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0327 : bundle_64ff450e75_cubeCofacetCertificate (⟨327, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0328 : bundle_64ff450e75_cubeCofacetCertificate (⟨328, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0329 : bundle_64ff450e75_cubeCofacetCertificate (⟨329, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0330 : bundle_64ff450e75_cubeCofacetCertificate (⟨330, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0331 : bundle_64ff450e75_cubeCofacetCertificate (⟨331, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0332 : bundle_64ff450e75_cubeCofacetCertificate (⟨332, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0333 : bundle_64ff450e75_cubeCofacetCertificate (⟨333, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0334 : bundle_64ff450e75_cubeCofacetCertificate (⟨334, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0335 : bundle_64ff450e75_cubeCofacetCertificate (⟨335, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0336 : bundle_64ff450e75_cubeCofacetCertificate (⟨336, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0337 : bundle_64ff450e75_cubeCofacetCertificate (⟨337, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0338 : bundle_64ff450e75_cubeCofacetCertificate (⟨338, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0339 : bundle_64ff450e75_cubeCofacetCertificate (⟨339, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0340 : bundle_64ff450e75_cubeCofacetCertificate (⟨340, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0341 : bundle_64ff450e75_cubeCofacetCertificate (⟨341, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0342 : bundle_64ff450e75_cubeCofacetCertificate (⟨342, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0343 : bundle_64ff450e75_cubeCofacetCertificate (⟨343, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0344 : bundle_64ff450e75_cubeCofacetCertificate (⟨344, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0345 : bundle_64ff450e75_cubeCofacetCertificate (⟨345, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0346 : bundle_64ff450e75_cubeCofacetCertificate (⟨346, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0347 : bundle_64ff450e75_cubeCofacetCertificate (⟨347, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0348 : bundle_64ff450e75_cubeCofacetCertificate (⟨348, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0349 : bundle_64ff450e75_cubeCofacetCertificate (⟨349, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0350 : bundle_64ff450e75_cubeCofacetCertificate (⟨350, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0351 : bundle_64ff450e75_cubeCofacetCertificate (⟨351, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0352 : bundle_64ff450e75_cubeCofacetCertificate (⟨352, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0353 : bundle_64ff450e75_cubeCofacetCertificate (⟨353, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0354 : bundle_64ff450e75_cubeCofacetCertificate (⟨354, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0355 : bundle_64ff450e75_cubeCofacetCertificate (⟨355, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0356 : bundle_64ff450e75_cubeCofacetCertificate (⟨356, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0357 : bundle_64ff450e75_cubeCofacetCertificate (⟨357, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0358 : bundle_64ff450e75_cubeCofacetCertificate (⟨358, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0359 : bundle_64ff450e75_cubeCofacetCertificate (⟨359, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0360 : bundle_64ff450e75_cubeCofacetCertificate (⟨360, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0361 : bundle_64ff450e75_cubeCofacetCertificate (⟨361, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0362 : bundle_64ff450e75_cubeCofacetCertificate (⟨362, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0363 : bundle_64ff450e75_cubeCofacetCertificate (⟨363, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0364 : bundle_64ff450e75_cubeCofacetCertificate (⟨364, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0365 : bundle_64ff450e75_cubeCofacetCertificate (⟨365, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0366 : bundle_64ff450e75_cubeCofacetCertificate (⟨366, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0367 : bundle_64ff450e75_cubeCofacetCertificate (⟨367, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0368 : bundle_64ff450e75_cubeCofacetCertificate (⟨368, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0369 : bundle_64ff450e75_cubeCofacetCertificate (⟨369, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0370 : bundle_64ff450e75_cubeCofacetCertificate (⟨370, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0371 : bundle_64ff450e75_cubeCofacetCertificate (⟨371, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0372 : bundle_64ff450e75_cubeCofacetCertificate (⟨372, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0373 : bundle_64ff450e75_cubeCofacetCertificate (⟨373, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0374 : bundle_64ff450e75_cubeCofacetCertificate (⟨374, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0375 : bundle_64ff450e75_cubeCofacetCertificate (⟨375, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0376 : bundle_64ff450e75_cubeCofacetCertificate (⟨376, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0377 : bundle_64ff450e75_cubeCofacetCertificate (⟨377, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0378 : bundle_64ff450e75_cubeCofacetCertificate (⟨378, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0379 : bundle_64ff450e75_cubeCofacetCertificate (⟨379, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0380 : bundle_64ff450e75_cubeCofacetCertificate (⟨380, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0381 : bundle_64ff450e75_cubeCofacetCertificate (⟨381, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0382 : bundle_64ff450e75_cubeCofacetCertificate (⟨382, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0383 : bundle_64ff450e75_cubeCofacetCertificate (⟨383, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0384 : bundle_64ff450e75_cubeCofacetCertificate (⟨384, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0385 : bundle_64ff450e75_cubeCofacetCertificate (⟨385, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0386 : bundle_64ff450e75_cubeCofacetCertificate (⟨386, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0387 : bundle_64ff450e75_cubeCofacetCertificate (⟨387, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0388 : bundle_64ff450e75_cubeCofacetCertificate (⟨388, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0389 : bundle_64ff450e75_cubeCofacetCertificate (⟨389, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0390 : bundle_64ff450e75_cubeCofacetCertificate (⟨390, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0391 : bundle_64ff450e75_cubeCofacetCertificate (⟨391, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0392 : bundle_64ff450e75_cubeCofacetCertificate (⟨392, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0393 : bundle_64ff450e75_cubeCofacetCertificate (⟨393, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0394 : bundle_64ff450e75_cubeCofacetCertificate (⟨394, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0395 : bundle_64ff450e75_cubeCofacetCertificate (⟨395, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0396 : bundle_64ff450e75_cubeCofacetCertificate (⟨396, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0397 : bundle_64ff450e75_cubeCofacetCertificate (⟨397, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0398 : bundle_64ff450e75_cubeCofacetCertificate (⟨398, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0399 : bundle_64ff450e75_cubeCofacetCertificate (⟨399, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0400 : bundle_64ff450e75_cubeCofacetCertificate (⟨400, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0401 : bundle_64ff450e75_cubeCofacetCertificate (⟨401, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0402 : bundle_64ff450e75_cubeCofacetCertificate (⟨402, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0403 : bundle_64ff450e75_cubeCofacetCertificate (⟨403, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0404 : bundle_64ff450e75_cubeCofacetCertificate (⟨404, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0405 : bundle_64ff450e75_cubeCofacetCertificate (⟨405, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0406 : bundle_64ff450e75_cubeCofacetCertificate (⟨406, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0407 : bundle_64ff450e75_cubeCofacetCertificate (⟨407, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0408 : bundle_64ff450e75_cubeCofacetCertificate (⟨408, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0409 : bundle_64ff450e75_cubeCofacetCertificate (⟨409, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0410 : bundle_64ff450e75_cubeCofacetCertificate (⟨410, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0411 : bundle_64ff450e75_cubeCofacetCertificate (⟨411, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0412 : bundle_64ff450e75_cubeCofacetCertificate (⟨412, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0413 : bundle_64ff450e75_cubeCofacetCertificate (⟨413, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0414 : bundle_64ff450e75_cubeCofacetCertificate (⟨414, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0415 : bundle_64ff450e75_cubeCofacetCertificate (⟨415, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0416 : bundle_64ff450e75_cubeCofacetCertificate (⟨416, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0417 : bundle_64ff450e75_cubeCofacetCertificate (⟨417, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0418 : bundle_64ff450e75_cubeCofacetCertificate (⟨418, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0419 : bundle_64ff450e75_cubeCofacetCertificate (⟨419, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0420 : bundle_64ff450e75_cubeCofacetCertificate (⟨420, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0421 : bundle_64ff450e75_cubeCofacetCertificate (⟨421, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0422 : bundle_64ff450e75_cubeCofacetCertificate (⟨422, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0423 : bundle_64ff450e75_cubeCofacetCertificate (⟨423, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0424 : bundle_64ff450e75_cubeCofacetCertificate (⟨424, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0425 : bundle_64ff450e75_cubeCofacetCertificate (⟨425, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0426 : bundle_64ff450e75_cubeCofacetCertificate (⟨426, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0427 : bundle_64ff450e75_cubeCofacetCertificate (⟨427, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0428 : bundle_64ff450e75_cubeCofacetCertificate (⟨428, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0429 : bundle_64ff450e75_cubeCofacetCertificate (⟨429, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0430 : bundle_64ff450e75_cubeCofacetCertificate (⟨430, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0431 : bundle_64ff450e75_cubeCofacetCertificate (⟨431, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0432 : bundle_64ff450e75_cubeCofacetCertificate (⟨432, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0433 : bundle_64ff450e75_cubeCofacetCertificate (⟨433, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0434 : bundle_64ff450e75_cubeCofacetCertificate (⟨434, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0435 : bundle_64ff450e75_cubeCofacetCertificate (⟨435, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0436 : bundle_64ff450e75_cubeCofacetCertificate (⟨436, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0437 : bundle_64ff450e75_cubeCofacetCertificate (⟨437, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0438 : bundle_64ff450e75_cubeCofacetCertificate (⟨438, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0439 : bundle_64ff450e75_cubeCofacetCertificate (⟨439, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0440 : bundle_64ff450e75_cubeCofacetCertificate (⟨440, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0441 : bundle_64ff450e75_cubeCofacetCertificate (⟨441, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0442 : bundle_64ff450e75_cubeCofacetCertificate (⟨442, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0443 : bundle_64ff450e75_cubeCofacetCertificate (⟨443, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0444 : bundle_64ff450e75_cubeCofacetCertificate (⟨444, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0445 : bundle_64ff450e75_cubeCofacetCertificate (⟨445, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0446 : bundle_64ff450e75_cubeCofacetCertificate (⟨446, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0447 : bundle_64ff450e75_cubeCofacetCertificate (⟨447, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0448 : bundle_64ff450e75_cubeCofacetCertificate (⟨448, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0449 : bundle_64ff450e75_cubeCofacetCertificate (⟨449, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0450 : bundle_64ff450e75_cubeCofacetCertificate (⟨450, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0451 : bundle_64ff450e75_cubeCofacetCertificate (⟨451, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0452 : bundle_64ff450e75_cubeCofacetCertificate (⟨452, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0453 : bundle_64ff450e75_cubeCofacetCertificate (⟨453, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0454 : bundle_64ff450e75_cubeCofacetCertificate (⟨454, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0455 : bundle_64ff450e75_cubeCofacetCertificate (⟨455, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0456 : bundle_64ff450e75_cubeCofacetCertificate (⟨456, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0457 : bundle_64ff450e75_cubeCofacetCertificate (⟨457, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0458 : bundle_64ff450e75_cubeCofacetCertificate (⟨458, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0459 : bundle_64ff450e75_cubeCofacetCertificate (⟨459, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0460 : bundle_64ff450e75_cubeCofacetCertificate (⟨460, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0461 : bundle_64ff450e75_cubeCofacetCertificate (⟨461, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0462 : bundle_64ff450e75_cubeCofacetCertificate (⟨462, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0463 : bundle_64ff450e75_cubeCofacetCertificate (⟨463, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0464 : bundle_64ff450e75_cubeCofacetCertificate (⟨464, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0465 : bundle_64ff450e75_cubeCofacetCertificate (⟨465, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0466 : bundle_64ff450e75_cubeCofacetCertificate (⟨466, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0467 : bundle_64ff450e75_cubeCofacetCertificate (⟨467, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0468 : bundle_64ff450e75_cubeCofacetCertificate (⟨468, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0469 : bundle_64ff450e75_cubeCofacetCertificate (⟨469, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0470 : bundle_64ff450e75_cubeCofacetCertificate (⟨470, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0471 : bundle_64ff450e75_cubeCofacetCertificate (⟨471, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0472 : bundle_64ff450e75_cubeCofacetCertificate (⟨472, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0473 : bundle_64ff450e75_cubeCofacetCertificate (⟨473, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0474 : bundle_64ff450e75_cubeCofacetCertificate (⟨474, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0475 : bundle_64ff450e75_cubeCofacetCertificate (⟨475, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0476 : bundle_64ff450e75_cubeCofacetCertificate (⟨476, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0477 : bundle_64ff450e75_cubeCofacetCertificate (⟨477, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0478 : bundle_64ff450e75_cubeCofacetCertificate (⟨478, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0479 : bundle_64ff450e75_cubeCofacetCertificate (⟨479, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0480 : bundle_64ff450e75_cubeCofacetCertificate (⟨480, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0481 : bundle_64ff450e75_cubeCofacetCertificate (⟨481, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0482 : bundle_64ff450e75_cubeCofacetCertificate (⟨482, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0483 : bundle_64ff450e75_cubeCofacetCertificate (⟨483, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0484 : bundle_64ff450e75_cubeCofacetCertificate (⟨484, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0485 : bundle_64ff450e75_cubeCofacetCertificate (⟨485, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0486 : bundle_64ff450e75_cubeCofacetCertificate (⟨486, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0487 : bundle_64ff450e75_cubeCofacetCertificate (⟨487, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0488 : bundle_64ff450e75_cubeCofacetCertificate (⟨488, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0489 : bundle_64ff450e75_cubeCofacetCertificate (⟨489, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0490 : bundle_64ff450e75_cubeCofacetCertificate (⟨490, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0491 : bundle_64ff450e75_cubeCofacetCertificate (⟨491, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0492 : bundle_64ff450e75_cubeCofacetCertificate (⟨492, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0493 : bundle_64ff450e75_cubeCofacetCertificate (⟨493, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0494 : bundle_64ff450e75_cubeCofacetCertificate (⟨494, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0495 : bundle_64ff450e75_cubeCofacetCertificate (⟨495, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0496 : bundle_64ff450e75_cubeCofacetCertificate (⟨496, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0497 : bundle_64ff450e75_cubeCofacetCertificate (⟨497, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0498 : bundle_64ff450e75_cubeCofacetCertificate (⟨498, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0499 : bundle_64ff450e75_cubeCofacetCertificate (⟨499, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0500 : bundle_64ff450e75_cubeCofacetCertificate (⟨500, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0501 : bundle_64ff450e75_cubeCofacetCertificate (⟨501, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0502 : bundle_64ff450e75_cubeCofacetCertificate (⟨502, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0503 : bundle_64ff450e75_cubeCofacetCertificate (⟨503, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0504 : bundle_64ff450e75_cubeCofacetCertificate (⟨504, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0505 : bundle_64ff450e75_cubeCofacetCertificate (⟨505, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0506 : bundle_64ff450e75_cubeCofacetCertificate (⟨506, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0507 : bundle_64ff450e75_cubeCofacetCertificate (⟨507, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0508 : bundle_64ff450e75_cubeCofacetCertificate (⟨508, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0509 : bundle_64ff450e75_cubeCofacetCertificate (⟨509, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0510 : bundle_64ff450e75_cubeCofacetCertificate (⟨510, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0511 : bundle_64ff450e75_cubeCofacetCertificate (⟨511, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0512 : bundle_64ff450e75_cubeCofacetCertificate (⟨512, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0513 : bundle_64ff450e75_cubeCofacetCertificate (⟨513, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0514 : bundle_64ff450e75_cubeCofacetCertificate (⟨514, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0515 : bundle_64ff450e75_cubeCofacetCertificate (⟨515, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0516 : bundle_64ff450e75_cubeCofacetCertificate (⟨516, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0517 : bundle_64ff450e75_cubeCofacetCertificate (⟨517, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0518 : bundle_64ff450e75_cubeCofacetCertificate (⟨518, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0519 : bundle_64ff450e75_cubeCofacetCertificate (⟨519, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0520 : bundle_64ff450e75_cubeCofacetCertificate (⟨520, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0521 : bundle_64ff450e75_cubeCofacetCertificate (⟨521, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0522 : bundle_64ff450e75_cubeCofacetCertificate (⟨522, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0523 : bundle_64ff450e75_cubeCofacetCertificate (⟨523, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0524 : bundle_64ff450e75_cubeCofacetCertificate (⟨524, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0525 : bundle_64ff450e75_cubeCofacetCertificate (⟨525, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0526 : bundle_64ff450e75_cubeCofacetCertificate (⟨526, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0527 : bundle_64ff450e75_cubeCofacetCertificate (⟨527, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0528 : bundle_64ff450e75_cubeCofacetCertificate (⟨528, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0529 : bundle_64ff450e75_cubeCofacetCertificate (⟨529, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0530 : bundle_64ff450e75_cubeCofacetCertificate (⟨530, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0531 : bundle_64ff450e75_cubeCofacetCertificate (⟨531, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0532 : bundle_64ff450e75_cubeCofacetCertificate (⟨532, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0533 : bundle_64ff450e75_cubeCofacetCertificate (⟨533, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0534 : bundle_64ff450e75_cubeCofacetCertificate (⟨534, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0535 : bundle_64ff450e75_cubeCofacetCertificate (⟨535, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0536 : bundle_64ff450e75_cubeCofacetCertificate (⟨536, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0537 : bundle_64ff450e75_cubeCofacetCertificate (⟨537, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0538 : bundle_64ff450e75_cubeCofacetCertificate (⟨538, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0539 : bundle_64ff450e75_cubeCofacetCertificate (⟨539, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0540 : bundle_64ff450e75_cubeCofacetCertificate (⟨540, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0541 : bundle_64ff450e75_cubeCofacetCertificate (⟨541, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0542 : bundle_64ff450e75_cubeCofacetCertificate (⟨542, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0543 : bundle_64ff450e75_cubeCofacetCertificate (⟨543, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0544 : bundle_64ff450e75_cubeCofacetCertificate (⟨544, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0545 : bundle_64ff450e75_cubeCofacetCertificate (⟨545, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0546 : bundle_64ff450e75_cubeCofacetCertificate (⟨546, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0547 : bundle_64ff450e75_cubeCofacetCertificate (⟨547, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0548 : bundle_64ff450e75_cubeCofacetCertificate (⟨548, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0549 : bundle_64ff450e75_cubeCofacetCertificate (⟨549, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0550 : bundle_64ff450e75_cubeCofacetCertificate (⟨550, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0551 : bundle_64ff450e75_cubeCofacetCertificate (⟨551, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0552 : bundle_64ff450e75_cubeCofacetCertificate (⟨552, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0553 : bundle_64ff450e75_cubeCofacetCertificate (⟨553, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0554 : bundle_64ff450e75_cubeCofacetCertificate (⟨554, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0555 : bundle_64ff450e75_cubeCofacetCertificate (⟨555, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0556 : bundle_64ff450e75_cubeCofacetCertificate (⟨556, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0557 : bundle_64ff450e75_cubeCofacetCertificate (⟨557, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0558 : bundle_64ff450e75_cubeCofacetCertificate (⟨558, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0559 : bundle_64ff450e75_cubeCofacetCertificate (⟨559, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0560 : bundle_64ff450e75_cubeCofacetCertificate (⟨560, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0561 : bundle_64ff450e75_cubeCofacetCertificate (⟨561, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0562 : bundle_64ff450e75_cubeCofacetCertificate (⟨562, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0563 : bundle_64ff450e75_cubeCofacetCertificate (⟨563, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0564 : bundle_64ff450e75_cubeCofacetCertificate (⟨564, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0565 : bundle_64ff450e75_cubeCofacetCertificate (⟨565, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0566 : bundle_64ff450e75_cubeCofacetCertificate (⟨566, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0567 : bundle_64ff450e75_cubeCofacetCertificate (⟨567, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0568 : bundle_64ff450e75_cubeCofacetCertificate (⟨568, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0569 : bundle_64ff450e75_cubeCofacetCertificate (⟨569, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0570 : bundle_64ff450e75_cubeCofacetCertificate (⟨570, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0571 : bundle_64ff450e75_cubeCofacetCertificate (⟨571, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0572 : bundle_64ff450e75_cubeCofacetCertificate (⟨572, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0573 : bundle_64ff450e75_cubeCofacetCertificate (⟨573, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0574 : bundle_64ff450e75_cubeCofacetCertificate (⟨574, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0575 : bundle_64ff450e75_cubeCofacetCertificate (⟨575, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0576 : bundle_64ff450e75_cubeCofacetCertificate (⟨576, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0577 : bundle_64ff450e75_cubeCofacetCertificate (⟨577, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0578 : bundle_64ff450e75_cubeCofacetCertificate (⟨578, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0579 : bundle_64ff450e75_cubeCofacetCertificate (⟨579, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0580 : bundle_64ff450e75_cubeCofacetCertificate (⟨580, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0581 : bundle_64ff450e75_cubeCofacetCertificate (⟨581, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0582 : bundle_64ff450e75_cubeCofacetCertificate (⟨582, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0583 : bundle_64ff450e75_cubeCofacetCertificate (⟨583, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0584 : bundle_64ff450e75_cubeCofacetCertificate (⟨584, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0585 : bundle_64ff450e75_cubeCofacetCertificate (⟨585, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0586 : bundle_64ff450e75_cubeCofacetCertificate (⟨586, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0587 : bundle_64ff450e75_cubeCofacetCertificate (⟨587, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0588 : bundle_64ff450e75_cubeCofacetCertificate (⟨588, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0589 : bundle_64ff450e75_cubeCofacetCertificate (⟨589, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0590 : bundle_64ff450e75_cubeCofacetCertificate (⟨590, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0591 : bundle_64ff450e75_cubeCofacetCertificate (⟨591, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0592 : bundle_64ff450e75_cubeCofacetCertificate (⟨592, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0593 : bundle_64ff450e75_cubeCofacetCertificate (⟨593, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0594 : bundle_64ff450e75_cubeCofacetCertificate (⟨594, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0595 : bundle_64ff450e75_cubeCofacetCertificate (⟨595, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0596 : bundle_64ff450e75_cubeCofacetCertificate (⟨596, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0597 : bundle_64ff450e75_cubeCofacetCertificate (⟨597, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0598 : bundle_64ff450e75_cubeCofacetCertificate (⟨598, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0599 : bundle_64ff450e75_cubeCofacetCertificate (⟨599, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0600 : bundle_64ff450e75_cubeCofacetCertificate (⟨600, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0601 : bundle_64ff450e75_cubeCofacetCertificate (⟨601, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0602 : bundle_64ff450e75_cubeCofacetCertificate (⟨602, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0603 : bundle_64ff450e75_cubeCofacetCertificate (⟨603, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0604 : bundle_64ff450e75_cubeCofacetCertificate (⟨604, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0605 : bundle_64ff450e75_cubeCofacetCertificate (⟨605, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0606 : bundle_64ff450e75_cubeCofacetCertificate (⟨606, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0607 : bundle_64ff450e75_cubeCofacetCertificate (⟨607, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0608 : bundle_64ff450e75_cubeCofacetCertificate (⟨608, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0609 : bundle_64ff450e75_cubeCofacetCertificate (⟨609, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0610 : bundle_64ff450e75_cubeCofacetCertificate (⟨610, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0611 : bundle_64ff450e75_cubeCofacetCertificate (⟨611, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0612 : bundle_64ff450e75_cubeCofacetCertificate (⟨612, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0613 : bundle_64ff450e75_cubeCofacetCertificate (⟨613, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0614 : bundle_64ff450e75_cubeCofacetCertificate (⟨614, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0615 : bundle_64ff450e75_cubeCofacetCertificate (⟨615, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0616 : bundle_64ff450e75_cubeCofacetCertificate (⟨616, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0617 : bundle_64ff450e75_cubeCofacetCertificate (⟨617, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0618 : bundle_64ff450e75_cubeCofacetCertificate (⟨618, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0619 : bundle_64ff450e75_cubeCofacetCertificate (⟨619, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0620 : bundle_64ff450e75_cubeCofacetCertificate (⟨620, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0621 : bundle_64ff450e75_cubeCofacetCertificate (⟨621, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0622 : bundle_64ff450e75_cubeCofacetCertificate (⟨622, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0623 : bundle_64ff450e75_cubeCofacetCertificate (⟨623, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0624 : bundle_64ff450e75_cubeCofacetCertificate (⟨624, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0625 : bundle_64ff450e75_cubeCofacetCertificate (⟨625, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0626 : bundle_64ff450e75_cubeCofacetCertificate (⟨626, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0627 : bundle_64ff450e75_cubeCofacetCertificate (⟨627, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0628 : bundle_64ff450e75_cubeCofacetCertificate (⟨628, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0629 : bundle_64ff450e75_cubeCofacetCertificate (⟨629, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0630 : bundle_64ff450e75_cubeCofacetCertificate (⟨630, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0631 : bundle_64ff450e75_cubeCofacetCertificate (⟨631, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0632 : bundle_64ff450e75_cubeCofacetCertificate (⟨632, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0633 : bundle_64ff450e75_cubeCofacetCertificate (⟨633, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0634 : bundle_64ff450e75_cubeCofacetCertificate (⟨634, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0635 : bundle_64ff450e75_cubeCofacetCertificate (⟨635, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0636 : bundle_64ff450e75_cubeCofacetCertificate (⟨636, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0637 : bundle_64ff450e75_cubeCofacetCertificate (⟨637, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0638 : bundle_64ff450e75_cubeCofacetCertificate (⟨638, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0639 : bundle_64ff450e75_cubeCofacetCertificate (⟨639, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0640 : bundle_64ff450e75_cubeCofacetCertificate (⟨640, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0641 : bundle_64ff450e75_cubeCofacetCertificate (⟨641, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0642 : bundle_64ff450e75_cubeCofacetCertificate (⟨642, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0643 : bundle_64ff450e75_cubeCofacetCertificate (⟨643, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0644 : bundle_64ff450e75_cubeCofacetCertificate (⟨644, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0645 : bundle_64ff450e75_cubeCofacetCertificate (⟨645, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0646 : bundle_64ff450e75_cubeCofacetCertificate (⟨646, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0647 : bundle_64ff450e75_cubeCofacetCertificate (⟨647, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0648 : bundle_64ff450e75_cubeCofacetCertificate (⟨648, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0649 : bundle_64ff450e75_cubeCofacetCertificate (⟨649, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0650 : bundle_64ff450e75_cubeCofacetCertificate (⟨650, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0651 : bundle_64ff450e75_cubeCofacetCertificate (⟨651, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0652 : bundle_64ff450e75_cubeCofacetCertificate (⟨652, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0653 : bundle_64ff450e75_cubeCofacetCertificate (⟨653, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0654 : bundle_64ff450e75_cubeCofacetCertificate (⟨654, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0655 : bundle_64ff450e75_cubeCofacetCertificate (⟨655, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0656 : bundle_64ff450e75_cubeCofacetCertificate (⟨656, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0657 : bundle_64ff450e75_cubeCofacetCertificate (⟨657, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0658 : bundle_64ff450e75_cubeCofacetCertificate (⟨658, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0659 : bundle_64ff450e75_cubeCofacetCertificate (⟨659, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0660 : bundle_64ff450e75_cubeCofacetCertificate (⟨660, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0661 : bundle_64ff450e75_cubeCofacetCertificate (⟨661, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0662 : bundle_64ff450e75_cubeCofacetCertificate (⟨662, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0663 : bundle_64ff450e75_cubeCofacetCertificate (⟨663, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0664 : bundle_64ff450e75_cubeCofacetCertificate (⟨664, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0665 : bundle_64ff450e75_cubeCofacetCertificate (⟨665, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0666 : bundle_64ff450e75_cubeCofacetCertificate (⟨666, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0667 : bundle_64ff450e75_cubeCofacetCertificate (⟨667, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0668 : bundle_64ff450e75_cubeCofacetCertificate (⟨668, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0669 : bundle_64ff450e75_cubeCofacetCertificate (⟨669, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0670 : bundle_64ff450e75_cubeCofacetCertificate (⟨670, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0671 : bundle_64ff450e75_cubeCofacetCertificate (⟨671, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0672 : bundle_64ff450e75_cubeCofacetCertificate (⟨672, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0673 : bundle_64ff450e75_cubeCofacetCertificate (⟨673, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0674 : bundle_64ff450e75_cubeCofacetCertificate (⟨674, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0675 : bundle_64ff450e75_cubeCofacetCertificate (⟨675, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0676 : bundle_64ff450e75_cubeCofacetCertificate (⟨676, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0677 : bundle_64ff450e75_cubeCofacetCertificate (⟨677, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0678 : bundle_64ff450e75_cubeCofacetCertificate (⟨678, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0679 : bundle_64ff450e75_cubeCofacetCertificate (⟨679, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0680 : bundle_64ff450e75_cubeCofacetCertificate (⟨680, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0681 : bundle_64ff450e75_cubeCofacetCertificate (⟨681, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0682 : bundle_64ff450e75_cubeCofacetCertificate (⟨682, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0683 : bundle_64ff450e75_cubeCofacetCertificate (⟨683, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0684 : bundle_64ff450e75_cubeCofacetCertificate (⟨684, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0685 : bundle_64ff450e75_cubeCofacetCertificate (⟨685, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0686 : bundle_64ff450e75_cubeCofacetCertificate (⟨686, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0687 : bundle_64ff450e75_cubeCofacetCertificate (⟨687, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0688 : bundle_64ff450e75_cubeCofacetCertificate (⟨688, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0689 : bundle_64ff450e75_cubeCofacetCertificate (⟨689, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0690 : bundle_64ff450e75_cubeCofacetCertificate (⟨690, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0691 : bundle_64ff450e75_cubeCofacetCertificate (⟨691, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0692 : bundle_64ff450e75_cubeCofacetCertificate (⟨692, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0693 : bundle_64ff450e75_cubeCofacetCertificate (⟨693, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0694 : bundle_64ff450e75_cubeCofacetCertificate (⟨694, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0695 : bundle_64ff450e75_cubeCofacetCertificate (⟨695, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0696 : bundle_64ff450e75_cubeCofacetCertificate (⟨696, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0697 : bundle_64ff450e75_cubeCofacetCertificate (⟨697, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0698 : bundle_64ff450e75_cubeCofacetCertificate (⟨698, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0699 : bundle_64ff450e75_cubeCofacetCertificate (⟨699, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0700 : bundle_64ff450e75_cubeCofacetCertificate (⟨700, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0701 : bundle_64ff450e75_cubeCofacetCertificate (⟨701, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0702 : bundle_64ff450e75_cubeCofacetCertificate (⟨702, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0703 : bundle_64ff450e75_cubeCofacetCertificate (⟨703, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0704 : bundle_64ff450e75_cubeCofacetCertificate (⟨704, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0705 : bundle_64ff450e75_cubeCofacetCertificate (⟨705, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0706 : bundle_64ff450e75_cubeCofacetCertificate (⟨706, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0707 : bundle_64ff450e75_cubeCofacetCertificate (⟨707, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0708 : bundle_64ff450e75_cubeCofacetCertificate (⟨708, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0709 : bundle_64ff450e75_cubeCofacetCertificate (⟨709, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0710 : bundle_64ff450e75_cubeCofacetCertificate (⟨710, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0711 : bundle_64ff450e75_cubeCofacetCertificate (⟨711, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0712 : bundle_64ff450e75_cubeCofacetCertificate (⟨712, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0713 : bundle_64ff450e75_cubeCofacetCertificate (⟨713, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0714 : bundle_64ff450e75_cubeCofacetCertificate (⟨714, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0715 : bundle_64ff450e75_cubeCofacetCertificate (⟨715, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0716 : bundle_64ff450e75_cubeCofacetCertificate (⟨716, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0717 : bundle_64ff450e75_cubeCofacetCertificate (⟨717, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0718 : bundle_64ff450e75_cubeCofacetCertificate (⟨718, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0719 : bundle_64ff450e75_cubeCofacetCertificate (⟨719, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0720 : bundle_64ff450e75_cubeCofacetCertificate (⟨720, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0721 : bundle_64ff450e75_cubeCofacetCertificate (⟨721, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0722 : bundle_64ff450e75_cubeCofacetCertificate (⟨722, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0723 : bundle_64ff450e75_cubeCofacetCertificate (⟨723, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0724 : bundle_64ff450e75_cubeCofacetCertificate (⟨724, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0725 : bundle_64ff450e75_cubeCofacetCertificate (⟨725, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0726 : bundle_64ff450e75_cubeCofacetCertificate (⟨726, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0727 : bundle_64ff450e75_cubeCofacetCertificate (⟨727, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0728 : bundle_64ff450e75_cubeCofacetCertificate (⟨728, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0729 : bundle_64ff450e75_cubeCofacetCertificate (⟨729, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0730 : bundle_64ff450e75_cubeCofacetCertificate (⟨730, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0731 : bundle_64ff450e75_cubeCofacetCertificate (⟨731, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0732 : bundle_64ff450e75_cubeCofacetCertificate (⟨732, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0733 : bundle_64ff450e75_cubeCofacetCertificate (⟨733, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0734 : bundle_64ff450e75_cubeCofacetCertificate (⟨734, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0735 : bundle_64ff450e75_cubeCofacetCertificate (⟨735, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0736 : bundle_64ff450e75_cubeCofacetCertificate (⟨736, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0737 : bundle_64ff450e75_cubeCofacetCertificate (⟨737, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0738 : bundle_64ff450e75_cubeCofacetCertificate (⟨738, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0739 : bundle_64ff450e75_cubeCofacetCertificate (⟨739, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0740 : bundle_64ff450e75_cubeCofacetCertificate (⟨740, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0741 : bundle_64ff450e75_cubeCofacetCertificate (⟨741, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0742 : bundle_64ff450e75_cubeCofacetCertificate (⟨742, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0743 : bundle_64ff450e75_cubeCofacetCertificate (⟨743, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0744 : bundle_64ff450e75_cubeCofacetCertificate (⟨744, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0745 : bundle_64ff450e75_cubeCofacetCertificate (⟨745, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0746 : bundle_64ff450e75_cubeCofacetCertificate (⟨746, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0747 : bundle_64ff450e75_cubeCofacetCertificate (⟨747, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0748 : bundle_64ff450e75_cubeCofacetCertificate (⟨748, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0749 : bundle_64ff450e75_cubeCofacetCertificate (⟨749, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0750 : bundle_64ff450e75_cubeCofacetCertificate (⟨750, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0751 : bundle_64ff450e75_cubeCofacetCertificate (⟨751, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0752 : bundle_64ff450e75_cubeCofacetCertificate (⟨752, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0753 : bundle_64ff450e75_cubeCofacetCertificate (⟨753, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0754 : bundle_64ff450e75_cubeCofacetCertificate (⟨754, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0755 : bundle_64ff450e75_cubeCofacetCertificate (⟨755, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0756 : bundle_64ff450e75_cubeCofacetCertificate (⟨756, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0757 : bundle_64ff450e75_cubeCofacetCertificate (⟨757, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

end CubicalIndecomposability
end VerificationSource001



end -- global noncomputable section
end -- global public section
