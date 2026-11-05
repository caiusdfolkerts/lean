module
public import TerminalGeometry
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Papers.FiniteProjectionChecks

section
set_option debug.skipKernelTC false

section BundlePart0
/- Source: ProjectionCertificates/R_multi_six_0048.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0048

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_199 : Finset (Fin 10) := literalFinset [0, 1, 2, 6, 7] (by decide +kernel)
noncomputable def vertices_587 : Finset (Fin 10) := literalFinset [0, 1, 3, 6, 9] (by decide +kernel)
noncomputable def vertices_149 : Finset (Fin 10) := literalFinset [0, 2, 4, 7] (by decide +kernel)
noncomputable def vertices_809 : Finset (Fin 10) := literalFinset [0, 3, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_753 : Finset (Fin 10) := literalFinset [0, 4, 5, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_782 : Finset (Fin 10) := literalFinset [1, 2, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_838 : Finset (Fin 10) := literalFinset [1, 2, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_412 : Finset (Fin 10) := literalFinset [2, 3, 4, 7, 8] (by decide +kernel)
noncomputable def vertices_452 : Finset (Fin 10) := literalFinset [2, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_440 : Finset (Fin 10) := literalFinset [3, 4, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_992 : Finset (Fin 10) := literalFinset [5, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_67 : Finset (Fin 10) := literalFinset [0, 1, 6] (by decide +kernel)
noncomputable def vertices_21 : Finset (Fin 10) := literalFinset [0, 2, 4] (by decide +kernel)
noncomputable def vertices_133 : Finset (Fin 10) := literalFinset [0, 2, 7] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_521 : Finset (Fin 10) := literalFinset [0, 3, 9] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_145 : Finset (Fin 10) := literalFinset [0, 4, 7] (by decide +kernel)
noncomputable def vertices_545 : Finset (Fin 10) := literalFinset [0, 5, 9] (by decide +kernel)
noncomputable def vertices_193 : Finset (Fin 10) := literalFinset [0, 6, 7] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_70 : Finset (Fin 10) := literalFinset [1, 2, 6] (by decide +kernel)
noncomputable def vertices_774 : Finset (Fin 10) := literalFinset [1, 2, 8, 9] (by decide +kernel)
noncomputable def vertices_522 : Finset (Fin 10) := literalFinset [1, 3, 9] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_28 : Finset (Fin 10) := literalFinset [2, 3, 4] (by decide +kernel)
noncomputable def vertices_268 : Finset (Fin 10) := literalFinset [2, 3, 8] (by decide +kernel)
noncomputable def vertices_148 : Finset (Fin 10) := literalFinset [2, 4, 7] (by decide +kernel)
noncomputable def vertices_196 : Finset (Fin 10) := literalFinset [2, 6, 7] (by decide +kernel)
noncomputable def vertices_324 : Finset (Fin 10) := literalFinset [2, 6, 8] (by decide +kernel)
noncomputable def vertices_388 : Finset (Fin 10) := literalFinset [2, 7, 8] (by decide +kernel)
noncomputable def vertices_56 : Finset (Fin 10) := literalFinset [3, 4, 5] (by decide +kernel)
noncomputable def vertices_408 : Finset (Fin 10) := literalFinset [3, 4, 7, 8] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_776 : Finset (Fin 10) := literalFinset [3, 8, 9] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_736 : Finset (Fin 10) := literalFinset [5, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_587, vertices_149, vertices_809, vertices_753, vertices_782, vertices_838, vertices_412, vertices_452, vertices_440, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_133, vertices_41, vertices_521, vertices_49, vertices_145, vertices_545, vertices_193, vertices_577, vertices_14, vertices_70, vertices_774, vertices_522, vertices_578, vertices_28, vertices_268, vertices_148, vertices_196, vertices_324, vertices_388, vertices_56, vertices_408, vertices_296, vertices_776, vertices_176, vertices_736, vertices_416, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_587), (false, vertices_149), (false, vertices_809), (false, vertices_753), (true, vertices_774), (true, vertices_268), (true, vertices_324), (true, vertices_388), (true, vertices_408), (true, vertices_416), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 16, 9, 7, 17, 19, 20, 21, 22]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 10 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_587) then 11 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_809) then 12 else
  if p.val = (false, vertices_753) then 18 else
  if p.val = (true, vertices_774) then 15 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_324) then 2 else
  if p.val = (true, vertices_388) then 3 else
  if p.val = (true, vertices_408) then 8 else
  if p.val = (true, vertices_416) then 4 else
  if p.val = (true, vertices_448) then 5 else
  if p.val = (true, vertices_832) then 6 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 7 => Sum.inl 3
  | 8 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
  | 9 => Sum.inl 2
  | 10 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inl 4
  | 18 => Sum.inr ⟨(false, vertices_753), by decide +kernel⟩
  | 19 => Sum.inl 5
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 3
  frame := ![4, 5, 6]
  vertex := 8
  face := Sum.inr ⟨vertices_736, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_736, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 3
  frame := ![2, 3, 6]
  vertex := 7
  face := Sum.inr ⟨vertices_408, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_408, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 3
  frame := ![0, 1, 7]
  vertex := 8
  face := Sum.inr ⟨vertices_774, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_774, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 3 → HeightRow boundary := ![row0, row1, row2]
noncomputable def pivot : Fin 3 → Fin 9 := ![4, 2, 0]
noncomputable def heightProof : HeightCertificate boundary 3 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_782, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_782, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_838, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_70, (by decide +kernel)⟩ ⟨vertices_838, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_412, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![1, 2, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_28, (by decide +kernel)⟩ ⟨vertices_412, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_452, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![1, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_196, (by decide +kernel)⟩ ⟨vertices_452, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_440, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![2, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_440, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_992, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![4, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_736, (by decide +kernel)⟩ ⟨vertices_992, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coveringFacets : Fin 6 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5]
noncomputable def coveringProof (j : Fin 6) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (fun i => Fin.elim0 i))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 3 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 6, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0048

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_multi_six_0049.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0049

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_199 : Finset (Fin 10) := literalFinset [0, 1, 2, 6, 7] (by decide +kernel)
noncomputable def vertices_331 : Finset (Fin 10) := literalFinset [0, 1, 3, 6, 8] (by decide +kernel)
noncomputable def vertices_397 : Finset (Fin 10) := literalFinset [0, 2, 3, 7, 8] (by decide +kernel)
noncomputable def vertices_961 : Finset (Fin 10) := literalFinset [0, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_86 : Finset (Fin 10) := literalFinset [1, 2, 4, 6] (by decide +kernel)
noncomputable def vertices_858 : Finset (Fin 10) := literalFinset [1, 3, 4, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_172 : Finset (Fin 10) := literalFinset [2, 3, 5, 7] (by decide +kernel)
noncomputable def vertices_628 : Finset (Fin 10) := literalFinset [2, 4, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_740 : Finset (Fin 10) := literalFinset [2, 5, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_440 : Finset (Fin 10) := literalFinset [3, 4, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_944 : Finset (Fin 10) := literalFinset [4, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_67 : Finset (Fin 10) := literalFinset [0, 1, 6] (by decide +kernel)
noncomputable def vertices_13 : Finset (Fin 10) := literalFinset [0, 2, 3] (by decide +kernel)
noncomputable def vertices_133 : Finset (Fin 10) := literalFinset [0, 2, 7] (by decide +kernel)
noncomputable def vertices_265 : Finset (Fin 10) := literalFinset [0, 3, 8] (by decide +kernel)
noncomputable def vertices_193 : Finset (Fin 10) := literalFinset [0, 6, 7] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_385 : Finset (Fin 10) := literalFinset [0, 7, 8] (by decide +kernel)
noncomputable def vertices_22 : Finset (Fin 10) := literalFinset [1, 2, 4] (by decide +kernel)
noncomputable def vertices_70 : Finset (Fin 10) := literalFinset [1, 2, 6] (by decide +kernel)
noncomputable def vertices_26 : Finset (Fin 10) := literalFinset [1, 3, 4] (by decide +kernel)
noncomputable def vertices_330 : Finset (Fin 10) := literalFinset [1, 3, 6, 8] (by decide +kernel)
noncomputable def vertices_82 : Finset (Fin 10) := literalFinset [1, 4, 6] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_140 : Finset (Fin 10) := literalFinset [2, 3, 7] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_612 : Finset (Fin 10) := literalFinset [2, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_164 : Finset (Fin 10) := literalFinset [2, 5, 7] (by decide +kernel)
noncomputable def vertices_196 : Finset (Fin 10) := literalFinset [2, 6, 7] (by decide +kernel)
noncomputable def vertices_56 : Finset (Fin 10) := literalFinset [3, 4, 5] (by decide +kernel)
noncomputable def vertices_280 : Finset (Fin 10) := literalFinset [3, 4, 8] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_392 : Finset (Fin 10) := literalFinset [3, 7, 8] (by decide +kernel)
noncomputable def vertices_432 : Finset (Fin 10) := literalFinset [4, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_784 : Finset (Fin 10) := literalFinset [4, 8, 9] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_397, vertices_961, vertices_86, vertices_858, vertices_172, vertices_628, vertices_740, vertices_440, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_330, vertices_82, vertices_44, vertices_140, vertices_52, vertices_84, vertices_612, vertices_164, vertices_196, vertices_56, vertices_280, vertices_168, vertices_392, vertices_432, vertices_560, vertices_592, vertices_784, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_84), (true, vertices_612), (true, vertices_164), (true, vertices_280), (true, vertices_168), (true, vertices_432), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![9, 12, 16, 17, 19, 20, 22, 23, 24]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_199) then 10 else
  if p.val = (false, vertices_331) then 11 else
  if p.val = (false, vertices_397) then 14 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_612) then 15 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_280) then 3 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_432) then 18 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_592) then 6 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_672) then 8 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_612), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(true, vertices_432), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 3
  frame := ![1, 4, 5]
  vertex := 8
  face := Sum.inr ⟨vertices_612, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_612, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 3
  frame := ![3, 4, 6]
  vertex := 7
  face := Sum.inr ⟨vertices_432, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_432, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 5]
  vertex := 7
  face := Sum.inl ⟨vertices_858, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_26, (by decide +kernel)⟩ ⟨vertices_858, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 5]
  vertex := 8
  face := Sum.inl ⟨vertices_858, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_26, (by decide +kernel)⟩ ⟨vertices_858, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![1, 4, 7, 0]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_86, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .fundamental ![0, 1, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_86, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_858, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_26, (by decide +kernel)⟩ ⟨vertices_858, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_172, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![1, 2, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_172, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_628, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_628, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_740, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![1, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_612, (by decide +kernel)⟩ ⟨vertices_740, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_440, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![2, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_440, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_944, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![3, 4, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_432, (by decide +kernel)⟩ ⟨vertices_944, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coveringFacets : Fin 7 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6]
noncomputable def coveringProof (j : Fin 7) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (fun i => Fin.elim0 i)))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 7, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0049

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_multi_six_0050.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0050

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_199 : Finset (Fin 10) := literalFinset [0, 1, 2, 6, 7] (by decide +kernel)
noncomputable def vertices_651 : Finset (Fin 10) := literalFinset [0, 1, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_341 : Finset (Fin 10) := literalFinset [0, 2, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_233 : Finset (Fin 10) := literalFinset [0, 3, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_369 : Finset (Fin 10) := literalFinset [0, 4, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_782 : Finset (Fin 10) := literalFinset [1, 2, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_838 : Finset (Fin 10) := literalFinset [1, 2, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_706 : Finset (Fin 10) := literalFinset [1, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_284 : Finset (Fin 10) := literalFinset [2, 3, 4, 8] (by decide +kernel)
noncomputable def vertices_952 : Finset (Fin 10) := literalFinset [3, 4, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_992 : Finset (Fin 10) := literalFinset [5, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_131 : Finset (Fin 10) := literalFinset [0, 1, 7] (by decide +kernel)
noncomputable def vertices_21 : Finset (Fin 10) := literalFinset [0, 2, 4] (by decide +kernel)
noncomputable def vertices_69 : Finset (Fin 10) := literalFinset [0, 2, 6] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_337 : Finset (Fin 10) := literalFinset [0, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_97 : Finset (Fin 10) := literalFinset [0, 5, 6] (by decide +kernel)
noncomputable def vertices_193 : Finset (Fin 10) := literalFinset [0, 6, 7] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_70 : Finset (Fin 10) := literalFinset [1, 2, 6] (by decide +kernel)
noncomputable def vertices_774 : Finset (Fin 10) := literalFinset [1, 2, 8, 9] (by decide +kernel)
noncomputable def vertices_522 : Finset (Fin 10) := literalFinset [1, 3, 9] (by decide +kernel)
noncomputable def vertices_194 : Finset (Fin 10) := literalFinset [1, 6, 7] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_28 : Finset (Fin 10) := literalFinset [2, 3, 4] (by decide +kernel)
noncomputable def vertices_268 : Finset (Fin 10) := literalFinset [2, 3, 8] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_324 : Finset (Fin 10) := literalFinset [2, 6, 8] (by decide +kernel)
noncomputable def vertices_56 : Finset (Fin 10) := literalFinset [3, 4, 5] (by decide +kernel)
noncomputable def vertices_280 : Finset (Fin 10) := literalFinset [3, 4, 8] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_648 : Finset (Fin 10) := literalFinset [3, 7, 9] (by decide +kernel)
noncomputable def vertices_776 : Finset (Fin 10) := literalFinset [3, 8, 9] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_224 : Finset (Fin 10) := literalFinset [5, 6, 7] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_928 : Finset (Fin 10) := literalFinset [5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_651, vertices_341, vertices_233, vertices_369, vertices_782, vertices_838, vertices_706, vertices_284, vertices_952, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_69, vertices_41, vertices_137, vertices_49, vertices_337, vertices_97, vertices_193, vertices_14, vertices_70, vertices_774, vertices_522, vertices_194, vertices_578, vertices_642, vertices_28, vertices_268, vertices_276, vertices_324, vertices_56, vertices_280, vertices_168, vertices_648, vertices_776, vertices_304, vertices_224, vertices_352, vertices_928, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_651), (false, vertices_341), (false, vertices_233), (false, vertices_369), (true, vertices_774), (true, vertices_578), (true, vertices_268), (true, vertices_280), (true, vertices_776), (true, vertices_928), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 16, 6, 9, 17, 19, 20, 21, 22]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 10 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_651) then 7 else
  if p.val = (false, vertices_341) then 11 else
  if p.val = (false, vertices_233) then 8 else
  if p.val = (false, vertices_369) then 12 else
  if p.val = (true, vertices_774) then 15 else
  if p.val = (true, vertices_578) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_280) then 2 else
  if p.val = (true, vertices_776) then 3 else
  if p.val = (true, vertices_928) then 18 else
  if p.val = (true, vertices_704) then 4 else
  if p.val = (true, vertices_832) then 5 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 6 => Sum.inl 2
  | 7 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 8 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 9 => Sum.inl 3
  | 10 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inl 4
  | 18 => Sum.inr ⟨(true, vertices_928), by decide +kernel⟩
  | 19 => Sum.inl 5
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 3
  frame := ![0, 1, 7]
  vertex := 8
  face := Sum.inr ⟨vertices_774, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_774, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![2, 3, 4, 6]
  vertex := 7
  face := Sum.inl ⟨vertices_952, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_952, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![2, 3, 4, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_952, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_952, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 3 → HeightRow boundary := ![row0, row1, row2]
noncomputable def pivot : Fin 3 → Fin 9 := ![0, 7, 2]
noncomputable def heightProof : HeightCertificate boundary 3 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_782, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_782, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_838, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_70, (by decide +kernel)⟩ ⟨vertices_838, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_706, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 5, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_194, (by decide +kernel)⟩ ⟨vertices_706, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_284, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![1, 2, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_28, (by decide +kernel)⟩ ⟨vertices_284, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_952, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![2, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_952, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_992, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fromLargerFacet ![4, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_224, (by decide +kernel)⟩ ⟨vertices_992, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_928, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_952, by decide +kernel⟩ ![2, 3, 4, 6]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_952, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def coveringFacets : Fin 6 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5]
noncomputable def coveringProof (j : Fin 6) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (fun i => Fin.elim0 i))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 3 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 6, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0050

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_multi_six_0054.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0054

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_583 : Finset (Fin 10) := literalFinset [0, 1, 2, 6, 9] (by decide +kernel)
noncomputable def vertices_331 : Finset (Fin 10) := literalFinset [0, 1, 3, 6, 8] (by decide +kernel)
noncomputable def vertices_781 : Finset (Fin 10) := literalFinset [0, 2, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_961 : Finset (Fin 10) := literalFinset [0, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_214 : Finset (Fin 10) := literalFinset [1, 2, 4, 6, 7] (by decide +kernel)
noncomputable def vertices_250 : Finset (Fin 10) := literalFinset [1, 3, 4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_300 : Finset (Fin 10) := literalFinset [2, 3, 5, 8] (by decide +kernel)
noncomputable def vertices_820 : Finset (Fin 10) := literalFinset [2, 4, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_660 : Finset (Fin 10) := literalFinset [2, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_708 : Finset (Fin 10) := literalFinset [2, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_488 : Finset (Fin 10) := literalFinset [3, 5, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_944 : Finset (Fin 10) := literalFinset [4, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_67 : Finset (Fin 10) := literalFinset [0, 1, 6] (by decide +kernel)
noncomputable def vertices_13 : Finset (Fin 10) := literalFinset [0, 2, 3] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_265 : Finset (Fin 10) := literalFinset [0, 3, 8] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_22 : Finset (Fin 10) := literalFinset [1, 2, 4] (by decide +kernel)
noncomputable def vertices_70 : Finset (Fin 10) := literalFinset [1, 2, 6] (by decide +kernel)
noncomputable def vertices_58 : Finset (Fin 10) := literalFinset [1, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_74 : Finset (Fin 10) := literalFinset [1, 3, 6] (by decide +kernel)
noncomputable def vertices_210 : Finset (Fin 10) := literalFinset [1, 4, 6, 7] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_268 : Finset (Fin 10) := literalFinset [2, 3, 8] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_148 : Finset (Fin 10) := literalFinset [2, 4, 7] (by decide +kernel)
noncomputable def vertices_532 : Finset (Fin 10) := literalFinset [2, 4, 9] (by decide +kernel)
noncomputable def vertices_292 : Finset (Fin 10) := literalFinset [2, 5, 8] (by decide +kernel)
noncomputable def vertices_196 : Finset (Fin 10) := literalFinset [2, 6, 7] (by decide +kernel)
noncomputable def vertices_580 : Finset (Fin 10) := literalFinset [2, 6, 9] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_232 : Finset (Fin 10) := literalFinset [3, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_328 : Finset (Fin 10) := literalFinset [3, 6, 8] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_816 : Finset (Fin 10) := literalFinset [4, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_331, vertices_781, vertices_961, vertices_214, vertices_250, vertices_300, vertices_820, vertices_660, vertices_708, vertices_488, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_517, vertices_265, vertices_321, vertices_577, vertices_769, vertices_22, vertices_70, vertices_58, vertices_74, vertices_210, vertices_44, vertices_268, vertices_52, vertices_148, vertices_532, vertices_292, vertices_196, vertices_580, vertices_644, vertices_772, vertices_232, vertices_296, vertices_328, vertices_176, vertices_816, vertices_656, vertices_416, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_331), (false, vertices_781), (false, vertices_961), (true, vertices_210), (true, vertices_148), (true, vertices_532), (true, vertices_292), (true, vertices_196), (true, vertices_644), (true, vertices_232), (true, vertices_296), (true, vertices_176), (true, vertices_816), (true, vertices_656), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![12, 9, 16, 18, 20, 21, 23, 24, 25]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_583) then 10 else
  if p.val = (false, vertices_331) then 14 else
  if p.val = (false, vertices_781) then 11 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_210) then 15 else
  if p.val = (true, vertices_148) then 0 else
  if p.val = (true, vertices_532) then 1 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_196) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_232) then 17 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_816) then 19 else
  if p.val = (true, vertices_656) then 7 else
  if p.val = (true, vertices_416) then 8 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_210), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(true, vertices_232), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 3
  frame := ![3, 4, 7]
  vertex := 8
  face := Sum.inr ⟨vertices_816, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_816, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 5]
  vertex := 4
  face := Sum.inl ⟨vertices_250, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 5]
  vertex := 6
  face := Sum.inl ⟨vertices_250, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 3 → HeightRow boundary := ![row0, row1, row2]
noncomputable def pivot : Fin 3 → Fin 9 := ![7, 4, 0]
noncomputable def heightProof : HeightCertificate boundary 3 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_214, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .fromLargerFacet ![0, 1, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_214, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_210, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_250, by decide +kernel⟩ ![0, 2, 3, 5]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_250, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_300, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![1, 2, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_300, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_820, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 3, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_820, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_660, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![1, 3, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_148, (by decide +kernel)⟩ ⟨vertices_660, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_708, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![1, 5, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_196, (by decide +kernel)⟩ ⟨vertices_708, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_488, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fromLargerFacet ![2, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_232, (by decide +kernel)⟩ ⟨vertices_488, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_232, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_250, by decide +kernel⟩ ![0, 2, 3, 5]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_944, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .oneRow ![3, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_176, (by decide +kernel)⟩ ⟨vertices_944, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coveringFacets : Fin 8 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6, coverFacet7]
noncomputable def coveringProof (j : Fin 8) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (Fin.cases cover7 (fun i => Fin.elim0 i))))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 3 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 8, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0054

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_multi_six_0055.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0055

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_583 : Finset (Fin 10) := literalFinset [0, 1, 2, 6, 9] (by decide +kernel)
noncomputable def vertices_331 : Finset (Fin 10) := literalFinset [0, 1, 3, 6, 8] (by decide +kernel)
noncomputable def vertices_781 : Finset (Fin 10) := literalFinset [0, 2, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_961 : Finset (Fin 10) := literalFinset [0, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_214 : Finset (Fin 10) := literalFinset [1, 2, 4, 6, 7] (by decide +kernel)
noncomputable def vertices_250 : Finset (Fin 10) := literalFinset [1, 3, 4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_812 : Finset (Fin 10) := literalFinset [2, 3, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_564 : Finset (Fin 10) := literalFinset [2, 4, 5, 9] (by decide +kernel)
noncomputable def vertices_660 : Finset (Fin 10) := literalFinset [2, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_708 : Finset (Fin 10) := literalFinset [2, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_488 : Finset (Fin 10) := literalFinset [3, 5, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_944 : Finset (Fin 10) := literalFinset [4, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_67 : Finset (Fin 10) := literalFinset [0, 1, 6] (by decide +kernel)
noncomputable def vertices_13 : Finset (Fin 10) := literalFinset [0, 2, 3] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_265 : Finset (Fin 10) := literalFinset [0, 3, 8] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_22 : Finset (Fin 10) := literalFinset [1, 2, 4] (by decide +kernel)
noncomputable def vertices_70 : Finset (Fin 10) := literalFinset [1, 2, 6] (by decide +kernel)
noncomputable def vertices_58 : Finset (Fin 10) := literalFinset [1, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_74 : Finset (Fin 10) := literalFinset [1, 3, 6] (by decide +kernel)
noncomputable def vertices_210 : Finset (Fin 10) := literalFinset [1, 4, 6, 7] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_780 : Finset (Fin 10) := literalFinset [2, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_148 : Finset (Fin 10) := literalFinset [2, 4, 7] (by decide +kernel)
noncomputable def vertices_532 : Finset (Fin 10) := literalFinset [2, 4, 9] (by decide +kernel)
noncomputable def vertices_548 : Finset (Fin 10) := literalFinset [2, 5, 9] (by decide +kernel)
noncomputable def vertices_196 : Finset (Fin 10) := literalFinset [2, 6, 7] (by decide +kernel)
noncomputable def vertices_580 : Finset (Fin 10) := literalFinset [2, 6, 9] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_232 : Finset (Fin 10) := literalFinset [3, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_328 : Finset (Fin 10) := literalFinset [3, 6, 8] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_331, vertices_781, vertices_961, vertices_214, vertices_250, vertices_812, vertices_564, vertices_660, vertices_708, vertices_488, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_517, vertices_265, vertices_321, vertices_577, vertices_769, vertices_22, vertices_70, vertices_58, vertices_74, vertices_210, vertices_44, vertices_780, vertices_52, vertices_148, vertices_532, vertices_548, vertices_196, vertices_580, vertices_644, vertices_232, vertices_296, vertices_328, vertices_176, vertices_560, vertices_656, vertices_416, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_331), (false, vertices_781), (false, vertices_961), (true, vertices_210), (true, vertices_148), (true, vertices_532), (true, vertices_548), (true, vertices_196), (true, vertices_644), (true, vertices_232), (true, vertices_296), (true, vertices_176), (true, vertices_560), (true, vertices_656), (true, vertices_416), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![14, 11, 18, 20, 21, 22, 24, 25, 26]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_583) then 12 else
  if p.val = (false, vertices_331) then 16 else
  if p.val = (false, vertices_781) then 13 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_210) then 17 else
  if p.val = (true, vertices_148) then 0 else
  if p.val = (true, vertices_532) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_196) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_232) then 19 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_656) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_210), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(true, vertices_232), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 3
  frame := ![1, 2, 7]
  vertex := 8
  face := Sum.inr ⟨vertices_780, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_780, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![3, 4, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_944, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_176, (by decide +kernel)⟩ ⟨vertices_944, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 5]
  vertex := 4
  face := Sum.inl ⟨vertices_250, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 5]
  vertex := 6
  face := Sum.inl ⟨vertices_250, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![1, 7, 4, 0]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_214, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .fromLargerFacet ![0, 1, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_214, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_210, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_250, by decide +kernel⟩ ![0, 2, 3, 5]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_250, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_812, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![1, 2, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_812, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_564, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![1, 3, 4, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_564, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_660, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![1, 3, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_148, (by decide +kernel)⟩ ⟨vertices_660, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_708, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![1, 5, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_196, (by decide +kernel)⟩ ⟨vertices_708, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_488, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fromLargerFacet ![2, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_232, (by decide +kernel)⟩ ⟨vertices_488, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_232, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_250, by decide +kernel⟩ ![0, 2, 3, 5]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_944, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .oneRow ![3, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_176, (by decide +kernel)⟩ ⟨vertices_944, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coveringFacets : Fin 8 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6, coverFacet7]
noncomputable def coveringProof (j : Fin 8) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (Fin.cases cover7 (fun i => Fin.elim0 i))))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 8, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0055

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_multi_six_0056.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0056

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_519 : Finset (Fin 10) := literalFinset [0, 1, 2, 9] (by decide +kernel)
noncomputable def vertices_331 : Finset (Fin 10) := literalFinset [0, 1, 3, 6, 8] (by decide +kernel)
noncomputable def vertices_771 : Finset (Fin 10) := literalFinset [0, 1, 8, 9] (by decide +kernel)
noncomputable def vertices_589 : Finset (Fin 10) := literalFinset [0, 2, 3, 6, 9] (by decide +kernel)
noncomputable def vertices_961 : Finset (Fin 10) := literalFinset [0, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_790 : Finset (Fin 10) := literalFinset [1, 2, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_250 : Finset (Fin 10) := literalFinset [1, 3, 4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_466 : Finset (Fin 10) := literalFinset [1, 4, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_556 : Finset (Fin 10) := literalFinset [2, 3, 5, 9] (by decide +kernel)
noncomputable def vertices_436 : Finset (Fin 10) := literalFinset [2, 4, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_932 : Finset (Fin 10) := literalFinset [2, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_744 : Finset (Fin 10) := literalFinset [3, 5, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_259 : Finset (Fin 10) := literalFinset [0, 1, 8] (by decide +kernel)
noncomputable def vertices_515 : Finset (Fin 10) := literalFinset [0, 1, 9] (by decide +kernel)
noncomputable def vertices_13 : Finset (Fin 10) := literalFinset [0, 2, 3] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_73 : Finset (Fin 10) := literalFinset [0, 3, 6] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_22 : Finset (Fin 10) := literalFinset [1, 2, 4] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_58 : Finset (Fin 10) := literalFinset [1, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_74 : Finset (Fin 10) := literalFinset [1, 3, 6] (by decide +kernel)
noncomputable def vertices_210 : Finset (Fin 10) := literalFinset [1, 4, 6, 7] (by decide +kernel)
noncomputable def vertices_274 : Finset (Fin 10) := literalFinset [1, 4, 8] (by decide +kernel)
noncomputable def vertices_322 : Finset (Fin 10) := literalFinset [1, 6, 8] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_420 : Finset (Fin 10) := literalFinset [2, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_548 : Finset (Fin 10) := literalFinset [2, 5, 9] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_232 : Finset (Fin 10) := literalFinset [3, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_552 : Finset (Fin 10) := literalFinset [3, 5, 9] (by decide +kernel)
noncomputable def vertices_584 : Finset (Fin 10) := literalFinset [3, 6, 9] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_331, vertices_771, vertices_589, vertices_961, vertices_790, vertices_250, vertices_466, vertices_556, vertices_436, vertices_932, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_515, vertices_13, vertices_517, vertices_73, vertices_321, vertices_577, vertices_769, vertices_22, vertices_518, vertices_58, vertices_74, vertices_210, vertices_274, vertices_322, vertices_770, vertices_44, vertices_524, vertices_52, vertices_276, vertices_420, vertices_548, vertices_772, vertices_232, vertices_552, vertices_584, vertices_176, vertices_400, vertices_672, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_331), (false, vertices_771), (false, vertices_589), (false, vertices_961), (true, vertices_210), (true, vertices_274), (true, vertices_276), (true, vertices_420), (true, vertices_548), (true, vertices_772), (true, vertices_232), (true, vertices_552), (true, vertices_176), (true, vertices_400), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![10, 13, 17, 19, 20, 21, 23, 24, 25]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_331) then 11 else
  if p.val = (false, vertices_771) then 1 else
  if p.val = (false, vertices_589) then 15 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_210) then 12 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_420) then 16 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_232) then 18 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_672) then 9 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_210), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_420), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(true, vertices_232), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 3, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_790, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_790, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 3
  frame := ![1, 4, 6]
  vertex := 7
  face := Sum.inr ⟨vertices_420, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_420, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 5]
  vertex := 4
  face := Sum.inl ⟨vertices_250, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 5]
  vertex := 6
  face := Sum.inl ⟨vertices_250, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![8, 1, 4, 0]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_790, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_790, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_250, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_466, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fromLargerFacet ![0, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_210, (by decide +kernel)⟩ ⟨vertices_466, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_210, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_250, by decide +kernel⟩ ![0, 2, 3, 5]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_556, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![1, 2, 4, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_556, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_436, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![1, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_436, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_932, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![1, 4, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_420, (by decide +kernel)⟩ ⟨vertices_932, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_744, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fromLargerFacet ![2, 4, 5, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_232, (by decide +kernel)⟩ ⟨vertices_744, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_232, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_250, by decide +kernel⟩ ![0, 2, 3, 5]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def coveringFacets : Fin 7 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6]
noncomputable def coveringProof (j : Fin 7) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (fun i => Fin.elim0 i)))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 7, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0056

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_multi_six_0057.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0057

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_583 : Finset (Fin 10) := literalFinset [0, 1, 2, 6, 9] (by decide +kernel)
noncomputable def vertices_203 : Finset (Fin 10) := literalFinset [0, 1, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_653 : Finset (Fin 10) := literalFinset [0, 2, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_961 : Finset (Fin 10) := literalFinset [0, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_790 : Finset (Fin 10) := literalFinset [1, 2, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_250 : Finset (Fin 10) := literalFinset [1, 3, 4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_850 : Finset (Fin 10) := literalFinset [1, 4, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_812 : Finset (Fin 10) := literalFinset [2, 3, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_308 : Finset (Fin 10) := literalFinset [2, 4, 5, 8] (by decide +kernel)
noncomputable def vertices_424 : Finset (Fin 10) := literalFinset [3, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_904 : Finset (Fin 10) := literalFinset [3, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_496 : Finset (Fin 10) := literalFinset [4, 5, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_67 : Finset (Fin 10) := literalFinset [0, 1, 6] (by decide +kernel)
noncomputable def vertices_13 : Finset (Fin 10) := literalFinset [0, 2, 3] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_193 : Finset (Fin 10) := literalFinset [0, 6, 7] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_22 : Finset (Fin 10) := literalFinset [1, 2, 4] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_58 : Finset (Fin 10) := literalFinset [1, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_202 : Finset (Fin 10) := literalFinset [1, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_82 : Finset (Fin 10) := literalFinset [1, 4, 6] (by decide +kernel)
noncomputable def vertices_786 : Finset (Fin 10) := literalFinset [1, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_292 : Finset (Fin 10) := literalFinset [2, 5, 8] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_392 : Finset (Fin 10) := literalFinset [3, 7, 8] (by decide +kernel)
noncomputable def vertices_648 : Finset (Fin 10) := literalFinset [3, 7, 9] (by decide +kernel)
noncomputable def vertices_776 : Finset (Fin 10) := literalFinset [3, 8, 9] (by decide +kernel)
noncomputable def vertices_240 : Finset (Fin 10) := literalFinset [4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_203, vertices_653, vertices_961, vertices_790, vertices_250, vertices_850, vertices_812, vertices_308, vertices_424, vertices_904, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_517, vertices_137, vertices_193, vertices_577, vertices_641, vertices_22, vertices_518, vertices_58, vertices_202, vertices_82, vertices_786, vertices_578, vertices_44, vertices_524, vertices_52, vertices_276, vertices_292, vertices_772, vertices_168, vertices_296, vertices_392, vertices_648, vertices_776, vertices_240, vertices_304, vertices_336, vertices_416, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_203), (false, vertices_653), (false, vertices_961), (true, vertices_82), (true, vertices_786), (true, vertices_276), (true, vertices_292), (true, vertices_772), (true, vertices_168), (true, vertices_296), (true, vertices_392), (true, vertices_776), (true, vertices_240), (true, vertices_304), (true, vertices_336), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![14, 11, 18, 19, 21, 22, 24, 25, 26]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_583) then 12 else
  if p.val = (false, vertices_203) then 16 else
  if p.val = (false, vertices_653) then 13 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_786) then 17 else
  if p.val = (true, vertices_276) then 1 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_772) then 3 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_240) then 20 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_416) then 10 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_786), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 5]
  vertex := 6
  face := Sum.inl ⟨vertices_250, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 4, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_812, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_812, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 3
  frame := ![0, 3, 7]
  vertex := 8
  face := Sum.inr ⟨vertices_786, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_786, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 5]
  vertex := 4
  face := Sum.inl ⟨vertices_250, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![6, 1, 7, 0]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_790, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_790, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_250, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_850, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_82, (by decide +kernel)⟩ ⟨vertices_850, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_812, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 2, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_812, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_308, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![1, 3, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_308, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_424, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![2, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_168, (by decide +kernel)⟩ ⟨vertices_424, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_904, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![2, 6, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_392, (by decide +kernel)⟩ ⟨vertices_904, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_496, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fromLargerFacet ![3, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_240, (by decide +kernel)⟩ ⟨vertices_496, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_240, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_250, by decide +kernel⟩ ![0, 2, 3, 5]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def coveringFacets : Fin 8 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6, coverFacet7]
noncomputable def coveringProof (j : Fin 8) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (Fin.cases cover7 (fun i => Fin.elim0 i))))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 8, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0057

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_multi_six_0058.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0058

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_583 : Finset (Fin 10) := literalFinset [0, 1, 2, 6, 9] (by decide +kernel)
noncomputable def vertices_203 : Finset (Fin 10) := literalFinset [0, 1, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_653 : Finset (Fin 10) := literalFinset [0, 2, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_961 : Finset (Fin 10) := literalFinset [0, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_790 : Finset (Fin 10) := literalFinset [1, 2, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_250 : Finset (Fin 10) := literalFinset [1, 3, 4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_850 : Finset (Fin 10) := literalFinset [1, 4, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_812 : Finset (Fin 10) := literalFinset [2, 3, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_308 : Finset (Fin 10) := literalFinset [2, 4, 5, 8] (by decide +kernel)
noncomputable def vertices_680 : Finset (Fin 10) := literalFinset [3, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_496 : Finset (Fin 10) := literalFinset [4, 5, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_928 : Finset (Fin 10) := literalFinset [5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_67 : Finset (Fin 10) := literalFinset [0, 1, 6] (by decide +kernel)
noncomputable def vertices_13 : Finset (Fin 10) := literalFinset [0, 2, 3] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_193 : Finset (Fin 10) := literalFinset [0, 6, 7] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_22 : Finset (Fin 10) := literalFinset [1, 2, 4] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_58 : Finset (Fin 10) := literalFinset [1, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_202 : Finset (Fin 10) := literalFinset [1, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_82 : Finset (Fin 10) := literalFinset [1, 4, 6] (by decide +kernel)
noncomputable def vertices_786 : Finset (Fin 10) := literalFinset [1, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_292 : Finset (Fin 10) := literalFinset [2, 5, 8] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_552 : Finset (Fin 10) := literalFinset [3, 5, 9] (by decide +kernel)
noncomputable def vertices_648 : Finset (Fin 10) := literalFinset [3, 7, 9] (by decide +kernel)
noncomputable def vertices_240 : Finset (Fin 10) := literalFinset [4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_203, vertices_653, vertices_961, vertices_790, vertices_250, vertices_850, vertices_812, vertices_308, vertices_680, vertices_496, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_517, vertices_137, vertices_193, vertices_577, vertices_641, vertices_22, vertices_518, vertices_58, vertices_202, vertices_82, vertices_786, vertices_578, vertices_44, vertices_524, vertices_52, vertices_276, vertices_292, vertices_772, vertices_168, vertices_552, vertices_648, vertices_240, vertices_304, vertices_336, vertices_416, vertices_672, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_203), (false, vertices_653), (false, vertices_961), (true, vertices_82), (true, vertices_786), (true, vertices_276), (true, vertices_292), (true, vertices_772), (true, vertices_168), (true, vertices_552), (true, vertices_240), (true, vertices_304), (true, vertices_336), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![14, 11, 18, 19, 21, 22, 24, 25, 26]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_583) then 12 else
  if p.val = (false, vertices_203) then 16 else
  if p.val = (false, vertices_653) then 13 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_786) then 17 else
  if p.val = (true, vertices_276) then 1 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_772) then 3 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_240) then 20 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_786), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 5]
  vertex := 6
  face := Sum.inl ⟨vertices_250, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 4, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_812, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_812, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 3
  frame := ![0, 3, 7]
  vertex := 8
  face := Sum.inr ⟨vertices_786, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_786, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 5]
  vertex := 4
  face := Sum.inl ⟨vertices_250, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![6, 1, 7, 0]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_790, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_790, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_250, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_850, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_82, (by decide +kernel)⟩ ⟨vertices_850, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_812, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 2, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_812, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_308, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![1, 3, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_308, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_680, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![2, 4, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_168, (by decide +kernel)⟩ ⟨vertices_680, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_496, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fromLargerFacet ![3, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_240, (by decide +kernel)⟩ ⟨vertices_496, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_240, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_250, by decide +kernel⟩ ![0, 2, 3, 5]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_928, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![4, 6, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_416, (by decide +kernel)⟩ ⟨vertices_928, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coveringFacets : Fin 8 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6, coverFacet7]
noncomputable def coveringProof (j : Fin 8) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (Fin.cases cover7 (fun i => Fin.elim0 i))))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 8, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0058

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_multi_six_0059.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0059

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_583 : Finset (Fin 10) := literalFinset [0, 1, 2, 6, 9] (by decide +kernel)
noncomputable def vertices_203 : Finset (Fin 10) := literalFinset [0, 1, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_789 : Finset (Fin 10) := literalFinset [0, 2, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_249 : Finset (Fin 10) := literalFinset [0, 3, 4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_849 : Finset (Fin 10) := literalFinset [0, 4, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_654 : Finset (Fin 10) := literalFinset [1, 2, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_962 : Finset (Fin 10) := literalFinset [1, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_556 : Finset (Fin 10) := literalFinset [2, 3, 5, 9] (by decide +kernel)
noncomputable def vertices_308 : Finset (Fin 10) := literalFinset [2, 4, 5, 8] (by decide +kernel)
noncomputable def vertices_804 : Finset (Fin 10) := literalFinset [2, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_936 : Finset (Fin 10) := literalFinset [3, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_496 : Finset (Fin 10) := literalFinset [4, 5, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_67 : Finset (Fin 10) := literalFinset [0, 1, 6] (by decide +kernel)
noncomputable def vertices_21 : Finset (Fin 10) := literalFinset [0, 2, 4] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_57 : Finset (Fin 10) := literalFinset [0, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_201 : Finset (Fin 10) := literalFinset [0, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_785 : Finset (Fin 10) := literalFinset [0, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_138 : Finset (Fin 10) := literalFinset [1, 3, 7] (by decide +kernel)
noncomputable def vertices_194 : Finset (Fin 10) := literalFinset [1, 6, 7] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_292 : Finset (Fin 10) := literalFinset [2, 5, 8] (by decide +kernel)
noncomputable def vertices_548 : Finset (Fin 10) := literalFinset [2, 5, 9] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_552 : Finset (Fin 10) := literalFinset [3, 5, 9] (by decide +kernel)
noncomputable def vertices_648 : Finset (Fin 10) := literalFinset [3, 7, 9] (by decide +kernel)
noncomputable def vertices_240 : Finset (Fin 10) := literalFinset [4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_203, vertices_789, vertices_249, vertices_849, vertices_654, vertices_962, vertices_556, vertices_308, vertices_804, vertices_936, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_517, vertices_57, vertices_201, vertices_81, vertices_785, vertices_577, vertices_14, vertices_518, vertices_138, vertices_194, vertices_578, vertices_642, vertices_44, vertices_524, vertices_52, vertices_276, vertices_292, vertices_548, vertices_772, vertices_168, vertices_552, vertices_648, vertices_240, vertices_304, vertices_336, vertices_416, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_203), (false, vertices_789), (false, vertices_249), (false, vertices_849), (true, vertices_642), (true, vertices_524), (true, vertices_292), (true, vertices_548), (true, vertices_552), (true, vertices_648), (true, vertices_304), (true, vertices_416), (true, vertices_800), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![11, 13, 14, 17, 21, 22, 23, 24, 25]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_583) then 12 else
  if p.val = (false, vertices_203) then 16 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_249) then 19 else
  if p.val = (false, vertices_849) then 20 else
  if p.val = (true, vertices_642) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_416) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_249), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 3
  frame := ![3, 4, 5]
  vertex := 6
  face := Sum.inr ⟨vertices_240, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_240, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 2, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_654, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_654, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 5, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_962, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_194, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![2, 4, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_936, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_168, (by decide +kernel)⟩ ⟨vertices_936, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![3, 1, 0, 2]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_654, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_654, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_962, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_194, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_556, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![1, 2, 4, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_556, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_308, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![1, 3, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_308, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_804, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![1, 4, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_292, (by decide +kernel)⟩ ⟨vertices_804, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_936, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![2, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_168, (by decide +kernel)⟩ ⟨vertices_936, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_496, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![3, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_240, (by decide +kernel)⟩ ⟨vertices_496, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coveringFacets : Fin 7 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6]
noncomputable def coveringProof (j : Fin 7) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (fun i => Fin.elim0 i)))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 7, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0059

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_multi_six_0060.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0060

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_583 : Finset (Fin 10) := literalFinset [0, 1, 2, 6, 9] (by decide +kernel)
noncomputable def vertices_203 : Finset (Fin 10) := literalFinset [0, 1, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_789 : Finset (Fin 10) := literalFinset [0, 2, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_249 : Finset (Fin 10) := literalFinset [0, 3, 4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_849 : Finset (Fin 10) := literalFinset [0, 4, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_654 : Finset (Fin 10) := literalFinset [1, 2, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_962 : Finset (Fin 10) := literalFinset [1, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_300 : Finset (Fin 10) := literalFinset [2, 3, 5, 8] (by decide +kernel)
noncomputable def vertices_780 : Finset (Fin 10) := literalFinset [2, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_308 : Finset (Fin 10) := literalFinset [2, 4, 5, 8] (by decide +kernel)
noncomputable def vertices_936 : Finset (Fin 10) := literalFinset [3, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_496 : Finset (Fin 10) := literalFinset [4, 5, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_67 : Finset (Fin 10) := literalFinset [0, 1, 6] (by decide +kernel)
noncomputable def vertices_21 : Finset (Fin 10) := literalFinset [0, 2, 4] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_57 : Finset (Fin 10) := literalFinset [0, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_201 : Finset (Fin 10) := literalFinset [0, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_785 : Finset (Fin 10) := literalFinset [0, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_138 : Finset (Fin 10) := literalFinset [1, 3, 7] (by decide +kernel)
noncomputable def vertices_194 : Finset (Fin 10) := literalFinset [1, 6, 7] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_268 : Finset (Fin 10) := literalFinset [2, 3, 8] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_292 : Finset (Fin 10) := literalFinset [2, 5, 8] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_648 : Finset (Fin 10) := literalFinset [3, 7, 9] (by decide +kernel)
noncomputable def vertices_776 : Finset (Fin 10) := literalFinset [3, 8, 9] (by decide +kernel)
noncomputable def vertices_240 : Finset (Fin 10) := literalFinset [4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_203, vertices_789, vertices_249, vertices_849, vertices_654, vertices_962, vertices_300, vertices_780, vertices_308, vertices_936, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_517, vertices_57, vertices_201, vertices_81, vertices_785, vertices_577, vertices_14, vertices_518, vertices_138, vertices_194, vertices_578, vertices_642, vertices_44, vertices_268, vertices_524, vertices_52, vertices_276, vertices_292, vertices_772, vertices_168, vertices_296, vertices_648, vertices_776, vertices_240, vertices_304, vertices_336, vertices_416, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_203), (false, vertices_789), (false, vertices_249), (false, vertices_849), (true, vertices_642), (true, vertices_268), (true, vertices_524), (true, vertices_292), (true, vertices_296), (true, vertices_648), (true, vertices_776), (true, vertices_304), (true, vertices_416), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![11, 13, 14, 17, 21, 22, 23, 24, 25]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_583) then 12 else
  if p.val = (false, vertices_203) then 16 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_249) then 19 else
  if p.val = (false, vertices_849) then 20 else
  if p.val = (true, vertices_642) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_292) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_249), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 3
  frame := ![3, 4, 5]
  vertex := 6
  face := Sum.inr ⟨vertices_240, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_240, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 2, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_654, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_654, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 5, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_962, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_194, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![2, 4, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_936, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_168, (by decide +kernel)⟩ ⟨vertices_936, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![3, 1, 0, 2]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_654, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_654, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_962, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_194, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_300, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![1, 2, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_300, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_780, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![1, 2, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_268, (by decide +kernel)⟩ ⟨vertices_780, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_308, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![1, 3, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_308, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_936, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![2, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_168, (by decide +kernel)⟩ ⟨vertices_936, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_496, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![3, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_240, (by decide +kernel)⟩ ⟨vertices_496, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coveringFacets : Fin 7 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6]
noncomputable def coveringProof (j : Fin 7) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (fun i => Fin.elim0 i)))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 7, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0060

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_multi_six_0061.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0061

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_775 : Finset (Fin 10) := literalFinset [0, 1, 2, 8, 9] (by decide +kernel)
noncomputable def vertices_203 : Finset (Fin 10) := literalFinset [0, 1, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_835 : Finset (Fin 10) := literalFinset [0, 1, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_341 : Finset (Fin 10) := literalFinset [0, 2, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_249 : Finset (Fin 10) := literalFinset [0, 3, 4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_654 : Finset (Fin 10) := literalFinset [1, 2, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_706 : Finset (Fin 10) := literalFinset [1, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_556 : Finset (Fin 10) := literalFinset [2, 3, 5, 9] (by decide +kernel)
noncomputable def vertices_820 : Finset (Fin 10) := literalFinset [2, 4, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_936 : Finset (Fin 10) := literalFinset [3, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_496 : Finset (Fin 10) := literalFinset [4, 5, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_960 : Finset (Fin 10) := literalFinset [6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_67 : Finset (Fin 10) := literalFinset [0, 1, 6] (by decide +kernel)
noncomputable def vertices_771 : Finset (Fin 10) := literalFinset [0, 1, 8, 9] (by decide +kernel)
noncomputable def vertices_21 : Finset (Fin 10) := literalFinset [0, 2, 4] (by decide +kernel)
noncomputable def vertices_261 : Finset (Fin 10) := literalFinset [0, 2, 8] (by decide +kernel)
noncomputable def vertices_57 : Finset (Fin 10) := literalFinset [0, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_201 : Finset (Fin 10) := literalFinset [0, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_138 : Finset (Fin 10) := literalFinset [1, 3, 7] (by decide +kernel)
noncomputable def vertices_194 : Finset (Fin 10) := literalFinset [1, 6, 7] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_548 : Finset (Fin 10) := literalFinset [2, 5, 9] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_552 : Finset (Fin 10) := literalFinset [3, 5, 9] (by decide +kernel)
noncomputable def vertices_648 : Finset (Fin 10) := literalFinset [3, 7, 9] (by decide +kernel)
noncomputable def vertices_240 : Finset (Fin 10) := literalFinset [4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_203, vertices_835, vertices_341, vertices_249, vertices_654, vertices_706, vertices_556, vertices_820, vertices_936, vertices_496, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_771, vertices_21, vertices_261, vertices_57, vertices_201, vertices_81, vertices_321, vertices_14, vertices_518, vertices_138, vertices_194, vertices_578, vertices_642, vertices_44, vertices_524, vertices_52, vertices_276, vertices_548, vertices_772, vertices_168, vertices_552, vertices_648, vertices_240, vertices_304, vertices_336, vertices_416, vertices_800, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_203), (false, vertices_835), (false, vertices_341), (false, vertices_249), (true, vertices_642), (true, vertices_524), (true, vertices_548), (true, vertices_552), (true, vertices_648), (true, vertices_304), (true, vertices_416), (true, vertices_800), (true, vertices_448), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![16, 11, 13, 19, 21, 22, 23, 24, 25]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_203) then 15 else
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_341) then 12 else
  if p.val = (false, vertices_249) then 20 else
  if p.val = (true, vertices_642) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_648) then 4 else
  if p.val = (true, vertices_304) then 5 else
  if p.val = (true, vertices_416) then 6 else
  if p.val = (true, vertices_800) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_249), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 3
  frame := ![3, 4, 5]
  vertex := 6
  face := Sum.inr ⟨vertices_240, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_240, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 2, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_654, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_654, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 3, 4, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_820, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_820, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![2, 4, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_936, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_168, (by decide +kernel)⟩ ⟨vertices_936, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![5, 0, 1, 2]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_654, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_654, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_706, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 5, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_194, (by decide +kernel)⟩ ⟨vertices_706, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_556, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![1, 2, 4, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_556, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_820, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 3, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_820, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_936, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![2, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_168, (by decide +kernel)⟩ ⟨vertices_936, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_496, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![3, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_240, (by decide +kernel)⟩ ⟨vertices_496, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_960, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![5, 6, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_448, (by decide +kernel)⟩ ⟨vertices_960, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coveringFacets : Fin 7 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6]
noncomputable def coveringProof (j : Fin 7) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (fun i => Fin.elim0 i)))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 7, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0061

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_multi_six_0062.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0062

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_519 : Finset (Fin 10) := literalFinset [0, 1, 2, 9] (by decide +kernel)
noncomputable def vertices_651 : Finset (Fin 10) := literalFinset [0, 1, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_341 : Finset (Fin 10) := literalFinset [0, 2, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_837 : Finset (Fin 10) := literalFinset [0, 2, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_553 : Finset (Fin 10) := literalFinset [0, 3, 5, 9] (by decide +kernel)
noncomputable def vertices_817 : Finset (Fin 10) := literalFinset [0, 4, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_206 : Finset (Fin 10) := literalFinset [1, 2, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_582 : Finset (Fin 10) := literalFinset [1, 2, 6, 9] (by decide +kernel)
noncomputable def vertices_962 : Finset (Fin 10) := literalFinset [1, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_252 : Finset (Fin 10) := literalFinset [2, 3, 4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_936 : Finset (Fin 10) := literalFinset [3, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_496 : Finset (Fin 10) := literalFinset [4, 5, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_515 : Finset (Fin 10) := literalFinset [0, 1, 9] (by decide +kernel)
noncomputable def vertices_21 : Finset (Fin 10) := literalFinset [0, 2, 4] (by decide +kernel)
noncomputable def vertices_325 : Finset (Fin 10) := literalFinset [0, 2, 6, 8] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_521 : Finset (Fin 10) := literalFinset [0, 3, 9] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_273 : Finset (Fin 10) := literalFinset [0, 4, 8] (by decide +kernel)
noncomputable def vertices_545 : Finset (Fin 10) := literalFinset [0, 5, 9] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_70 : Finset (Fin 10) := literalFinset [1, 2, 6] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_138 : Finset (Fin 10) := literalFinset [1, 3, 7] (by decide +kernel)
noncomputable def vertices_194 : Finset (Fin 10) := literalFinset [1, 6, 7] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_60 : Finset (Fin 10) := literalFinset [2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_204 : Finset (Fin 10) := literalFinset [2, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_580 : Finset (Fin 10) := literalFinset [2, 6, 9] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_552 : Finset (Fin 10) := literalFinset [3, 5, 9] (by decide +kernel)
noncomputable def vertices_648 : Finset (Fin 10) := literalFinset [3, 7, 9] (by decide +kernel)
noncomputable def vertices_240 : Finset (Fin 10) := literalFinset [4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_651, vertices_341, vertices_837, vertices_553, vertices_817, vertices_206, vertices_582, vertices_962, vertices_252, vertices_936, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_325, vertices_517, vertices_41, vertices_521, vertices_49, vertices_273, vertices_545, vertices_769, vertices_14, vertices_70, vertices_518, vertices_138, vertices_194, vertices_578, vertices_642, vertices_60, vertices_204, vertices_84, vertices_580, vertices_168, vertices_552, vertices_648, vertices_240, vertices_304, vertices_336, vertices_416, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_651), (false, vertices_341), (false, vertices_837), (false, vertices_553), (false, vertices_817), (true, vertices_70), (true, vertices_194), (true, vertices_578), (true, vertices_204), (true, vertices_168), (true, vertices_240), (true, vertices_416), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![9, 14, 11, 17, 20, 21, 22, 23, 24]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_651) then 10 else
  if p.val = (false, vertices_341) then 15 else
  if p.val = (false, vertices_837) then 16 else
  if p.val = (false, vertices_553) then 1 else
  if p.val = (false, vertices_817) then 18 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_204) then 13 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_240) then 19 else
  if p.val = (true, vertices_416) then 6 else
  if p.val = (true, vertices_448) then 7 else
  if p.val = (true, vertices_896) then 8 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 11 => Sum.inl 2
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 5, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_962, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_194, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![2, 4, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_936, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_168, (by decide +kernel)⟩ ⟨vertices_936, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 3, 5]
  vertex := 4
  face := Sum.inl ⟨vertices_252, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_252, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 3, 5]
  vertex := 6
  face := Sum.inl ⟨vertices_252, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_252, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 7, 4, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_206, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .fromLargerFacet ![0, 1, 2, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_206, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_204, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_252, by decide +kernel⟩ ![1, 2, 3, 5]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_252, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_582, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 1, 5, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_70, (by decide +kernel)⟩ ⟨vertices_582, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_962, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_194, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_252, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![1, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_252, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_936, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![2, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_168, (by decide +kernel)⟩ ⟨vertices_936, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_496, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fromLargerFacet ![3, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_240, (by decide +kernel)⟩ ⟨vertices_496, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_240, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_252, by decide +kernel⟩ ![1, 2, 3, 5]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_252, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def coveringFacets : Fin 6 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5]
noncomputable def coveringProof (j : Fin 6) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (fun i => Fin.elim0 i))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 6, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0062

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_multi_six_0063.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0063

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_583 : Finset (Fin 10) := literalFinset [0, 1, 2, 6, 9] (by decide +kernel)
noncomputable def vertices_651 : Finset (Fin 10) := literalFinset [0, 1, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_277 : Finset (Fin 10) := literalFinset [0, 2, 4, 8] (by decide +kernel)
noncomputable def vertices_837 : Finset (Fin 10) := literalFinset [0, 2, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_553 : Finset (Fin 10) := literalFinset [0, 3, 5, 9] (by decide +kernel)
noncomputable def vertices_817 : Finset (Fin 10) := literalFinset [0, 4, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_206 : Finset (Fin 10) := literalFinset [1, 2, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_962 : Finset (Fin 10) := literalFinset [1, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_252 : Finset (Fin 10) := literalFinset [2, 3, 4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_340 : Finset (Fin 10) := literalFinset [2, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_936 : Finset (Fin 10) := literalFinset [3, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_496 : Finset (Fin 10) := literalFinset [4, 5, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_515 : Finset (Fin 10) := literalFinset [0, 1, 9] (by decide +kernel)
noncomputable def vertices_21 : Finset (Fin 10) := literalFinset [0, 2, 4] (by decide +kernel)
noncomputable def vertices_581 : Finset (Fin 10) := literalFinset [0, 2, 6, 9] (by decide +kernel)
noncomputable def vertices_261 : Finset (Fin 10) := literalFinset [0, 2, 8] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_521 : Finset (Fin 10) := literalFinset [0, 3, 9] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_273 : Finset (Fin 10) := literalFinset [0, 4, 8] (by decide +kernel)
noncomputable def vertices_545 : Finset (Fin 10) := literalFinset [0, 5, 9] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_70 : Finset (Fin 10) := literalFinset [1, 2, 6] (by decide +kernel)
noncomputable def vertices_138 : Finset (Fin 10) := literalFinset [1, 3, 7] (by decide +kernel)
noncomputable def vertices_194 : Finset (Fin 10) := literalFinset [1, 6, 7] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_60 : Finset (Fin 10) := literalFinset [2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_204 : Finset (Fin 10) := literalFinset [2, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_324 : Finset (Fin 10) := literalFinset [2, 6, 8] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_552 : Finset (Fin 10) := literalFinset [3, 5, 9] (by decide +kernel)
noncomputable def vertices_648 : Finset (Fin 10) := literalFinset [3, 7, 9] (by decide +kernel)
noncomputable def vertices_240 : Finset (Fin 10) := literalFinset [4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_651, vertices_277, vertices_837, vertices_553, vertices_817, vertices_206, vertices_962, vertices_252, vertices_340, vertices_936, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_581, vertices_261, vertices_41, vertices_521, vertices_49, vertices_273, vertices_545, vertices_769, vertices_14, vertices_70, vertices_138, vertices_194, vertices_578, vertices_642, vertices_60, vertices_204, vertices_84, vertices_276, vertices_324, vertices_168, vertices_552, vertices_648, vertices_240, vertices_304, vertices_336, vertices_416, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_651), (false, vertices_277), (false, vertices_837), (false, vertices_553), (false, vertices_817), (true, vertices_194), (true, vertices_204), (true, vertices_84), (true, vertices_168), (true, vertices_240), (true, vertices_336), (true, vertices_416), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![9, 14, 11, 17, 20, 21, 22, 23, 24]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_583) then 15 else
  if p.val = (false, vertices_651) then 10 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_837) then 16 else
  if p.val = (false, vertices_553) then 1 else
  if p.val = (false, vertices_817) then 18 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_204) then 13 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_240) then 19 else
  if p.val = (true, vertices_336) then 5 else
  if p.val = (true, vertices_416) then 6 else
  if p.val = (true, vertices_448) then 7 else
  if p.val = (true, vertices_896) then 8 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 11 => Sum.inl 2
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 5, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_962, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_194, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![2, 4, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_936, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_168, (by decide +kernel)⟩ ⟨vertices_936, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 3, 5]
  vertex := 4
  face := Sum.inl ⟨vertices_252, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_252, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 3, 5]
  vertex := 6
  face := Sum.inl ⟨vertices_252, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_252, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 7, 4, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_206, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .fromLargerFacet ![0, 1, 2, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_206, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_204, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_252, by decide +kernel⟩ ![1, 2, 3, 5]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_252, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_962, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_194, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_252, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![1, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_252, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_340, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![1, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_340, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_936, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![2, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_168, (by decide +kernel)⟩ ⟨vertices_936, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_496, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fromLargerFacet ![3, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_240, (by decide +kernel)⟩ ⟨vertices_496, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_240, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_252, by decide +kernel⟩ ![1, 2, 3, 5]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_252, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def coveringFacets : Fin 6 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5]
noncomputable def coveringProof (j : Fin 6) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (fun i => Fin.elim0 i))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 6, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0063

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_multi_six_0064.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0064

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_519 : Finset (Fin 10) := literalFinset [0, 1, 2, 9] (by decide +kernel)
noncomputable def vertices_651 : Finset (Fin 10) := literalFinset [0, 1, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_341 : Finset (Fin 10) := literalFinset [0, 2, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_773 : Finset (Fin 10) := literalFinset [0, 2, 8, 9] (by decide +kernel)
noncomputable def vertices_553 : Finset (Fin 10) := literalFinset [0, 3, 5, 9] (by decide +kernel)
noncomputable def vertices_817 : Finset (Fin 10) := literalFinset [0, 4, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_206 : Finset (Fin 10) := literalFinset [1, 2, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_838 : Finset (Fin 10) := literalFinset [1, 2, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_962 : Finset (Fin 10) := literalFinset [1, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_252 : Finset (Fin 10) := literalFinset [2, 3, 4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_936 : Finset (Fin 10) := literalFinset [3, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_496 : Finset (Fin 10) := literalFinset [4, 5, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_515 : Finset (Fin 10) := literalFinset [0, 1, 9] (by decide +kernel)
noncomputable def vertices_21 : Finset (Fin 10) := literalFinset [0, 2, 4] (by decide +kernel)
noncomputable def vertices_261 : Finset (Fin 10) := literalFinset [0, 2, 8] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_521 : Finset (Fin 10) := literalFinset [0, 3, 9] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_273 : Finset (Fin 10) := literalFinset [0, 4, 8] (by decide +kernel)
noncomputable def vertices_545 : Finset (Fin 10) := literalFinset [0, 5, 9] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_70 : Finset (Fin 10) := literalFinset [1, 2, 6] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_138 : Finset (Fin 10) := literalFinset [1, 3, 7] (by decide +kernel)
noncomputable def vertices_194 : Finset (Fin 10) := literalFinset [1, 6, 7] (by decide +kernel)
noncomputable def vertices_834 : Finset (Fin 10) := literalFinset [1, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_60 : Finset (Fin 10) := literalFinset [2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_204 : Finset (Fin 10) := literalFinset [2, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_324 : Finset (Fin 10) := literalFinset [2, 6, 8] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_552 : Finset (Fin 10) := literalFinset [3, 5, 9] (by decide +kernel)
noncomputable def vertices_648 : Finset (Fin 10) := literalFinset [3, 7, 9] (by decide +kernel)
noncomputable def vertices_240 : Finset (Fin 10) := literalFinset [4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_651, vertices_341, vertices_773, vertices_553, vertices_817, vertices_206, vertices_838, vertices_962, vertices_252, vertices_936, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_261, vertices_517, vertices_41, vertices_521, vertices_49, vertices_273, vertices_545, vertices_769, vertices_14, vertices_70, vertices_518, vertices_138, vertices_194, vertices_834, vertices_642, vertices_60, vertices_204, vertices_84, vertices_324, vertices_772, vertices_168, vertices_552, vertices_648, vertices_240, vertices_304, vertices_336, vertices_416, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_651), (false, vertices_341), (false, vertices_773), (false, vertices_553), (false, vertices_817), (true, vertices_70), (true, vertices_194), (true, vertices_834), (true, vertices_204), (true, vertices_168), (true, vertices_240), (true, vertices_416), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![9, 12, 16, 17, 20, 21, 22, 23, 24]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_651) then 10 else
  if p.val = (false, vertices_341) then 14 else
  if p.val = (false, vertices_773) then 1 else
  if p.val = (false, vertices_553) then 2 else
  if p.val = (false, vertices_817) then 18 else
  if p.val = (true, vertices_70) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_834) then 11 else
  if p.val = (true, vertices_204) then 15 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_240) then 19 else
  if p.val = (true, vertices_416) then 6 else
  if p.val = (true, vertices_448) then 7 else
  if p.val = (true, vertices_896) then 8 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_773), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_834), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 3
  frame := ![0, 5, 7]
  vertex := 8
  face := Sum.inr ⟨vertices_834, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_834, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![2, 4, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_936, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_168, (by decide +kernel)⟩ ⟨vertices_936, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 3, 5]
  vertex := 4
  face := Sum.inl ⟨vertices_252, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_252, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 3, 5]
  vertex := 6
  face := Sum.inl ⟨vertices_252, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_252, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 7, 4, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_206, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .fromLargerFacet ![0, 1, 2, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_206, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_204, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_252, by decide +kernel⟩ ![1, 2, 3, 5]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_252, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_838, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_70, (by decide +kernel)⟩ ⟨vertices_838, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_962, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_194, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_252, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![1, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_252, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_936, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![2, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_168, (by decide +kernel)⟩ ⟨vertices_936, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_496, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fromLargerFacet ![3, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_240, (by decide +kernel)⟩ ⟨vertices_496, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_240, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_252, by decide +kernel⟩ ![1, 2, 3, 5]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_252, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def coveringFacets : Fin 6 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5]
noncomputable def coveringProof (j : Fin 6) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (fun i => Fin.elim0 i))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 6, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0064

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_multi_six_0065.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0065

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_583 : Finset (Fin 10) := literalFinset [0, 1, 2, 6, 9] (by decide +kernel)
noncomputable def vertices_203 : Finset (Fin 10) := literalFinset [0, 1, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_653 : Finset (Fin 10) := literalFinset [0, 2, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_961 : Finset (Fin 10) := literalFinset [0, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_534 : Finset (Fin 10) := literalFinset [1, 2, 4, 9] (by decide +kernel)
noncomputable def vertices_250 : Finset (Fin 10) := literalFinset [1, 3, 4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_850 : Finset (Fin 10) := literalFinset [1, 4, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_812 : Finset (Fin 10) := literalFinset [2, 3, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_820 : Finset (Fin 10) := literalFinset [2, 4, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_424 : Finset (Fin 10) := literalFinset [3, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_904 : Finset (Fin 10) := literalFinset [3, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_496 : Finset (Fin 10) := literalFinset [4, 5, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_67 : Finset (Fin 10) := literalFinset [0, 1, 6] (by decide +kernel)
noncomputable def vertices_13 : Finset (Fin 10) := literalFinset [0, 2, 3] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_193 : Finset (Fin 10) := literalFinset [0, 6, 7] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_22 : Finset (Fin 10) := literalFinset [1, 2, 4] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_58 : Finset (Fin 10) := literalFinset [1, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_202 : Finset (Fin 10) := literalFinset [1, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_82 : Finset (Fin 10) := literalFinset [1, 4, 6] (by decide +kernel)
noncomputable def vertices_530 : Finset (Fin 10) := literalFinset [1, 4, 9] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_532 : Finset (Fin 10) := literalFinset [2, 4, 9] (by decide +kernel)
noncomputable def vertices_804 : Finset (Fin 10) := literalFinset [2, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_392 : Finset (Fin 10) := literalFinset [3, 7, 8] (by decide +kernel)
noncomputable def vertices_648 : Finset (Fin 10) := literalFinset [3, 7, 9] (by decide +kernel)
noncomputable def vertices_776 : Finset (Fin 10) := literalFinset [3, 8, 9] (by decide +kernel)
noncomputable def vertices_240 : Finset (Fin 10) := literalFinset [4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_784 : Finset (Fin 10) := literalFinset [4, 8, 9] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_203, vertices_653, vertices_961, vertices_534, vertices_250, vertices_850, vertices_812, vertices_820, vertices_424, vertices_904, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_517, vertices_137, vertices_193, vertices_577, vertices_641, vertices_22, vertices_518, vertices_58, vertices_202, vertices_82, vertices_530, vertices_578, vertices_44, vertices_524, vertices_52, vertices_532, vertices_804, vertices_168, vertices_296, vertices_392, vertices_648, vertices_776, vertices_240, vertices_304, vertices_336, vertices_784, vertices_416, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_203), (false, vertices_653), (false, vertices_961), (true, vertices_82), (true, vertices_530), (true, vertices_532), (true, vertices_804), (true, vertices_168), (true, vertices_296), (true, vertices_392), (true, vertices_776), (true, vertices_240), (true, vertices_304), (true, vertices_336), (true, vertices_784), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![11, 14, 18, 19, 21, 22, 24, 25, 26]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_583) then 12 else
  if p.val = (false, vertices_203) then 13 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_804) then 17 else
  if p.val = (true, vertices_168) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_392) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_240) then 20 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_416) then 10 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_804), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 3
  frame := ![1, 4, 7]
  vertex := 8
  face := Sum.inr ⟨vertices_804, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_804, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 5]
  vertex := 4
  face := Sum.inl ⟨vertices_250, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 5]
  vertex := 6
  face := Sum.inl ⟨vertices_250, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 3, 5, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_850, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_82, (by decide +kernel)⟩ ⟨vertices_850, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![1, 4, 2, 0]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_534, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .fundamental ![0, 1, 3, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_534, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_250, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_850, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_82, (by decide +kernel)⟩ ⟨vertices_850, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_812, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 2, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_812, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_820, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![1, 3, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_820, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_424, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![2, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_168, (by decide +kernel)⟩ ⟨vertices_424, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_904, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![2, 6, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_392, (by decide +kernel)⟩ ⟨vertices_904, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_496, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fromLargerFacet ![3, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_240, (by decide +kernel)⟩ ⟨vertices_496, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_240, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_250, by decide +kernel⟩ ![0, 2, 3, 5]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def coveringFacets : Fin 8 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6, coverFacet7]
noncomputable def coveringProof (j : Fin 8) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (Fin.cases cover7 (fun i => Fin.elim0 i))))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 8, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0065

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_multi_six_0066.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0066

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_583 : Finset (Fin 10) := literalFinset [0, 1, 2, 6, 9] (by decide +kernel)
noncomputable def vertices_779 : Finset (Fin 10) := literalFinset [0, 1, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_597 : Finset (Fin 10) := literalFinset [0, 2, 4, 6, 9] (by decide +kernel)
noncomputable def vertices_425 : Finset (Fin 10) := literalFinset [0, 3, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_817 : Finset (Fin 10) := literalFinset [0, 4, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_270 : Finset (Fin 10) := literalFinset [1, 2, 3, 8] (by decide +kernel)
noncomputable def vertices_326 : Finset (Fin 10) := literalFinset [1, 2, 6, 8] (by decide +kernel)
noncomputable def vertices_962 : Finset (Fin 10) := literalFinset [1, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_252 : Finset (Fin 10) := literalFinset [2, 3, 4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_460 : Finset (Fin 10) := literalFinset [2, 3, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_752 : Finset (Fin 10) := literalFinset [4, 5, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_928 : Finset (Fin 10) := literalFinset [5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_515 : Finset (Fin 10) := literalFinset [0, 1, 9] (by decide +kernel)
noncomputable def vertices_21 : Finset (Fin 10) := literalFinset [0, 2, 4] (by decide +kernel)
noncomputable def vertices_581 : Finset (Fin 10) := literalFinset [0, 2, 6, 9] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_265 : Finset (Fin 10) := literalFinset [0, 3, 8] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_529 : Finset (Fin 10) := literalFinset [0, 4, 9] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_70 : Finset (Fin 10) := literalFinset [1, 2, 6] (by decide +kernel)
noncomputable def vertices_262 : Finset (Fin 10) := literalFinset [1, 2, 8] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_322 : Finset (Fin 10) := literalFinset [1, 6, 8] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_60 : Finset (Fin 10) := literalFinset [2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_204 : Finset (Fin 10) := literalFinset [2, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_268 : Finset (Fin 10) := literalFinset [2, 3, 8] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_324 : Finset (Fin 10) := literalFinset [2, 6, 8] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_392 : Finset (Fin 10) := literalFinset [3, 7, 8] (by decide +kernel)
noncomputable def vertices_240 : Finset (Fin 10) := literalFinset [4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_779, vertices_597, vertices_425, vertices_817, vertices_270, vertices_326, vertices_962, vertices_252, vertices_460, vertices_752, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_581, vertices_41, vertices_265, vertices_49, vertices_529, vertices_289, vertices_769, vertices_14, vertices_70, vertices_262, vertices_266, vertices_322, vertices_578, vertices_770, vertices_60, vertices_204, vertices_268, vertices_84, vertices_324, vertices_168, vertices_392, vertices_240, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_779), (false, vertices_597), (false, vertices_425), (false, vertices_817), (true, vertices_262), (true, vertices_322), (true, vertices_204), (true, vertices_268), (true, vertices_324), (true, vertices_240), (true, vertices_672), (true, vertices_448), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![8, 14, 10, 17, 20, 21, 22, 23, 24]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 11 else
  if p.val = (false, vertices_583) then 15 else
  if p.val = (false, vertices_779) then 9 else
  if p.val = (false, vertices_597) then 16 else
  if p.val = (false, vertices_425) then 12 else
  if p.val = (false, vertices_817) then 18 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_204) then 13 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_324) then 3 else
  if p.val = (true, vertices_240) then 19 else
  if p.val = (true, vertices_672) then 4 else
  if p.val = (true, vertices_448) then 5 else
  if p.val = (true, vertices_704) then 6 else
  if p.val = (true, vertices_896) then 7 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 10 => Sum.inl 2
  | 11 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 5, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_962, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_322, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 3, 5]
  vertex := 4
  face := Sum.inl ⟨vertices_252, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_252, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 3, 5]
  vertex := 6
  face := Sum.inl ⟨vertices_252, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_252, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 3 → HeightRow boundary := ![row0, row1, row2]
noncomputable def pivot : Fin 3 → Fin 9 := ![0, 4, 1]
noncomputable def heightProof : HeightCertificate boundary 3 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_270, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .fundamental ![0, 1, 2, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_270, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_326, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 1, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_70, (by decide +kernel)⟩ ⟨vertices_326, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_962, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_322, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_252, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![1, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_252, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_460, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fromLargerFacet ![1, 2, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_204, (by decide +kernel)⟩ ⟨vertices_460, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_204, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_252, by decide +kernel⟩ ![1, 2, 3, 5]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_252, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_752, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fromLargerFacet ![3, 4, 5, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_240, (by decide +kernel)⟩ ⟨vertices_752, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_240, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_252, by decide +kernel⟩ ![1, 2, 3, 5]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_252, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_928, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![4, 6, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_416, (by decide +kernel)⟩ ⟨vertices_928, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coveringFacets : Fin 7 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6]
noncomputable def coveringProof (j : Fin 7) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (fun i => Fin.elim0 i)))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 3 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 7, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0066

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_multi_six_0068.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0068

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_327 : Finset (Fin 10) := literalFinset [0, 1, 2, 6, 8] (by decide +kernel)
noncomputable def vertices_203 : Finset (Fin 10) := literalFinset [0, 1, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_397 : Finset (Fin 10) := literalFinset [0, 2, 3, 7, 8] (by decide +kernel)
noncomputable def vertices_961 : Finset (Fin 10) := literalFinset [0, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_278 : Finset (Fin 10) := literalFinset [1, 2, 4, 8] (by decide +kernel)
noncomputable def vertices_122 : Finset (Fin 10) := literalFinset [1, 3, 4, 5, 6] (by decide +kernel)
noncomputable def vertices_850 : Finset (Fin 10) := literalFinset [1, 4, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_940 : Finset (Fin 10) := literalFinset [2, 3, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_820 : Finset (Fin 10) := literalFinset [2, 4, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_744 : Finset (Fin 10) := literalFinset [3, 5, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_624 : Finset (Fin 10) := literalFinset [4, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_67 : Finset (Fin 10) := literalFinset [0, 1, 6] (by decide +kernel)
noncomputable def vertices_13 : Finset (Fin 10) := literalFinset [0, 2, 3] (by decide +kernel)
noncomputable def vertices_261 : Finset (Fin 10) := literalFinset [0, 2, 8] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_193 : Finset (Fin 10) := literalFinset [0, 6, 7] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_385 : Finset (Fin 10) := literalFinset [0, 7, 8] (by decide +kernel)
noncomputable def vertices_22 : Finset (Fin 10) := literalFinset [1, 2, 4] (by decide +kernel)
noncomputable def vertices_262 : Finset (Fin 10) := literalFinset [1, 2, 8] (by decide +kernel)
noncomputable def vertices_58 : Finset (Fin 10) := literalFinset [1, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_74 : Finset (Fin 10) := literalFinset [1, 3, 6] (by decide +kernel)
noncomputable def vertices_82 : Finset (Fin 10) := literalFinset [1, 4, 6] (by decide +kernel)
noncomputable def vertices_274 : Finset (Fin 10) := literalFinset [1, 4, 8] (by decide +kernel)
noncomputable def vertices_322 : Finset (Fin 10) := literalFinset [1, 6, 8] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_396 : Finset (Fin 10) := literalFinset [2, 3, 7, 8] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_804 : Finset (Fin 10) := literalFinset [2, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_104 : Finset (Fin 10) := literalFinset [3, 5, 6] (by decide +kernel)
noncomputable def vertices_680 : Finset (Fin 10) := literalFinset [3, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_200 : Finset (Fin 10) := literalFinset [3, 6, 7] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_784 : Finset (Fin 10) := literalFinset [4, 8, 9] (by decide +kernel)
noncomputable def vertices_608 : Finset (Fin 10) := literalFinset [5, 6, 9] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_203, vertices_397, vertices_961, vertices_278, vertices_122, vertices_850, vertices_940, vertices_820, vertices_744, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_261, vertices_137, vertices_193, vertices_321, vertices_385, vertices_22, vertices_262, vertices_58, vertices_74, vertices_82, vertices_274, vertices_322, vertices_44, vertices_396, vertices_52, vertices_276, vertices_804, vertices_104, vertices_680, vertices_200, vertices_112, vertices_560, vertices_592, vertices_784, vertices_608, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_203), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_274), (true, vertices_276), (true, vertices_804), (true, vertices_104), (true, vertices_680), (true, vertices_112), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![9, 12, 16, 18, 19, 20, 22, 23, 24]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_327) then 10 else
  if p.val = (false, vertices_203) then 11 else
  if p.val = (false, vertices_397) then 14 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_804) then 15 else
  if p.val = (true, vertices_104) then 3 else
  if p.val = (true, vertices_680) then 17 else
  if p.val = (true, vertices_112) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_592) then 6 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_608) then 8 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_804), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(true, vertices_680), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 3, 5, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_850, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_82, (by decide +kernel)⟩ ⟨vertices_850, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 3
  frame := ![0, 2, 3]
  vertex := 4
  face := Sum.inr ⟨vertices_58, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 4, 6]
  vertex := 7
  face := Sum.inl ⟨vertices_940, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_940, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 4, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_940, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_940, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![5, 0, 7, 2]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_278, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .fundamental ![0, 1, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_278, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_122, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_122, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_850, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_82, (by decide +kernel)⟩ ⟨vertices_850, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_940, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![1, 2, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_940, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_820, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fromLargerFacet ![1, 3, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_820, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_804, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_940, by decide +kernel⟩ ![1, 2, 4, 6]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_940, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_744, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fromLargerFacet ![2, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_104, (by decide +kernel)⟩ ⟨vertices_744, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_680, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_940, by decide +kernel⟩ ![1, 2, 4, 6]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_940, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_624, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![3, 4, 5, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_624, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coveringFacets : Fin 7 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6]
noncomputable def coveringProof (j : Fin 7) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (fun i => Fin.elim0 i)))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 7, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0068

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_multi_six_0070.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0070

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_775 : Finset (Fin 10) := literalFinset [0, 1, 2, 8, 9] (by decide +kernel)
noncomputable def vertices_331 : Finset (Fin 10) := literalFinset [0, 1, 3, 6, 8] (by decide +kernel)
noncomputable def vertices_589 : Finset (Fin 10) := literalFinset [0, 2, 3, 6, 9] (by decide +kernel)
noncomputable def vertices_961 : Finset (Fin 10) := literalFinset [0, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_278 : Finset (Fin 10) := literalFinset [1, 2, 4, 8] (by decide +kernel)
noncomputable def vertices_250 : Finset (Fin 10) := literalFinset [1, 3, 4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_466 : Finset (Fin 10) := literalFinset [1, 4, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_556 : Finset (Fin 10) := literalFinset [2, 3, 5, 9] (by decide +kernel)
noncomputable def vertices_692 : Finset (Fin 10) := literalFinset [2, 4, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_916 : Finset (Fin 10) := literalFinset [2, 4, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_744 : Finset (Fin 10) := literalFinset [3, 5, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_259 : Finset (Fin 10) := literalFinset [0, 1, 8] (by decide +kernel)
noncomputable def vertices_13 : Finset (Fin 10) := literalFinset [0, 2, 3] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_73 : Finset (Fin 10) := literalFinset [0, 3, 6] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_22 : Finset (Fin 10) := literalFinset [1, 2, 4] (by decide +kernel)
noncomputable def vertices_262 : Finset (Fin 10) := literalFinset [1, 2, 8] (by decide +kernel)
noncomputable def vertices_58 : Finset (Fin 10) := literalFinset [1, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_74 : Finset (Fin 10) := literalFinset [1, 3, 6] (by decide +kernel)
noncomputable def vertices_210 : Finset (Fin 10) := literalFinset [1, 4, 6, 7] (by decide +kernel)
noncomputable def vertices_274 : Finset (Fin 10) := literalFinset [1, 4, 8] (by decide +kernel)
noncomputable def vertices_322 : Finset (Fin 10) := literalFinset [1, 6, 8] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_660 : Finset (Fin 10) := literalFinset [2, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_548 : Finset (Fin 10) := literalFinset [2, 5, 9] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_232 : Finset (Fin 10) := literalFinset [3, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_552 : Finset (Fin 10) := literalFinset [3, 5, 9] (by decide +kernel)
noncomputable def vertices_584 : Finset (Fin 10) := literalFinset [3, 6, 9] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_331, vertices_589, vertices_961, vertices_278, vertices_250, vertices_466, vertices_556, vertices_692, vertices_916, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_13, vertices_517, vertices_73, vertices_321, vertices_577, vertices_769, vertices_22, vertices_262, vertices_58, vertices_74, vertices_210, vertices_274, vertices_322, vertices_44, vertices_524, vertices_52, vertices_660, vertices_276, vertices_548, vertices_772, vertices_232, vertices_552, vertices_584, vertices_176, vertices_400, vertices_672, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_331), (false, vertices_589), (false, vertices_961), (true, vertices_210), (true, vertices_274), (true, vertices_660), (true, vertices_276), (true, vertices_548), (true, vertices_232), (true, vertices_552), (true, vertices_176), (true, vertices_400), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 16, 9, 18, 7, 19, 21, 22, 23]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 10 else
  if p.val = (false, vertices_775) then 14 else
  if p.val = (false, vertices_331) then 11 else
  if p.val = (false, vertices_589) then 12 else
  if p.val = (false, vertices_961) then 20 else
  if p.val = (true, vertices_210) then 15 else
  if p.val = (true, vertices_274) then 0 else
  if p.val = (true, vertices_660) then 17 else
  if p.val = (true, vertices_276) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_232) then 8 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_176) then 4 else
  if p.val = (true, vertices_400) then 5 else
  if p.val = (true, vertices_672) then 6 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 7 => Sum.inl 4
  | 8 => Sum.inr ⟨(true, vertices_232), by decide +kernel⟩
  | 9 => Sum.inl 2
  | 10 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_210), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(true, vertices_660), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inl 5
  | 20 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 3
  frame := ![1, 3, 6]
  vertex := 8
  face := Sum.inr ⟨vertices_660, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_660, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 5]
  vertex := 4
  face := Sum.inl ⟨vertices_250, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 5]
  vertex := 6
  face := Sum.inl ⟨vertices_250, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 3 → HeightRow boundary := ![row0, row1, row2]
noncomputable def pivot : Fin 3 → Fin 9 := ![1, 4, 0]
noncomputable def heightProof : HeightCertificate boundary 3 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_278, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .fundamental ![0, 1, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_278, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_250, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_466, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fromLargerFacet ![0, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_210, (by decide +kernel)⟩ ⟨vertices_466, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_210, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_250, by decide +kernel⟩ ![0, 2, 3, 5]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_556, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![1, 2, 4, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_556, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_692, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![1, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_692, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_916, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![1, 3, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_660, (by decide +kernel)⟩ ⟨vertices_916, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_744, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fromLargerFacet ![2, 4, 5, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_232, (by decide +kernel)⟩ ⟨vertices_744, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_232, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_250, by decide +kernel⟩ ![0, 2, 3, 5]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def coveringFacets : Fin 7 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6]
noncomputable def coveringProof (j : Fin 7) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (fun i => Fin.elim0 i)))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 3 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 7, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0070

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_multi_six_0071.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0071

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_775 : Finset (Fin 10) := literalFinset [0, 1, 2, 8, 9] (by decide +kernel)
noncomputable def vertices_331 : Finset (Fin 10) := literalFinset [0, 1, 3, 6, 8] (by decide +kernel)
noncomputable def vertices_589 : Finset (Fin 10) := literalFinset [0, 2, 3, 6, 9] (by decide +kernel)
noncomputable def vertices_961 : Finset (Fin 10) := literalFinset [0, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_278 : Finset (Fin 10) := literalFinset [1, 2, 4, 8] (by decide +kernel)
noncomputable def vertices_250 : Finset (Fin 10) := literalFinset [1, 3, 4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_466 : Finset (Fin 10) := literalFinset [1, 4, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_556 : Finset (Fin 10) := literalFinset [2, 3, 5, 9] (by decide +kernel)
noncomputable def vertices_436 : Finset (Fin 10) := literalFinset [2, 4, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_932 : Finset (Fin 10) := literalFinset [2, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_744 : Finset (Fin 10) := literalFinset [3, 5, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_259 : Finset (Fin 10) := literalFinset [0, 1, 8] (by decide +kernel)
noncomputable def vertices_13 : Finset (Fin 10) := literalFinset [0, 2, 3] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_73 : Finset (Fin 10) := literalFinset [0, 3, 6] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_22 : Finset (Fin 10) := literalFinset [1, 2, 4] (by decide +kernel)
noncomputable def vertices_262 : Finset (Fin 10) := literalFinset [1, 2, 8] (by decide +kernel)
noncomputable def vertices_58 : Finset (Fin 10) := literalFinset [1, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_74 : Finset (Fin 10) := literalFinset [1, 3, 6] (by decide +kernel)
noncomputable def vertices_210 : Finset (Fin 10) := literalFinset [1, 4, 6, 7] (by decide +kernel)
noncomputable def vertices_274 : Finset (Fin 10) := literalFinset [1, 4, 8] (by decide +kernel)
noncomputable def vertices_322 : Finset (Fin 10) := literalFinset [1, 6, 8] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_420 : Finset (Fin 10) := literalFinset [2, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_548 : Finset (Fin 10) := literalFinset [2, 5, 9] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_232 : Finset (Fin 10) := literalFinset [3, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_552 : Finset (Fin 10) := literalFinset [3, 5, 9] (by decide +kernel)
noncomputable def vertices_584 : Finset (Fin 10) := literalFinset [3, 6, 9] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_331, vertices_589, vertices_961, vertices_278, vertices_250, vertices_466, vertices_556, vertices_436, vertices_932, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_13, vertices_517, vertices_73, vertices_321, vertices_577, vertices_769, vertices_22, vertices_262, vertices_58, vertices_74, vertices_210, vertices_274, vertices_322, vertices_44, vertices_524, vertices_52, vertices_276, vertices_420, vertices_548, vertices_772, vertices_232, vertices_552, vertices_584, vertices_176, vertices_400, vertices_672, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_331), (false, vertices_589), (false, vertices_961), (true, vertices_210), (true, vertices_274), (true, vertices_276), (true, vertices_420), (true, vertices_548), (true, vertices_232), (true, vertices_552), (true, vertices_176), (true, vertices_400), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![9, 13, 16, 7, 18, 19, 21, 22, 23]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 10 else
  if p.val = (false, vertices_775) then 11 else
  if p.val = (false, vertices_331) then 12 else
  if p.val = (false, vertices_589) then 14 else
  if p.val = (false, vertices_961) then 20 else
  if p.val = (true, vertices_210) then 8 else
  if p.val = (true, vertices_274) then 0 else
  if p.val = (true, vertices_276) then 1 else
  if p.val = (true, vertices_420) then 15 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_232) then 17 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_176) then 4 else
  if p.val = (true, vertices_400) then 5 else
  if p.val = (true, vertices_672) then 6 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 7 => Sum.inl 3
  | 8 => Sum.inr ⟨(true, vertices_210), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_420), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(true, vertices_232), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 3
  frame := ![1, 4, 6]
  vertex := 7
  face := Sum.inr ⟨vertices_420, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_420, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 5]
  vertex := 4
  face := Sum.inl ⟨vertices_250, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 5]
  vertex := 6
  face := Sum.inl ⟨vertices_250, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 3 → HeightRow boundary := ![row0, row1, row2]
noncomputable def pivot : Fin 3 → Fin 9 := ![1, 4, 0]
noncomputable def heightProof : HeightCertificate boundary 3 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_278, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .fundamental ![0, 1, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_278, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_250, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_466, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fromLargerFacet ![0, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_210, (by decide +kernel)⟩ ⟨vertices_466, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_210, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_250, by decide +kernel⟩ ![0, 2, 3, 5]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_556, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![1, 2, 4, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_556, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_436, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![1, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_436, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_932, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![1, 4, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_420, (by decide +kernel)⟩ ⟨vertices_932, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_744, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fromLargerFacet ![2, 4, 5, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_232, (by decide +kernel)⟩ ⟨vertices_744, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_232, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_250, by decide +kernel⟩ ![0, 2, 3, 5]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def coveringFacets : Fin 7 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6]
noncomputable def coveringProof (j : Fin 7) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (fun i => Fin.elim0 i)))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 3 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 7, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0071

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_multi_six_0072.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0072

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_775 : Finset (Fin 10) := literalFinset [0, 1, 2, 8, 9] (by decide +kernel)
noncomputable def vertices_331 : Finset (Fin 10) := literalFinset [0, 1, 3, 6, 8] (by decide +kernel)
noncomputable def vertices_589 : Finset (Fin 10) := literalFinset [0, 2, 3, 6, 9] (by decide +kernel)
noncomputable def vertices_961 : Finset (Fin 10) := literalFinset [0, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_278 : Finset (Fin 10) := literalFinset [1, 2, 4, 8] (by decide +kernel)
noncomputable def vertices_250 : Finset (Fin 10) := literalFinset [1, 3, 4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_466 : Finset (Fin 10) := literalFinset [1, 4, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_556 : Finset (Fin 10) := literalFinset [2, 3, 5, 9] (by decide +kernel)
noncomputable def vertices_820 : Finset (Fin 10) := literalFinset [2, 4, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_744 : Finset (Fin 10) := literalFinset [3, 5, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_944 : Finset (Fin 10) := literalFinset [4, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_259 : Finset (Fin 10) := literalFinset [0, 1, 8] (by decide +kernel)
noncomputable def vertices_13 : Finset (Fin 10) := literalFinset [0, 2, 3] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_73 : Finset (Fin 10) := literalFinset [0, 3, 6] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_22 : Finset (Fin 10) := literalFinset [1, 2, 4] (by decide +kernel)
noncomputable def vertices_262 : Finset (Fin 10) := literalFinset [1, 2, 8] (by decide +kernel)
noncomputable def vertices_58 : Finset (Fin 10) := literalFinset [1, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_74 : Finset (Fin 10) := literalFinset [1, 3, 6] (by decide +kernel)
noncomputable def vertices_210 : Finset (Fin 10) := literalFinset [1, 4, 6, 7] (by decide +kernel)
noncomputable def vertices_274 : Finset (Fin 10) := literalFinset [1, 4, 8] (by decide +kernel)
noncomputable def vertices_322 : Finset (Fin 10) := literalFinset [1, 6, 8] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_548 : Finset (Fin 10) := literalFinset [2, 5, 9] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_232 : Finset (Fin 10) := literalFinset [3, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_552 : Finset (Fin 10) := literalFinset [3, 5, 9] (by decide +kernel)
noncomputable def vertices_584 : Finset (Fin 10) := literalFinset [3, 6, 9] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_816 : Finset (Fin 10) := literalFinset [4, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_331, vertices_589, vertices_961, vertices_278, vertices_250, vertices_466, vertices_556, vertices_820, vertices_744, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_13, vertices_517, vertices_73, vertices_321, vertices_577, vertices_769, vertices_22, vertices_262, vertices_58, vertices_74, vertices_210, vertices_274, vertices_322, vertices_44, vertices_524, vertices_52, vertices_276, vertices_548, vertices_772, vertices_232, vertices_552, vertices_584, vertices_176, vertices_816, vertices_400, vertices_672, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_331), (false, vertices_589), (false, vertices_961), (true, vertices_210), (true, vertices_274), (true, vertices_276), (true, vertices_548), (true, vertices_232), (true, vertices_552), (true, vertices_176), (true, vertices_816), (true, vertices_400), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![10, 7, 14, 16, 18, 19, 21, 22, 23]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 11 else
  if p.val = (false, vertices_775) then 8 else
  if p.val = (false, vertices_331) then 12 else
  if p.val = (false, vertices_589) then 9 else
  if p.val = (false, vertices_961) then 20 else
  if p.val = (true, vertices_210) then 13 else
  if p.val = (true, vertices_274) then 0 else
  if p.val = (true, vertices_276) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_232) then 15 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_176) then 4 else
  if p.val = (true, vertices_816) then 17 else
  if p.val = (true, vertices_400) then 5 else
  if p.val = (true, vertices_672) then 6 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 7 => Sum.inl 1
  | 8 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_210), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(true, vertices_232), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 3
  frame := ![3, 4, 7]
  vertex := 8
  face := Sum.inr ⟨vertices_816, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_816, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 5]
  vertex := 4
  face := Sum.inl ⟨vertices_250, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 5]
  vertex := 6
  face := Sum.inl ⟨vertices_250, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 3 → HeightRow boundary := ![row0, row1, row2]
noncomputable def pivot : Fin 3 → Fin 9 := ![7, 4, 0]
noncomputable def heightProof : HeightCertificate boundary 3 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_278, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .fundamental ![0, 1, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_278, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_250, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_466, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fromLargerFacet ![0, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_210, (by decide +kernel)⟩ ⟨vertices_466, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_210, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_250, by decide +kernel⟩ ![0, 2, 3, 5]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_556, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![1, 2, 4, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_556, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_820, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![1, 3, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_820, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_744, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fromLargerFacet ![2, 4, 5, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_232, (by decide +kernel)⟩ ⟨vertices_744, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_232, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_250, by decide +kernel⟩ ![0, 2, 3, 5]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_944, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![3, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_176, (by decide +kernel)⟩ ⟨vertices_944, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coveringFacets : Fin 7 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6]
noncomputable def coveringProof (j : Fin 7) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (fun i => Fin.elim0 i)))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 3 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 7, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0072

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_multi_six_0073.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0073

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_775 : Finset (Fin 10) := literalFinset [0, 1, 2, 8, 9] (by decide +kernel)
noncomputable def vertices_331 : Finset (Fin 10) := literalFinset [0, 1, 3, 6, 8] (by decide +kernel)
noncomputable def vertices_589 : Finset (Fin 10) := literalFinset [0, 2, 3, 6, 9] (by decide +kernel)
noncomputable def vertices_961 : Finset (Fin 10) := literalFinset [0, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_790 : Finset (Fin 10) := literalFinset [1, 2, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_250 : Finset (Fin 10) := literalFinset [1, 3, 4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_466 : Finset (Fin 10) := literalFinset [1, 4, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_556 : Finset (Fin 10) := literalFinset [2, 3, 5, 9] (by decide +kernel)
noncomputable def vertices_692 : Finset (Fin 10) := literalFinset [2, 4, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_744 : Finset (Fin 10) := literalFinset [3, 5, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_912 : Finset (Fin 10) := literalFinset [4, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_259 : Finset (Fin 10) := literalFinset [0, 1, 8] (by decide +kernel)
noncomputable def vertices_13 : Finset (Fin 10) := literalFinset [0, 2, 3] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_73 : Finset (Fin 10) := literalFinset [0, 3, 6] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_22 : Finset (Fin 10) := literalFinset [1, 2, 4] (by decide +kernel)
noncomputable def vertices_774 : Finset (Fin 10) := literalFinset [1, 2, 8, 9] (by decide +kernel)
noncomputable def vertices_58 : Finset (Fin 10) := literalFinset [1, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_74 : Finset (Fin 10) := literalFinset [1, 3, 6] (by decide +kernel)
noncomputable def vertices_210 : Finset (Fin 10) := literalFinset [1, 4, 6, 7] (by decide +kernel)
noncomputable def vertices_274 : Finset (Fin 10) := literalFinset [1, 4, 8] (by decide +kernel)
noncomputable def vertices_322 : Finset (Fin 10) := literalFinset [1, 6, 8] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_532 : Finset (Fin 10) := literalFinset [2, 4, 9] (by decide +kernel)
noncomputable def vertices_548 : Finset (Fin 10) := literalFinset [2, 5, 9] (by decide +kernel)
noncomputable def vertices_232 : Finset (Fin 10) := literalFinset [3, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_552 : Finset (Fin 10) := literalFinset [3, 5, 9] (by decide +kernel)
noncomputable def vertices_584 : Finset (Fin 10) := literalFinset [3, 6, 9] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_784 : Finset (Fin 10) := literalFinset [4, 8, 9] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_331, vertices_589, vertices_961, vertices_790, vertices_250, vertices_466, vertices_556, vertices_692, vertices_744, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_13, vertices_517, vertices_73, vertices_321, vertices_577, vertices_769, vertices_22, vertices_774, vertices_58, vertices_74, vertices_210, vertices_274, vertices_322, vertices_44, vertices_524, vertices_52, vertices_532, vertices_548, vertices_232, vertices_552, vertices_584, vertices_176, vertices_400, vertices_656, vertices_784, vertices_672, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_331), (false, vertices_589), (false, vertices_961), (true, vertices_210), (true, vertices_274), (true, vertices_532), (true, vertices_548), (true, vertices_232), (true, vertices_552), (true, vertices_176), (true, vertices_400), (true, vertices_656), (true, vertices_784), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![12, 9, 16, 18, 19, 20, 22, 23, 24]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_775) then 10 else
  if p.val = (false, vertices_331) then 14 else
  if p.val = (false, vertices_589) then 11 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_210) then 15 else
  if p.val = (true, vertices_274) then 0 else
  if p.val = (true, vertices_532) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_232) then 17 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_176) then 4 else
  if p.val = (true, vertices_400) then 5 else
  if p.val = (true, vertices_656) then 6 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_672) then 8 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_210), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(true, vertices_232), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 3
  frame := ![0, 1, 7]
  vertex := 8
  face := Sum.inr ⟨vertices_774, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_774, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 3, 4, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_692, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_692, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 5]
  vertex := 4
  face := Sum.inl ⟨vertices_250, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 5]
  vertex := 6
  face := Sum.inl ⟨vertices_250, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![7, 1, 4, 0]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_790, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_790, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_250, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_466, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fromLargerFacet ![0, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_210, (by decide +kernel)⟩ ⟨vertices_466, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_210, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_250, by decide +kernel⟩ ![0, 2, 3, 5]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_556, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![1, 2, 4, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_556, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_692, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![1, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_692, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_744, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fromLargerFacet ![2, 4, 5, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_232, (by decide +kernel)⟩ ⟨vertices_744, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_232, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_250, by decide +kernel⟩ ![0, 2, 3, 5]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_912, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![3, 6, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_400, (by decide +kernel)⟩ ⟨vertices_912, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coveringFacets : Fin 7 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6]
noncomputable def coveringProof (j : Fin 7) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (fun i => Fin.elim0 i)))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 7, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0073

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_multi_six_0074.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0074

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_775 : Finset (Fin 10) := literalFinset [0, 1, 2, 8, 9] (by decide +kernel)
noncomputable def vertices_331 : Finset (Fin 10) := literalFinset [0, 1, 3, 6, 8] (by decide +kernel)
noncomputable def vertices_589 : Finset (Fin 10) := literalFinset [0, 2, 3, 6, 9] (by decide +kernel)
noncomputable def vertices_961 : Finset (Fin 10) := literalFinset [0, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_790 : Finset (Fin 10) := literalFinset [1, 2, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_250 : Finset (Fin 10) := literalFinset [1, 3, 4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_466 : Finset (Fin 10) := literalFinset [1, 4, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_556 : Finset (Fin 10) := literalFinset [2, 3, 5, 9] (by decide +kernel)
noncomputable def vertices_564 : Finset (Fin 10) := literalFinset [2, 4, 5, 9] (by decide +kernel)
noncomputable def vertices_744 : Finset (Fin 10) := literalFinset [3, 5, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_944 : Finset (Fin 10) := literalFinset [4, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_259 : Finset (Fin 10) := literalFinset [0, 1, 8] (by decide +kernel)
noncomputable def vertices_13 : Finset (Fin 10) := literalFinset [0, 2, 3] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_73 : Finset (Fin 10) := literalFinset [0, 3, 6] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_22 : Finset (Fin 10) := literalFinset [1, 2, 4] (by decide +kernel)
noncomputable def vertices_774 : Finset (Fin 10) := literalFinset [1, 2, 8, 9] (by decide +kernel)
noncomputable def vertices_58 : Finset (Fin 10) := literalFinset [1, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_74 : Finset (Fin 10) := literalFinset [1, 3, 6] (by decide +kernel)
noncomputable def vertices_210 : Finset (Fin 10) := literalFinset [1, 4, 6, 7] (by decide +kernel)
noncomputable def vertices_274 : Finset (Fin 10) := literalFinset [1, 4, 8] (by decide +kernel)
noncomputable def vertices_322 : Finset (Fin 10) := literalFinset [1, 6, 8] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_532 : Finset (Fin 10) := literalFinset [2, 4, 9] (by decide +kernel)
noncomputable def vertices_548 : Finset (Fin 10) := literalFinset [2, 5, 9] (by decide +kernel)
noncomputable def vertices_232 : Finset (Fin 10) := literalFinset [3, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_552 : Finset (Fin 10) := literalFinset [3, 5, 9] (by decide +kernel)
noncomputable def vertices_584 : Finset (Fin 10) := literalFinset [3, 6, 9] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_784 : Finset (Fin 10) := literalFinset [4, 8, 9] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_331, vertices_589, vertices_961, vertices_790, vertices_250, vertices_466, vertices_556, vertices_564, vertices_744, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_13, vertices_517, vertices_73, vertices_321, vertices_577, vertices_769, vertices_22, vertices_774, vertices_58, vertices_74, vertices_210, vertices_274, vertices_322, vertices_44, vertices_524, vertices_52, vertices_532, vertices_548, vertices_232, vertices_552, vertices_584, vertices_176, vertices_560, vertices_400, vertices_784, vertices_672, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_331), (false, vertices_589), (false, vertices_961), (true, vertices_210), (true, vertices_274), (true, vertices_532), (true, vertices_548), (true, vertices_232), (true, vertices_552), (true, vertices_176), (true, vertices_560), (true, vertices_400), (true, vertices_784), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![12, 9, 16, 18, 19, 20, 22, 23, 24]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_775) then 10 else
  if p.val = (false, vertices_331) then 14 else
  if p.val = (false, vertices_589) then 11 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_210) then 15 else
  if p.val = (true, vertices_274) then 0 else
  if p.val = (true, vertices_532) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_232) then 17 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_176) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_400) then 6 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_672) then 8 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_210), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(true, vertices_232), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 3
  frame := ![0, 1, 7]
  vertex := 8
  face := Sum.inr ⟨vertices_774, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_774, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![3, 4, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_944, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_176, (by decide +kernel)⟩ ⟨vertices_944, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 5]
  vertex := 4
  face := Sum.inl ⟨vertices_250, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 5]
  vertex := 6
  face := Sum.inl ⟨vertices_250, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![1, 7, 4, 0]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_790, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_790, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_250, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_466, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fromLargerFacet ![0, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_210, (by decide +kernel)⟩ ⟨vertices_466, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_210, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_250, by decide +kernel⟩ ![0, 2, 3, 5]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_556, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![1, 2, 4, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_556, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_564, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![1, 3, 4, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_564, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_744, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fromLargerFacet ![2, 4, 5, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_232, (by decide +kernel)⟩ ⟨vertices_744, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_232, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_250, by decide +kernel⟩ ![0, 2, 3, 5]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_944, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![3, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_176, (by decide +kernel)⟩ ⟨vertices_944, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coveringFacets : Fin 7 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6]
noncomputable def coveringProof (j : Fin 7) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (fun i => Fin.elim0 i)))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 7, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0074

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_multi_six_0075.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0075

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_583 : Finset (Fin 10) := literalFinset [0, 1, 2, 6, 9] (by decide +kernel)
noncomputable def vertices_203 : Finset (Fin 10) := literalFinset [0, 1, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_781 : Finset (Fin 10) := literalFinset [0, 2, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_393 : Finset (Fin 10) := literalFinset [0, 3, 7, 8] (by decide +kernel)
noncomputable def vertices_961 : Finset (Fin 10) := literalFinset [0, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_790 : Finset (Fin 10) := literalFinset [1, 2, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_250 : Finset (Fin 10) := literalFinset [1, 3, 4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_850 : Finset (Fin 10) := literalFinset [1, 4, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_428 : Finset (Fin 10) := literalFinset [2, 3, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_308 : Finset (Fin 10) := literalFinset [2, 4, 5, 8] (by decide +kernel)
noncomputable def vertices_496 : Finset (Fin 10) := literalFinset [4, 5, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_67 : Finset (Fin 10) := literalFinset [0, 1, 6] (by decide +kernel)
noncomputable def vertices_13 : Finset (Fin 10) := literalFinset [0, 2, 3] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_265 : Finset (Fin 10) := literalFinset [0, 3, 8] (by decide +kernel)
noncomputable def vertices_193 : Finset (Fin 10) := literalFinset [0, 6, 7] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_385 : Finset (Fin 10) := literalFinset [0, 7, 8] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_22 : Finset (Fin 10) := literalFinset [1, 2, 4] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_58 : Finset (Fin 10) := literalFinset [1, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_202 : Finset (Fin 10) := literalFinset [1, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_82 : Finset (Fin 10) := literalFinset [1, 4, 6] (by decide +kernel)
noncomputable def vertices_786 : Finset (Fin 10) := literalFinset [1, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_268 : Finset (Fin 10) := literalFinset [2, 3, 8] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_292 : Finset (Fin 10) := literalFinset [2, 5, 8] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_392 : Finset (Fin 10) := literalFinset [3, 7, 8] (by decide +kernel)
noncomputable def vertices_240 : Finset (Fin 10) := literalFinset [4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_203, vertices_781, vertices_393, vertices_961, vertices_790, vertices_250, vertices_850, vertices_428, vertices_308, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_517, vertices_137, vertices_265, vertices_193, vertices_577, vertices_385, vertices_769, vertices_22, vertices_518, vertices_58, vertices_202, vertices_82, vertices_786, vertices_578, vertices_44, vertices_268, vertices_52, vertices_276, vertices_292, vertices_772, vertices_168, vertices_392, vertices_240, vertices_304, vertices_336, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_203), (false, vertices_781), (false, vertices_393), (false, vertices_961), (true, vertices_82), (true, vertices_786), (true, vertices_276), (true, vertices_292), (true, vertices_168), (true, vertices_240), (true, vertices_304), (true, vertices_336), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![11, 8, 15, 16, 18, 19, 21, 22, 23]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_583) then 9 else
  if p.val = (false, vertices_203) then 13 else
  if p.val = (false, vertices_781) then 10 else
  if p.val = (false, vertices_393) then 0 else
  if p.val = (false, vertices_961) then 20 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_786) then 14 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_292) then 3 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_240) then 17 else
  if p.val = (true, vertices_304) then 5 else
  if p.val = (true, vertices_336) then 6 else
  if p.val = (true, vertices_416) then 7 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_393), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 8 => Sum.inl 1
  | 9 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_786), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 3
  frame := ![0, 3, 7]
  vertex := 8
  face := Sum.inr ⟨vertices_786, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_786, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 4, 6]
  vertex := 7
  face := Sum.inl ⟨vertices_428, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_428, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 5]
  vertex := 4
  face := Sum.inl ⟨vertices_250, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 5]
  vertex := 6
  face := Sum.inl ⟨vertices_250, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![8, 1, 4, 0]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_790, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_790, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_250, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_850, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_82, (by decide +kernel)⟩ ⟨vertices_850, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_428, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 2, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_428, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_308, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![1, 3, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_308, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_496, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fromLargerFacet ![3, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_240, (by decide +kernel)⟩ ⟨vertices_496, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_240, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_250, by decide +kernel⟩ ![0, 2, 3, 5]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def coveringFacets : Fin 6 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5]
noncomputable def coveringProof (j : Fin 6) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (fun i => Fin.elim0 i))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 6, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0075

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_multi_six_0076.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0076

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_583 : Finset (Fin 10) := literalFinset [0, 1, 2, 6, 9] (by decide +kernel)
noncomputable def vertices_203 : Finset (Fin 10) := literalFinset [0, 1, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_653 : Finset (Fin 10) := literalFinset [0, 2, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_961 : Finset (Fin 10) := literalFinset [0, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_790 : Finset (Fin 10) := literalFinset [1, 2, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_250 : Finset (Fin 10) := literalFinset [1, 3, 4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_850 : Finset (Fin 10) := literalFinset [1, 4, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_428 : Finset (Fin 10) := literalFinset [2, 3, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_308 : Finset (Fin 10) := literalFinset [2, 4, 5, 8] (by decide +kernel)
noncomputable def vertices_900 : Finset (Fin 10) := literalFinset [2, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_496 : Finset (Fin 10) := literalFinset [4, 5, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_67 : Finset (Fin 10) := literalFinset [0, 1, 6] (by decide +kernel)
noncomputable def vertices_13 : Finset (Fin 10) := literalFinset [0, 2, 3] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_193 : Finset (Fin 10) := literalFinset [0, 6, 7] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_22 : Finset (Fin 10) := literalFinset [1, 2, 4] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_58 : Finset (Fin 10) := literalFinset [1, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_202 : Finset (Fin 10) := literalFinset [1, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_82 : Finset (Fin 10) := literalFinset [1, 4, 6] (by decide +kernel)
noncomputable def vertices_786 : Finset (Fin 10) := literalFinset [1, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_140 : Finset (Fin 10) := literalFinset [2, 3, 7] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_292 : Finset (Fin 10) := literalFinset [2, 5, 8] (by decide +kernel)
noncomputable def vertices_388 : Finset (Fin 10) := literalFinset [2, 7, 8] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_240 : Finset (Fin 10) := literalFinset [4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_203, vertices_653, vertices_961, vertices_790, vertices_250, vertices_850, vertices_428, vertices_308, vertices_900, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_517, vertices_137, vertices_193, vertices_577, vertices_641, vertices_22, vertices_518, vertices_58, vertices_202, vertices_82, vertices_786, vertices_578, vertices_44, vertices_140, vertices_52, vertices_276, vertices_292, vertices_388, vertices_644, vertices_772, vertices_168, vertices_240, vertices_304, vertices_336, vertices_416, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_203), (false, vertices_653), (false, vertices_961), (true, vertices_82), (true, vertices_786), (true, vertices_276), (true, vertices_292), (true, vertices_388), (true, vertices_772), (true, vertices_168), (true, vertices_240), (true, vertices_304), (true, vertices_336), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![12, 9, 16, 17, 19, 20, 22, 23, 24]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_583) then 10 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_653) then 11 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_786) then 15 else
  if p.val = (true, vertices_276) then 1 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_388) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_240) then 18 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_416) then 8 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_786), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 3
  frame := ![0, 3, 7]
  vertex := 8
  face := Sum.inr ⟨vertices_786, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_786, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 4, 6]
  vertex := 7
  face := Sum.inl ⟨vertices_428, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_428, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 5]
  vertex := 4
  face := Sum.inl ⟨vertices_250, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 5]
  vertex := 6
  face := Sum.inl ⟨vertices_250, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![8, 1, 4, 0]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_790, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_790, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_250, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_850, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_82, (by decide +kernel)⟩ ⟨vertices_850, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_428, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 2, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_428, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_308, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![1, 3, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_308, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_900, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![1, 6, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_388, (by decide +kernel)⟩ ⟨vertices_900, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_496, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fromLargerFacet ![3, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_240, (by decide +kernel)⟩ ⟨vertices_496, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_240, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_250, by decide +kernel⟩ ![0, 2, 3, 5]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def coveringFacets : Fin 7 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6]
noncomputable def coveringProof (j : Fin 7) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (fun i => Fin.elim0 i)))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 7, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0076

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_multi_six_0077.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0077

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_583 : Finset (Fin 10) := literalFinset [0, 1, 2, 6, 9] (by decide +kernel)
noncomputable def vertices_203 : Finset (Fin 10) := literalFinset [0, 1, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_653 : Finset (Fin 10) := literalFinset [0, 2, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_961 : Finset (Fin 10) := literalFinset [0, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_790 : Finset (Fin 10) := literalFinset [1, 2, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_250 : Finset (Fin 10) := literalFinset [1, 3, 4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_850 : Finset (Fin 10) := literalFinset [1, 4, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_172 : Finset (Fin 10) := literalFinset [2, 3, 5, 7] (by decide +kernel)
noncomputable def vertices_308 : Finset (Fin 10) := literalFinset [2, 4, 5, 8] (by decide +kernel)
noncomputable def vertices_932 : Finset (Fin 10) := literalFinset [2, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_496 : Finset (Fin 10) := literalFinset [4, 5, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_67 : Finset (Fin 10) := literalFinset [0, 1, 6] (by decide +kernel)
noncomputable def vertices_13 : Finset (Fin 10) := literalFinset [0, 2, 3] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_193 : Finset (Fin 10) := literalFinset [0, 6, 7] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_22 : Finset (Fin 10) := literalFinset [1, 2, 4] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_58 : Finset (Fin 10) := literalFinset [1, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_202 : Finset (Fin 10) := literalFinset [1, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_82 : Finset (Fin 10) := literalFinset [1, 4, 6] (by decide +kernel)
noncomputable def vertices_786 : Finset (Fin 10) := literalFinset [1, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_140 : Finset (Fin 10) := literalFinset [2, 3, 7] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_164 : Finset (Fin 10) := literalFinset [2, 5, 7] (by decide +kernel)
noncomputable def vertices_292 : Finset (Fin 10) := literalFinset [2, 5, 8] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_240 : Finset (Fin 10) := literalFinset [4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_203, vertices_653, vertices_961, vertices_790, vertices_250, vertices_850, vertices_172, vertices_308, vertices_932, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_517, vertices_137, vertices_193, vertices_577, vertices_641, vertices_22, vertices_518, vertices_58, vertices_202, vertices_82, vertices_786, vertices_578, vertices_44, vertices_140, vertices_52, vertices_276, vertices_164, vertices_292, vertices_644, vertices_772, vertices_168, vertices_240, vertices_304, vertices_336, vertices_416, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_203), (false, vertices_653), (false, vertices_961), (true, vertices_82), (true, vertices_786), (true, vertices_276), (true, vertices_164), (true, vertices_292), (true, vertices_772), (true, vertices_168), (true, vertices_240), (true, vertices_304), (true, vertices_336), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![12, 9, 16, 17, 19, 20, 22, 23, 24]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_583) then 10 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_653) then 11 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_786) then 15 else
  if p.val = (true, vertices_276) then 1 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_292) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_240) then 18 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_416) then 8 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_786), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 4, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_932, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_164, (by decide +kernel)⟩ ⟨vertices_932, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 3
  frame := ![0, 3, 7]
  vertex := 8
  face := Sum.inr ⟨vertices_786, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_786, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 5]
  vertex := 4
  face := Sum.inl ⟨vertices_250, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 5]
  vertex := 6
  face := Sum.inl ⟨vertices_250, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![1, 7, 4, 0]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_790, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_790, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_250, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_850, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_82, (by decide +kernel)⟩ ⟨vertices_850, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_172, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![1, 2, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_172, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_308, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![1, 3, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_308, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_932, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![1, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_164, (by decide +kernel)⟩ ⟨vertices_932, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_496, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fromLargerFacet ![3, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_240, (by decide +kernel)⟩ ⟨vertices_496, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_240, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_250, by decide +kernel⟩ ![0, 2, 3, 5]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_250, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def coveringFacets : Fin 7 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6]
noncomputable def coveringProof (j : Fin 7) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (fun i => Fin.elim0 i)))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 7, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0077

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_multi_six_0078.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0078

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_583 : Finset (Fin 10) := literalFinset [0, 1, 2, 6, 9] (by decide +kernel)
noncomputable def vertices_203 : Finset (Fin 10) := literalFinset [0, 1, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_533 : Finset (Fin 10) := literalFinset [0, 2, 4, 9] (by decide +kernel)
noncomputable def vertices_249 : Finset (Fin 10) := literalFinset [0, 3, 4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_849 : Finset (Fin 10) := literalFinset [0, 4, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_654 : Finset (Fin 10) := literalFinset [1, 2, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_962 : Finset (Fin 10) := literalFinset [1, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_684 : Finset (Fin 10) := literalFinset [2, 3, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_820 : Finset (Fin 10) := literalFinset [2, 4, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_496 : Finset (Fin 10) := literalFinset [4, 5, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_928 : Finset (Fin 10) := literalFinset [5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_67 : Finset (Fin 10) := literalFinset [0, 1, 6] (by decide +kernel)
noncomputable def vertices_21 : Finset (Fin 10) := literalFinset [0, 2, 4] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_57 : Finset (Fin 10) := literalFinset [0, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_201 : Finset (Fin 10) := literalFinset [0, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_529 : Finset (Fin 10) := literalFinset [0, 4, 9] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_138 : Finset (Fin 10) := literalFinset [1, 3, 7] (by decide +kernel)
noncomputable def vertices_194 : Finset (Fin 10) := literalFinset [1, 6, 7] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_652 : Finset (Fin 10) := literalFinset [2, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_532 : Finset (Fin 10) := literalFinset [2, 4, 9] (by decide +kernel)
noncomputable def vertices_548 : Finset (Fin 10) := literalFinset [2, 5, 9] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_240 : Finset (Fin 10) := literalFinset [4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_784 : Finset (Fin 10) := literalFinset [4, 8, 9] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_203, vertices_533, vertices_249, vertices_849, vertices_654, vertices_962, vertices_684, vertices_820, vertices_496, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_517, vertices_57, vertices_201, vertices_81, vertices_529, vertices_577, vertices_14, vertices_518, vertices_138, vertices_194, vertices_578, vertices_642, vertices_44, vertices_652, vertices_52, vertices_532, vertices_548, vertices_168, vertices_240, vertices_304, vertices_336, vertices_784, vertices_416, vertices_672, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_203), (false, vertices_533), (false, vertices_249), (false, vertices_849), (true, vertices_642), (true, vertices_652), (true, vertices_548), (true, vertices_304), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![9, 11, 13, 16, 19, 20, 21, 22, 23]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_583) then 10 else
  if p.val = (false, vertices_203) then 15 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_249) then 17 else
  if p.val = (false, vertices_849) then 18 else
  if p.val = (true, vertices_642) then 1 else
  if p.val = (true, vertices_652) then 12 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_304) then 3 else
  if p.val = (true, vertices_416) then 4 else
  if p.val = (true, vertices_672) then 5 else
  if p.val = (true, vertices_800) then 6 else
  if p.val = (true, vertices_448) then 7 else
  if p.val = (true, vertices_896) then 8 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(true, vertices_652), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_249), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 3
  frame := ![1, 2, 6]
  vertex := 8
  face := Sum.inr ⟨vertices_652, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_652, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 5, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_962, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_194, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 3
  frame := ![3, 4, 5]
  vertex := 6
  face := Sum.inr ⟨vertices_240, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_240, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 3, 4, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_820, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_820, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![2, 0, 5, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_654, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_654, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_962, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_194, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_684, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![1, 2, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_684, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_820, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 3, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_820, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_496, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![3, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_240, (by decide +kernel)⟩ ⟨vertices_496, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_928, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![4, 6, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_416, (by decide +kernel)⟩ ⟨vertices_928, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coveringFacets : Fin 6 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5]
noncomputable def coveringProof (j : Fin 6) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (fun i => Fin.elim0 i))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 6, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0078

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_multi_six_0079.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0079

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_583 : Finset (Fin 10) := literalFinset [0, 1, 2, 6, 9] (by decide +kernel)
noncomputable def vertices_203 : Finset (Fin 10) := literalFinset [0, 1, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_341 : Finset (Fin 10) := literalFinset [0, 2, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_249 : Finset (Fin 10) := literalFinset [0, 3, 4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_654 : Finset (Fin 10) := literalFinset [1, 2, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_962 : Finset (Fin 10) := literalFinset [1, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_684 : Finset (Fin 10) := literalFinset [2, 3, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_820 : Finset (Fin 10) := literalFinset [2, 4, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_836 : Finset (Fin 10) := literalFinset [2, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_496 : Finset (Fin 10) := literalFinset [4, 5, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_928 : Finset (Fin 10) := literalFinset [5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_67 : Finset (Fin 10) := literalFinset [0, 1, 6] (by decide +kernel)
noncomputable def vertices_21 : Finset (Fin 10) := literalFinset [0, 2, 4] (by decide +kernel)
noncomputable def vertices_69 : Finset (Fin 10) := literalFinset [0, 2, 6] (by decide +kernel)
noncomputable def vertices_57 : Finset (Fin 10) := literalFinset [0, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_201 : Finset (Fin 10) := literalFinset [0, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_138 : Finset (Fin 10) := literalFinset [1, 3, 7] (by decide +kernel)
noncomputable def vertices_194 : Finset (Fin 10) := literalFinset [1, 6, 7] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_652 : Finset (Fin 10) := literalFinset [2, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_548 : Finset (Fin 10) := literalFinset [2, 5, 9] (by decide +kernel)
noncomputable def vertices_324 : Finset (Fin 10) := literalFinset [2, 6, 8] (by decide +kernel)
noncomputable def vertices_580 : Finset (Fin 10) := literalFinset [2, 6, 9] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_240 : Finset (Fin 10) := literalFinset [4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_203, vertices_341, vertices_249, vertices_654, vertices_962, vertices_684, vertices_820, vertices_836, vertices_496, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_57, vertices_201, vertices_81, vertices_14, vertices_518, vertices_138, vertices_194, vertices_578, vertices_642, vertices_44, vertices_652, vertices_52, vertices_276, vertices_548, vertices_324, vertices_580, vertices_772, vertices_168, vertices_240, vertices_304, vertices_336, vertices_416, vertices_672, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_203), (false, vertices_341), (false, vertices_249), (true, vertices_642), (true, vertices_652), (true, vertices_548), (true, vertices_772), (true, vertices_304), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_448), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![10, 12, 15, 18, 20, 21, 22, 23, 24]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_583) then 11 else
  if p.val = (false, vertices_203) then 17 else
  if p.val = (false, vertices_341) then 13 else
  if p.val = (false, vertices_249) then 19 else
  if p.val = (true, vertices_642) then 0 else
  if p.val = (true, vertices_652) then 14 else
  if p.val = (true, vertices_548) then 1 else
  if p.val = (true, vertices_772) then 2 else
  if p.val = (true, vertices_304) then 3 else
  if p.val = (true, vertices_416) then 4 else
  if p.val = (true, vertices_672) then 5 else
  if p.val = (true, vertices_800) then 6 else
  if p.val = (true, vertices_448) then 7 else
  if p.val = (true, vertices_832) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_652), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_249), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 3
  frame := ![1, 2, 6]
  vertex := 8
  face := Sum.inr ⟨vertices_652, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_652, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 5, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_962, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_194, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 3
  frame := ![3, 4, 5]
  vertex := 6
  face := Sum.inr ⟨vertices_240, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_240, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 3, 4, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_820, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_820, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![2, 0, 5, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_654, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_654, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_962, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_194, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_684, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![1, 2, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_684, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_820, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 3, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_820, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_836, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![1, 5, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_324, (by decide +kernel)⟩ ⟨vertices_836, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_496, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![3, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_240, (by decide +kernel)⟩ ⟨vertices_496, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_928, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![4, 6, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_416, (by decide +kernel)⟩ ⟨vertices_928, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coveringFacets : Fin 7 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6]
noncomputable def coveringProof (j : Fin 7) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (fun i => Fin.elim0 i)))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 7, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0079

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_multi_six_0080.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0080

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_775 : Finset (Fin 10) := literalFinset [0, 1, 2, 8, 9] (by decide +kernel)
noncomputable def vertices_203 : Finset (Fin 10) := literalFinset [0, 1, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_323 : Finset (Fin 10) := literalFinset [0, 1, 6, 8] (by decide +kernel)
noncomputable def vertices_341 : Finset (Fin 10) := literalFinset [0, 2, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_249 : Finset (Fin 10) := literalFinset [0, 3, 4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_654 : Finset (Fin 10) := literalFinset [1, 2, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_962 : Finset (Fin 10) := literalFinset [1, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_684 : Finset (Fin 10) := literalFinset [2, 3, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_820 : Finset (Fin 10) := literalFinset [2, 4, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_496 : Finset (Fin 10) := literalFinset [4, 5, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_928 : Finset (Fin 10) := literalFinset [5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_67 : Finset (Fin 10) := literalFinset [0, 1, 6] (by decide +kernel)
noncomputable def vertices_259 : Finset (Fin 10) := literalFinset [0, 1, 8] (by decide +kernel)
noncomputable def vertices_21 : Finset (Fin 10) := literalFinset [0, 2, 4] (by decide +kernel)
noncomputable def vertices_261 : Finset (Fin 10) := literalFinset [0, 2, 8] (by decide +kernel)
noncomputable def vertices_57 : Finset (Fin 10) := literalFinset [0, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_201 : Finset (Fin 10) := literalFinset [0, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_138 : Finset (Fin 10) := literalFinset [1, 3, 7] (by decide +kernel)
noncomputable def vertices_194 : Finset (Fin 10) := literalFinset [1, 6, 7] (by decide +kernel)
noncomputable def vertices_322 : Finset (Fin 10) := literalFinset [1, 6, 8] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_652 : Finset (Fin 10) := literalFinset [2, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_548 : Finset (Fin 10) := literalFinset [2, 5, 9] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_240 : Finset (Fin 10) := literalFinset [4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_203, vertices_323, vertices_341, vertices_249, vertices_654, vertices_962, vertices_684, vertices_820, vertices_496, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_261, vertices_57, vertices_201, vertices_81, vertices_321, vertices_14, vertices_518, vertices_138, vertices_194, vertices_322, vertices_642, vertices_770, vertices_44, vertices_652, vertices_52, vertices_276, vertices_548, vertices_772, vertices_168, vertices_240, vertices_304, vertices_336, vertices_416, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_203), (false, vertices_323), (false, vertices_341), (false, vertices_249), (true, vertices_642), (true, vertices_652), (true, vertices_548), (true, vertices_304), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![9, 11, 14, 17, 19, 20, 21, 22, 23]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_775) then 10 else
  if p.val = (false, vertices_203) then 16 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_341) then 12 else
  if p.val = (false, vertices_249) then 18 else
  if p.val = (true, vertices_642) then 1 else
  if p.val = (true, vertices_652) then 13 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_304) then 3 else
  if p.val = (true, vertices_416) then 4 else
  if p.val = (true, vertices_672) then 5 else
  if p.val = (true, vertices_800) then 6 else
  if p.val = (true, vertices_448) then 7 else
  if p.val = (true, vertices_896) then 8 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_652), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_249), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 3
  frame := ![1, 2, 6]
  vertex := 8
  face := Sum.inr ⟨vertices_652, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_652, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 5, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_962, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_194, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 3
  frame := ![3, 4, 5]
  vertex := 6
  face := Sum.inr ⟨vertices_240, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_240, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 3, 4, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_820, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_820, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![2, 0, 5, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_654, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_654, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_962, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_194, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_684, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![1, 2, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_684, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_820, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 3, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_820, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_496, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![3, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_240, (by decide +kernel)⟩ ⟨vertices_496, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_928, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![4, 6, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_416, (by decide +kernel)⟩ ⟨vertices_928, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coveringFacets : Fin 6 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5]
noncomputable def coveringProof (j : Fin 6) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (fun i => Fin.elim0 i))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 6, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0080

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_multi_six_0081.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0081

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_327 : Finset (Fin 10) := literalFinset [0, 1, 2, 6, 8] (by decide +kernel)
noncomputable def vertices_779 : Finset (Fin 10) := literalFinset [0, 1, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_341 : Finset (Fin 10) := literalFinset [0, 2, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_681 : Finset (Fin 10) := literalFinset [0, 3, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_817 : Finset (Fin 10) := literalFinset [0, 4, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_206 : Finset (Fin 10) := literalFinset [1, 2, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_650 : Finset (Fin 10) := literalFinset [1, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_962 : Finset (Fin 10) := literalFinset [1, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_252 : Finset (Fin 10) := literalFinset [2, 3, 4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_496 : Finset (Fin 10) := literalFinset [4, 5, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_928 : Finset (Fin 10) := literalFinset [5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_259 : Finset (Fin 10) := literalFinset [0, 1, 8] (by decide +kernel)
noncomputable def vertices_21 : Finset (Fin 10) := literalFinset [0, 2, 4] (by decide +kernel)
noncomputable def vertices_325 : Finset (Fin 10) := literalFinset [0, 2, 6, 8] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_521 : Finset (Fin 10) := literalFinset [0, 3, 9] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_273 : Finset (Fin 10) := literalFinset [0, 4, 8] (by decide +kernel)
noncomputable def vertices_545 : Finset (Fin 10) := literalFinset [0, 5, 9] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_70 : Finset (Fin 10) := literalFinset [1, 2, 6] (by decide +kernel)
noncomputable def vertices_138 : Finset (Fin 10) := literalFinset [1, 3, 7] (by decide +kernel)
noncomputable def vertices_522 : Finset (Fin 10) := literalFinset [1, 3, 9] (by decide +kernel)
noncomputable def vertices_194 : Finset (Fin 10) := literalFinset [1, 6, 7] (by decide +kernel)
noncomputable def vertices_322 : Finset (Fin 10) := literalFinset [1, 6, 8] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_60 : Finset (Fin 10) := literalFinset [2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_204 : Finset (Fin 10) := literalFinset [2, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_648 : Finset (Fin 10) := literalFinset [3, 7, 9] (by decide +kernel)
noncomputable def vertices_240 : Finset (Fin 10) := literalFinset [4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_779, vertices_341, vertices_681, vertices_817, vertices_206, vertices_650, vertices_962, vertices_252, vertices_496, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_325, vertices_41, vertices_521, vertices_49, vertices_273, vertices_545, vertices_769, vertices_14, vertices_70, vertices_138, vertices_522, vertices_194, vertices_322, vertices_642, vertices_770, vertices_60, vertices_204, vertices_84, vertices_168, vertices_648, vertices_240, vertices_304, vertices_336, vertices_416, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_779), (false, vertices_341), (false, vertices_681), (false, vertices_817), (true, vertices_138), (true, vertices_194), (true, vertices_642), (true, vertices_204), (true, vertices_240), (true, vertices_416), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![6, 12, 8, 15, 18, 19, 20, 21, 22]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 9 else
  if p.val = (false, vertices_327) then 13 else
  if p.val = (false, vertices_779) then 7 else
  if p.val = (false, vertices_341) then 14 else
  if p.val = (false, vertices_681) then 10 else
  if p.val = (false, vertices_817) then 16 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_204) then 11 else
  if p.val = (true, vertices_240) then 17 else
  if p.val = (true, vertices_416) then 3 else
  if p.val = (true, vertices_448) then 4 else
  if p.val = (true, vertices_896) then 5 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 6 => Sum.inl 0
  | 7 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 8 => Sum.inl 2
  | 9 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 5, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_962, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_194, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 3, 5]
  vertex := 4
  face := Sum.inl ⟨vertices_252, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_252, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 3, 5]
  vertex := 6
  face := Sum.inl ⟨vertices_252, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_252, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 3 → HeightRow boundary := ![row0, row1, row2]
noncomputable def pivot : Fin 3 → Fin 9 := ![0, 4, 1]
noncomputable def heightProof : HeightCertificate boundary 3 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_206, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .fromLargerFacet ![0, 1, 2, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_206, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_204, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_252, by decide +kernel⟩ ![1, 2, 3, 5]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_252, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_650, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 2, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_138, (by decide +kernel)⟩ ⟨vertices_650, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_962, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_194, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_252, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![1, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_252, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_496, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fromLargerFacet ![3, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_240, (by decide +kernel)⟩ ⟨vertices_496, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_240, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_252, by decide +kernel⟩ ![1, 2, 3, 5]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_252, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_928, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![4, 6, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_416, (by decide +kernel)⟩ ⟨vertices_928, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coveringFacets : Fin 6 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5]
noncomputable def coveringProof (j : Fin 6) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (fun i => Fin.elim0 i))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 3 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 6, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0081

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_multi_six_0082.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0082

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_327 : Finset (Fin 10) := literalFinset [0, 1, 2, 6, 8] (by decide +kernel)
noncomputable def vertices_651 : Finset (Fin 10) := literalFinset [0, 1, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_771 : Finset (Fin 10) := literalFinset [0, 1, 8, 9] (by decide +kernel)
noncomputable def vertices_341 : Finset (Fin 10) := literalFinset [0, 2, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_553 : Finset (Fin 10) := literalFinset [0, 3, 5, 9] (by decide +kernel)
noncomputable def vertices_817 : Finset (Fin 10) := literalFinset [0, 4, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_206 : Finset (Fin 10) := literalFinset [1, 2, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_962 : Finset (Fin 10) := literalFinset [1, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_252 : Finset (Fin 10) := literalFinset [2, 3, 4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_936 : Finset (Fin 10) := literalFinset [3, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_496 : Finset (Fin 10) := literalFinset [4, 5, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_259 : Finset (Fin 10) := literalFinset [0, 1, 8] (by decide +kernel)
noncomputable def vertices_515 : Finset (Fin 10) := literalFinset [0, 1, 9] (by decide +kernel)
noncomputable def vertices_21 : Finset (Fin 10) := literalFinset [0, 2, 4] (by decide +kernel)
noncomputable def vertices_325 : Finset (Fin 10) := literalFinset [0, 2, 6, 8] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_521 : Finset (Fin 10) := literalFinset [0, 3, 9] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_273 : Finset (Fin 10) := literalFinset [0, 4, 8] (by decide +kernel)
noncomputable def vertices_545 : Finset (Fin 10) := literalFinset [0, 5, 9] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_70 : Finset (Fin 10) := literalFinset [1, 2, 6] (by decide +kernel)
noncomputable def vertices_138 : Finset (Fin 10) := literalFinset [1, 3, 7] (by decide +kernel)
noncomputable def vertices_194 : Finset (Fin 10) := literalFinset [1, 6, 7] (by decide +kernel)
noncomputable def vertices_322 : Finset (Fin 10) := literalFinset [1, 6, 8] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_60 : Finset (Fin 10) := literalFinset [2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_204 : Finset (Fin 10) := literalFinset [2, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_552 : Finset (Fin 10) := literalFinset [3, 5, 9] (by decide +kernel)
noncomputable def vertices_648 : Finset (Fin 10) := literalFinset [3, 7, 9] (by decide +kernel)
noncomputable def vertices_240 : Finset (Fin 10) := literalFinset [4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_651, vertices_771, vertices_341, vertices_553, vertices_817, vertices_206, vertices_962, vertices_252, vertices_936, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_515, vertices_21, vertices_325, vertices_41, vertices_521, vertices_49, vertices_273, vertices_545, vertices_769, vertices_14, vertices_70, vertices_138, vertices_194, vertices_322, vertices_642, vertices_770, vertices_60, vertices_204, vertices_84, vertices_168, vertices_552, vertices_648, vertices_240, vertices_304, vertices_336, vertices_416, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_651), (false, vertices_771), (false, vertices_341), (false, vertices_553), (false, vertices_817), (true, vertices_194), (true, vertices_204), (true, vertices_168), (true, vertices_240), (true, vertices_416), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![7, 12, 9, 15, 18, 19, 20, 21, 22]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 10 else
  if p.val = (false, vertices_327) then 13 else
  if p.val = (false, vertices_651) then 8 else
  if p.val = (false, vertices_771) then 0 else
  if p.val = (false, vertices_341) then 14 else
  if p.val = (false, vertices_553) then 1 else
  if p.val = (false, vertices_817) then 16 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_204) then 11 else
  if p.val = (true, vertices_168) then 3 else
  if p.val = (true, vertices_240) then 17 else
  if p.val = (true, vertices_416) then 4 else
  if p.val = (true, vertices_448) then 5 else
  if p.val = (true, vertices_896) then 6 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 7 => Sum.inl 0
  | 8 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 9 => Sum.inl 2
  | 10 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 5, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_962, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_194, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![2, 4, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_936, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_168, (by decide +kernel)⟩ ⟨vertices_936, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 3, 5]
  vertex := 4
  face := Sum.inl ⟨vertices_252, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_252, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 3, 5]
  vertex := 6
  face := Sum.inl ⟨vertices_252, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_252, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 7, 4, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_206, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .fromLargerFacet ![0, 1, 2, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_206, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_204, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_252, by decide +kernel⟩ ![1, 2, 3, 5]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_252, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_962, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_194, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_252, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![1, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_252, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_936, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![2, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_168, (by decide +kernel)⟩ ⟨vertices_936, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_496, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fromLargerFacet ![3, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_240, (by decide +kernel)⟩ ⟨vertices_496, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_240, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_252, by decide +kernel⟩ ![1, 2, 3, 5]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_252, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def coveringFacets : Fin 5 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4]
noncomputable def coveringProof (j : Fin 5) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (fun i => Fin.elim0 i)))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 5, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0082

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_0570 : Certifies 570 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0048.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0571 : Certifies 571 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0049.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0572 : Certifies 572 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0050.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0573 : Certifies 573 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0054.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0574 : Certifies 574 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0055.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0575 : Certifies 575 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0056.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0576 : Certifies 576 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0057.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0577 : Certifies 577 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0058.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0578 : Certifies 578 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0059.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0579 : Certifies 579 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0060.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0580 : Certifies 580 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0061.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0581 : Certifies 581 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0062.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0582 : Certifies 582 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0063.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0583 : Certifies 583 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0064.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0584 : Certifies 584 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0065.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0585 : Certifies 585 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0066.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0586 : Certifies 586 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0068.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0587 : Certifies 587 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0070.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0588 : Certifies 588 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0071.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0589 : Certifies 589 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0072.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0590 : Certifies 590 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0073.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0591 : Certifies 591 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0074.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0592 : Certifies 592 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0075.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0593 : Certifies 593 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0076.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0594 : Certifies 594 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0077.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0595 : Certifies 595 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0078.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0596 : Certifies 596 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0079.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0597 : Certifies 597 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0080.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0598 : Certifies 598 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0081.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0599 : Certifies 599 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0082.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B019 (j : Fin 30) :
    Certifies (570 + j.val) := by
  fin_cases j
  · exact projection_0570
  · exact projection_0571
  · exact projection_0572
  · exact projection_0573
  · exact projection_0574
  · exact projection_0575
  · exact projection_0576
  · exact projection_0577
  · exact projection_0578
  · exact projection_0579
  · exact projection_0580
  · exact projection_0581
  · exact projection_0582
  · exact projection_0583
  · exact projection_0584
  · exact projection_0585
  · exact projection_0586
  · exact projection_0587
  · exact projection_0588
  · exact projection_0589
  · exact projection_0590
  · exact projection_0591
  · exact projection_0592
  · exact projection_0593
  · exact projection_0594
  · exact projection_0595
  · exact projection_0596
  · exact projection_0597
  · exact projection_0598
  · exact projection_0599

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
