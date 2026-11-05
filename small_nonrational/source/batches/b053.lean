module
public import TerminalGeometry
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Papers.FiniteProjectionChecks

section
set_option debug.skipKernelTC false

section BundlePart0
/- Source: ProjectionCertificates/R_one_six_1365.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1365

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_647 : Finset (Fin 10) := literalFinset [0, 1, 2, 7, 9] (by decide +kernel)
noncomputable def vertices_91 : Finset (Fin 10) := literalFinset [0, 1, 3, 4, 6] (by decide +kernel)
noncomputable def vertices_835 : Finset (Fin 10) := literalFinset [0, 1, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_181 : Finset (Fin 10) := literalFinset [0, 2, 4, 5, 7] (by decide +kernel)
noncomputable def vertices_337 : Finset (Fin 10) := literalFinset [0, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_913 : Finset (Fin 10) := literalFinset [0, 4, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_590 : Finset (Fin 10) := literalFinset [1, 2, 3, 6, 9] (by decide +kernel)
noncomputable def vertices_364 : Finset (Fin 10) := literalFinset [2, 3, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_612 : Finset (Fin 10) := literalFinset [2, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_676 : Finset (Fin 10) := literalFinset [2, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_440 : Finset (Fin 10) := literalFinset [3, 4, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_344 : Finset (Fin 10) := literalFinset [3, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_992 : Finset (Fin 10) := literalFinset [5, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_27 : Finset (Fin 10) := literalFinset [0, 1, 3, 4] (by decide +kernel)
noncomputable def vertices_67 : Finset (Fin 10) := literalFinset [0, 1, 6] (by decide +kernel)
noncomputable def vertices_515 : Finset (Fin 10) := literalFinset [0, 1, 9] (by decide +kernel)
noncomputable def vertices_53 : Finset (Fin 10) := literalFinset [0, 2, 4, 5] (by decide +kernel)
noncomputable def vertices_133 : Finset (Fin 10) := literalFinset [0, 2, 7] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_145 : Finset (Fin 10) := literalFinset [0, 4, 7] (by decide +kernel)
noncomputable def vertices_273 : Finset (Fin 10) := literalFinset [0, 4, 8] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_74 : Finset (Fin 10) := literalFinset [1, 3, 6] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_76 : Finset (Fin 10) := literalFinset [2, 3, 6] (by decide +kernel)
noncomputable def vertices_100 : Finset (Fin 10) := literalFinset [2, 5, 6] (by decide +kernel)
noncomputable def vertices_164 : Finset (Fin 10) := literalFinset [2, 5, 7] (by decide +kernel)
noncomputable def vertices_548 : Finset (Fin 10) := literalFinset [2, 5, 9] (by decide +kernel)
noncomputable def vertices_580 : Finset (Fin 10) := literalFinset [2, 6, 9] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_56 : Finset (Fin 10) := literalFinset [3, 4, 5] (by decide +kernel)
noncomputable def vertices_88 : Finset (Fin 10) := literalFinset [3, 4, 6] (by decide +kernel)
noncomputable def vertices_280 : Finset (Fin 10) := literalFinset [3, 4, 8] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_328 : Finset (Fin 10) := literalFinset [3, 6, 8] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_608 : Finset (Fin 10) := literalFinset [5, 6, 9] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_835, vertices_181, vertices_337, vertices_913, vertices_590, vertices_364, vertices_612, vertices_676, vertices_440, vertices_344, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_53, vertices_133, vertices_81, vertices_145, vertices_273, vertices_321, vertices_641, vertices_769, vertices_14, vertices_518, vertices_74, vertices_578, vertices_44, vertices_76, vertices_100, vertices_164, vertices_548, vertices_580, vertices_644, vertices_56, vertices_88, vertices_280, vertices_296, vertices_328, vertices_176, vertices_336, vertices_400, vertices_352, vertices_608, vertices_416, vertices_672, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_337), (false, vertices_913), (true, vertices_76), (true, vertices_100), (true, vertices_548), (true, vertices_580), (true, vertices_280), (true, vertices_296), (true, vertices_328), (true, vertices_352), (true, vertices_608), (true, vertices_416), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![15, 12, 19, 20, 22, 23, 24, 25, 26]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_647) then 13 else
  if p.val = (false, vertices_91) then 17 else
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_181) then 14 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (false, vertices_913) then 21 else
  if p.val = (true, vertices_76) then 1 else
  if p.val = (true, vertices_100) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_580) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_328) then 7 else
  if p.val = (true, vertices_352) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_416) then 10 else
  if p.val = (true, vertices_672) then 11 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_337), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
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
  frame := ![0, 1, 2, 5]
  vertex := 8
  face := Sum.inl ⟨vertices_590, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_590, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 4, 5]
  vertex := 7
  face := Sum.inl ⟨vertices_364, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_364, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![2, 3, 4, 6]
  vertex := 7
  face := Sum.inl ⟨vertices_440, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_440, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![4, 5, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_992, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_352, (by decide +kernel)⟩ ⟨vertices_992, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 1, 2, 4]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_590, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_590, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_364, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![1, 2, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_364, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_612, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![1, 4, 5, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_100, (by decide +kernel)⟩ ⟨vertices_612, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_676, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![1, 4, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_164, (by decide +kernel)⟩ ⟨vertices_676, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_440, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![2, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_440, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_344, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![2, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_88, (by decide +kernel)⟩ ⟨vertices_344, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_992, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![4, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_352, (by decide +kernel)⟩ ⟨vertices_992, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1365

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_one_six_1366.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1366

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_647 : Finset (Fin 10) := literalFinset [0, 1, 2, 7, 9] (by decide +kernel)
noncomputable def vertices_91 : Finset (Fin 10) := literalFinset [0, 1, 3, 4, 6] (by decide +kernel)
noncomputable def vertices_835 : Finset (Fin 10) := literalFinset [0, 1, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_181 : Finset (Fin 10) := literalFinset [0, 2, 4, 5, 7] (by decide +kernel)
noncomputable def vertices_337 : Finset (Fin 10) := literalFinset [0, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_913 : Finset (Fin 10) := literalFinset [0, 4, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_590 : Finset (Fin 10) := literalFinset [1, 2, 3, 6, 9] (by decide +kernel)
noncomputable def vertices_364 : Finset (Fin 10) := literalFinset [2, 3, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_228 : Finset (Fin 10) := literalFinset [2, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_708 : Finset (Fin 10) := literalFinset [2, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_440 : Finset (Fin 10) := literalFinset [3, 4, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_344 : Finset (Fin 10) := literalFinset [3, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_992 : Finset (Fin 10) := literalFinset [5, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_27 : Finset (Fin 10) := literalFinset [0, 1, 3, 4] (by decide +kernel)
noncomputable def vertices_67 : Finset (Fin 10) := literalFinset [0, 1, 6] (by decide +kernel)
noncomputable def vertices_515 : Finset (Fin 10) := literalFinset [0, 1, 9] (by decide +kernel)
noncomputable def vertices_53 : Finset (Fin 10) := literalFinset [0, 2, 4, 5] (by decide +kernel)
noncomputable def vertices_133 : Finset (Fin 10) := literalFinset [0, 2, 7] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_145 : Finset (Fin 10) := literalFinset [0, 4, 7] (by decide +kernel)
noncomputable def vertices_273 : Finset (Fin 10) := literalFinset [0, 4, 8] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_74 : Finset (Fin 10) := literalFinset [1, 3, 6] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_76 : Finset (Fin 10) := literalFinset [2, 3, 6] (by decide +kernel)
noncomputable def vertices_100 : Finset (Fin 10) := literalFinset [2, 5, 6] (by decide +kernel)
noncomputable def vertices_164 : Finset (Fin 10) := literalFinset [2, 5, 7] (by decide +kernel)
noncomputable def vertices_196 : Finset (Fin 10) := literalFinset [2, 6, 7] (by decide +kernel)
noncomputable def vertices_580 : Finset (Fin 10) := literalFinset [2, 6, 9] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_56 : Finset (Fin 10) := literalFinset [3, 4, 5] (by decide +kernel)
noncomputable def vertices_88 : Finset (Fin 10) := literalFinset [3, 4, 6] (by decide +kernel)
noncomputable def vertices_280 : Finset (Fin 10) := literalFinset [3, 4, 8] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_328 : Finset (Fin 10) := literalFinset [3, 6, 8] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_224 : Finset (Fin 10) := literalFinset [5, 6, 7] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_835, vertices_181, vertices_337, vertices_913, vertices_590, vertices_364, vertices_228, vertices_708, vertices_440, vertices_344, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_53, vertices_133, vertices_81, vertices_145, vertices_273, vertices_321, vertices_641, vertices_769, vertices_14, vertices_518, vertices_74, vertices_578, vertices_44, vertices_76, vertices_100, vertices_164, vertices_196, vertices_580, vertices_644, vertices_56, vertices_88, vertices_280, vertices_296, vertices_328, vertices_176, vertices_336, vertices_400, vertices_224, vertices_352, vertices_416, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_337), (false, vertices_913), (true, vertices_76), (true, vertices_100), (true, vertices_196), (true, vertices_580), (true, vertices_280), (true, vertices_296), (true, vertices_328), (true, vertices_224), (true, vertices_352), (true, vertices_416), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![15, 12, 19, 20, 22, 23, 24, 25, 26]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_647) then 13 else
  if p.val = (false, vertices_91) then 17 else
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_181) then 14 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (false, vertices_913) then 21 else
  if p.val = (true, vertices_76) then 1 else
  if p.val = (true, vertices_100) then 2 else
  if p.val = (true, vertices_196) then 3 else
  if p.val = (true, vertices_580) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_328) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_352) then 9 else
  if p.val = (true, vertices_416) then 10 else
  if p.val = (true, vertices_704) then 11 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_337), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
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
  frame := ![0, 1, 2, 5]
  vertex := 8
  face := Sum.inl ⟨vertices_590, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_590, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 4, 5]
  vertex := 7
  face := Sum.inl ⟨vertices_364, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_364, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![2, 3, 4, 6]
  vertex := 7
  face := Sum.inl ⟨vertices_440, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_440, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![4, 5, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_992, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_224, (by decide +kernel)⟩ ⟨vertices_992, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 1, 2, 4]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_590, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_590, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_364, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![1, 2, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_364, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_228, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![1, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_100, (by decide +kernel)⟩ ⟨vertices_228, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_708, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![1, 5, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_196, (by decide +kernel)⟩ ⟨vertices_708, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_440, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![2, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_440, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_344, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![2, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_88, (by decide +kernel)⟩ ⟨vertices_344, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_992, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![4, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_224, (by decide +kernel)⟩ ⟨vertices_992, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1366

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_one_six_1367.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1367

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_647 : Finset (Fin 10) := literalFinset [0, 1, 2, 7, 9] (by decide +kernel)
noncomputable def vertices_587 : Finset (Fin 10) := literalFinset [0, 1, 3, 6, 9] (by decide +kernel)
noncomputable def vertices_181 : Finset (Fin 10) := literalFinset [0, 2, 4, 5, 7] (by decide +kernel)
noncomputable def vertices_361 : Finset (Fin 10) := literalFinset [0, 3, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_737 : Finset (Fin 10) := literalFinset [0, 5, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_94 : Finset (Fin 10) := literalFinset [1, 2, 3, 4, 6] (by decide +kernel)
noncomputable def vertices_838 : Finset (Fin 10) := literalFinset [1, 2, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_340 : Finset (Fin 10) := literalFinset [2, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_916 : Finset (Fin 10) := literalFinset [2, 4, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_440 : Finset (Fin 10) := literalFinset [3, 4, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_344 : Finset (Fin 10) := literalFinset [3, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_480 : Finset (Fin 10) := literalFinset [5, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_960 : Finset (Fin 10) := literalFinset [6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_515 : Finset (Fin 10) := literalFinset [0, 1, 9] (by decide +kernel)
noncomputable def vertices_53 : Finset (Fin 10) := literalFinset [0, 2, 4, 5] (by decide +kernel)
noncomputable def vertices_133 : Finset (Fin 10) := literalFinset [0, 2, 7] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_73 : Finset (Fin 10) := literalFinset [0, 3, 6] (by decide +kernel)
noncomputable def vertices_97 : Finset (Fin 10) := literalFinset [0, 5, 6] (by decide +kernel)
noncomputable def vertices_161 : Finset (Fin 10) := literalFinset [0, 5, 7] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_30 : Finset (Fin 10) := literalFinset [1, 2, 3, 4] (by decide +kernel)
noncomputable def vertices_70 : Finset (Fin 10) := literalFinset [1, 2, 6] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_74 : Finset (Fin 10) := literalFinset [1, 3, 6] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_148 : Finset (Fin 10) := literalFinset [2, 4, 7] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_324 : Finset (Fin 10) := literalFinset [2, 6, 8] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_56 : Finset (Fin 10) := literalFinset [3, 4, 5] (by decide +kernel)
noncomputable def vertices_88 : Finset (Fin 10) := literalFinset [3, 4, 6] (by decide +kernel)
noncomputable def vertices_280 : Finset (Fin 10) := literalFinset [3, 4, 8] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_328 : Finset (Fin 10) := literalFinset [3, 6, 8] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_224 : Finset (Fin 10) := literalFinset [5, 6, 7] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_587, vertices_181, vertices_361, vertices_737, vertices_94, vertices_838, vertices_340, vertices_916, vertices_440, vertices_344, vertices_480, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_53, vertices_133, vertices_41, vertices_73, vertices_97, vertices_161, vertices_577, vertices_641, vertices_30, vertices_70, vertices_518, vertices_74, vertices_578, vertices_84, vertices_148, vertices_276, vertices_324, vertices_644, vertices_772, vertices_56, vertices_88, vertices_280, vertices_296, vertices_328, vertices_176, vertices_336, vertices_400, vertices_224, vertices_352, vertices_416, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_587), (false, vertices_181), (false, vertices_361), (false, vertices_737), (true, vertices_70), (true, vertices_84), (true, vertices_276), (true, vertices_324), (true, vertices_772), (true, vertices_88), (true, vertices_280), (true, vertices_336), (true, vertices_400), (true, vertices_416), (true, vertices_448), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 16, 19, 21, 22, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_647) then 14 else
  if p.val = (false, vertices_587) then 15 else
  if p.val = (false, vertices_181) then 18 else
  if p.val = (false, vertices_361) then 20 else
  if p.val = (false, vertices_737) then 23 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_324) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_88) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_832) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 5, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_838, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_70, (by decide +kernel)⟩ ⟨vertices_838, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 3
  frame := ![0, 1, 2]
  vertex := 3
  face := Sum.inr ⟨vertices_30, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_30, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 3, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_916, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_148, (by decide +kernel)⟩ ⟨vertices_916, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![2, 3, 4, 6]
  vertex := 7
  face := Sum.inl ⟨vertices_440, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_440, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![5, 0, 1, 2]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_94, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_30, (by decide +kernel)⟩ ⟨vertices_94, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_838, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_70, (by decide +kernel)⟩ ⟨vertices_838, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_340, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![1, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_340, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_916, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 3, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_148, (by decide +kernel)⟩ ⟨vertices_916, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_440, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![2, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_440, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_344, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![2, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_88, (by decide +kernel)⟩ ⟨vertices_344, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_480, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![4, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_224, (by decide +kernel)⟩ ⟨vertices_480, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_960, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![5, 6, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_448, (by decide +kernel)⟩ ⟨vertices_960, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1367

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_one_six_1368.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1368

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_647 : Finset (Fin 10) := literalFinset [0, 1, 2, 7, 9] (by decide +kernel)
noncomputable def vertices_587 : Finset (Fin 10) := literalFinset [0, 1, 3, 6, 9] (by decide +kernel)
noncomputable def vertices_181 : Finset (Fin 10) := literalFinset [0, 2, 4, 5, 7] (by decide +kernel)
noncomputable def vertices_361 : Finset (Fin 10) := literalFinset [0, 3, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_737 : Finset (Fin 10) := literalFinset [0, 5, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_94 : Finset (Fin 10) := literalFinset [1, 2, 3, 4, 6] (by decide +kernel)
noncomputable def vertices_838 : Finset (Fin 10) := literalFinset [1, 2, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_340 : Finset (Fin 10) := literalFinset [2, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_916 : Finset (Fin 10) := literalFinset [2, 4, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_440 : Finset (Fin 10) := literalFinset [3, 4, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_344 : Finset (Fin 10) := literalFinset [3, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_864 : Finset (Fin 10) := literalFinset [5, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_928 : Finset (Fin 10) := literalFinset [5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_515 : Finset (Fin 10) := literalFinset [0, 1, 9] (by decide +kernel)
noncomputable def vertices_53 : Finset (Fin 10) := literalFinset [0, 2, 4, 5] (by decide +kernel)
noncomputable def vertices_133 : Finset (Fin 10) := literalFinset [0, 2, 7] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_73 : Finset (Fin 10) := literalFinset [0, 3, 6] (by decide +kernel)
noncomputable def vertices_97 : Finset (Fin 10) := literalFinset [0, 5, 6] (by decide +kernel)
noncomputable def vertices_161 : Finset (Fin 10) := literalFinset [0, 5, 7] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_30 : Finset (Fin 10) := literalFinset [1, 2, 3, 4] (by decide +kernel)
noncomputable def vertices_70 : Finset (Fin 10) := literalFinset [1, 2, 6] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_74 : Finset (Fin 10) := literalFinset [1, 3, 6] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_148 : Finset (Fin 10) := literalFinset [2, 4, 7] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_324 : Finset (Fin 10) := literalFinset [2, 6, 8] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_56 : Finset (Fin 10) := literalFinset [3, 4, 5] (by decide +kernel)
noncomputable def vertices_88 : Finset (Fin 10) := literalFinset [3, 4, 6] (by decide +kernel)
noncomputable def vertices_280 : Finset (Fin 10) := literalFinset [3, 4, 8] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_328 : Finset (Fin 10) := literalFinset [3, 6, 8] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_608 : Finset (Fin 10) := literalFinset [5, 6, 9] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_587, vertices_181, vertices_361, vertices_737, vertices_94, vertices_838, vertices_340, vertices_916, vertices_440, vertices_344, vertices_864, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_53, vertices_133, vertices_41, vertices_73, vertices_97, vertices_161, vertices_577, vertices_641, vertices_30, vertices_70, vertices_518, vertices_74, vertices_578, vertices_84, vertices_148, vertices_276, vertices_324, vertices_644, vertices_772, vertices_56, vertices_88, vertices_280, vertices_296, vertices_328, vertices_176, vertices_336, vertices_400, vertices_352, vertices_608, vertices_416, vertices_672, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_587), (false, vertices_181), (false, vertices_361), (false, vertices_737), (true, vertices_70), (true, vertices_84), (true, vertices_276), (true, vertices_324), (true, vertices_772), (true, vertices_88), (true, vertices_280), (true, vertices_336), (true, vertices_400), (true, vertices_416), (true, vertices_800), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 16, 19, 21, 22, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_647) then 14 else
  if p.val = (false, vertices_587) then 15 else
  if p.val = (false, vertices_181) then 18 else
  if p.val = (false, vertices_361) then 20 else
  if p.val = (false, vertices_737) then 23 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_324) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_88) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_832) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 5, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_838, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_70, (by decide +kernel)⟩ ⟨vertices_838, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 3
  frame := ![0, 1, 2]
  vertex := 3
  face := Sum.inr ⟨vertices_30, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_30, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 3, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_916, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_148, (by decide +kernel)⟩ ⟨vertices_916, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![2, 3, 4, 6]
  vertex := 7
  face := Sum.inl ⟨vertices_440, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_440, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![5, 0, 1, 2]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_94, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_30, (by decide +kernel)⟩ ⟨vertices_94, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_838, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_70, (by decide +kernel)⟩ ⟨vertices_838, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_340, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![1, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_340, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_916, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 3, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_148, (by decide +kernel)⟩ ⟨vertices_916, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_440, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![2, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_440, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_344, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![2, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_88, (by decide +kernel)⟩ ⟨vertices_344, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_864, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![4, 5, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_352, (by decide +kernel)⟩ ⟨vertices_864, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1368

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_one_six_1369.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1369

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_647 : Finset (Fin 10) := literalFinset [0, 1, 2, 7, 9] (by decide +kernel)
noncomputable def vertices_587 : Finset (Fin 10) := literalFinset [0, 1, 3, 6, 9] (by decide +kernel)
noncomputable def vertices_181 : Finset (Fin 10) := literalFinset [0, 2, 4, 5, 7] (by decide +kernel)
noncomputable def vertices_361 : Finset (Fin 10) := literalFinset [0, 3, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_929 : Finset (Fin 10) := literalFinset [0, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_833 : Finset (Fin 10) := literalFinset [0, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_94 : Finset (Fin 10) := literalFinset [1, 2, 3, 4, 6] (by decide +kernel)
noncomputable def vertices_838 : Finset (Fin 10) := literalFinset [1, 2, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_340 : Finset (Fin 10) := literalFinset [2, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_916 : Finset (Fin 10) := literalFinset [2, 4, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_248 : Finset (Fin 10) := literalFinset [3, 4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_464 : Finset (Fin 10) := literalFinset [4, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_480 : Finset (Fin 10) := literalFinset [5, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_515 : Finset (Fin 10) := literalFinset [0, 1, 9] (by decide +kernel)
noncomputable def vertices_53 : Finset (Fin 10) := literalFinset [0, 2, 4, 5] (by decide +kernel)
noncomputable def vertices_133 : Finset (Fin 10) := literalFinset [0, 2, 7] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_73 : Finset (Fin 10) := literalFinset [0, 3, 6] (by decide +kernel)
noncomputable def vertices_161 : Finset (Fin 10) := literalFinset [0, 5, 7] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_30 : Finset (Fin 10) := literalFinset [1, 2, 3, 4] (by decide +kernel)
noncomputable def vertices_70 : Finset (Fin 10) := literalFinset [1, 2, 6] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_74 : Finset (Fin 10) := literalFinset [1, 3, 6] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_148 : Finset (Fin 10) := literalFinset [2, 4, 7] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_324 : Finset (Fin 10) := literalFinset [2, 6, 8] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_56 : Finset (Fin 10) := literalFinset [3, 4, 5] (by decide +kernel)
noncomputable def vertices_88 : Finset (Fin 10) := literalFinset [3, 4, 6] (by decide +kernel)
noncomputable def vertices_104 : Finset (Fin 10) := literalFinset [3, 5, 6] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_208 : Finset (Fin 10) := literalFinset [4, 6, 7] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_224 : Finset (Fin 10) := literalFinset [5, 6, 7] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_587, vertices_181, vertices_361, vertices_929, vertices_833, vertices_94, vertices_838, vertices_340, vertices_916, vertices_248, vertices_464, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_53, vertices_133, vertices_41, vertices_73, vertices_161, vertices_289, vertices_321, vertices_577, vertices_641, vertices_769, vertices_30, vertices_70, vertices_518, vertices_74, vertices_578, vertices_84, vertices_148, vertices_276, vertices_324, vertices_644, vertices_772, vertices_56, vertices_88, vertices_104, vertices_176, vertices_208, vertices_336, vertices_400, vertices_224, vertices_352, vertices_416, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_587), (false, vertices_181), (false, vertices_361), (false, vertices_929), (false, vertices_833), (true, vertices_70), (true, vertices_84), (true, vertices_276), (true, vertices_324), (true, vertices_772), (true, vertices_88), (true, vertices_208), (true, vertices_336), (true, vertices_400), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![12, 15, 18, 20, 21, 23, 24, 25, 26]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_647) then 13 else
  if p.val = (false, vertices_587) then 14 else
  if p.val = (false, vertices_181) then 17 else
  if p.val = (false, vertices_361) then 19 else
  if p.val = (false, vertices_929) then 22 else
  if p.val = (false, vertices_833) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_324) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_448) then 11 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_833), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 23 => Sum.inl 5
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
  frame := ![2, 3, 4, 5]
  vertex := 6
  face := Sum.inl ⟨vertices_248, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_248, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 3
  frame := ![0, 1, 2]
  vertex := 3
  face := Sum.inr ⟨vertices_30, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_30, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 5, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_838, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_70, (by decide +kernel)⟩ ⟨vertices_838, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 3, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_916, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_148, (by decide +kernel)⟩ ⟨vertices_916, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![4, 2, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_94, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_30, (by decide +kernel)⟩ ⟨vertices_94, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_838, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_70, (by decide +kernel)⟩ ⟨vertices_838, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_340, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![1, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_340, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_916, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 3, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_148, (by decide +kernel)⟩ ⟨vertices_916, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_248, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![2, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_248, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_464, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![3, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_208, (by decide +kernel)⟩ ⟨vertices_464, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_480, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![4, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_224, (by decide +kernel)⟩ ⟨vertices_480, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1369

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_one_six_1370.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1370

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_647 : Finset (Fin 10) := literalFinset [0, 1, 2, 7, 9] (by decide +kernel)
noncomputable def vertices_91 : Finset (Fin 10) := literalFinset [0, 1, 3, 4, 6] (by decide +kernel)
noncomputable def vertices_835 : Finset (Fin 10) := literalFinset [0, 1, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_181 : Finset (Fin 10) := literalFinset [0, 2, 4, 5, 7] (by decide +kernel)
noncomputable def vertices_337 : Finset (Fin 10) := literalFinset [0, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_913 : Finset (Fin 10) := literalFinset [0, 4, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_590 : Finset (Fin 10) := literalFinset [1, 2, 3, 6, 9] (by decide +kernel)
noncomputable def vertices_364 : Finset (Fin 10) := literalFinset [2, 3, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_932 : Finset (Fin 10) := literalFinset [2, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_836 : Finset (Fin 10) := literalFinset [2, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_184 : Finset (Fin 10) := literalFinset [3, 4, 5, 7] (by decide +kernel)
noncomputable def vertices_472 : Finset (Fin 10) := literalFinset [3, 4, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_424 : Finset (Fin 10) := literalFinset [3, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_27 : Finset (Fin 10) := literalFinset [0, 1, 3, 4] (by decide +kernel)
noncomputable def vertices_67 : Finset (Fin 10) := literalFinset [0, 1, 6] (by decide +kernel)
noncomputable def vertices_515 : Finset (Fin 10) := literalFinset [0, 1, 9] (by decide +kernel)
noncomputable def vertices_53 : Finset (Fin 10) := literalFinset [0, 2, 4, 5] (by decide +kernel)
noncomputable def vertices_133 : Finset (Fin 10) := literalFinset [0, 2, 7] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_145 : Finset (Fin 10) := literalFinset [0, 4, 7] (by decide +kernel)
noncomputable def vertices_273 : Finset (Fin 10) := literalFinset [0, 4, 8] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_74 : Finset (Fin 10) := literalFinset [1, 3, 6] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_76 : Finset (Fin 10) := literalFinset [2, 3, 6] (by decide +kernel)
noncomputable def vertices_164 : Finset (Fin 10) := literalFinset [2, 5, 7] (by decide +kernel)
noncomputable def vertices_292 : Finset (Fin 10) := literalFinset [2, 5, 8] (by decide +kernel)
noncomputable def vertices_324 : Finset (Fin 10) := literalFinset [2, 6, 8] (by decide +kernel)
noncomputable def vertices_580 : Finset (Fin 10) := literalFinset [2, 6, 9] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_56 : Finset (Fin 10) := literalFinset [3, 4, 5] (by decide +kernel)
noncomputable def vertices_88 : Finset (Fin 10) := literalFinset [3, 4, 6] (by decide +kernel)
noncomputable def vertices_152 : Finset (Fin 10) := literalFinset [3, 4, 7] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_328 : Finset (Fin 10) := literalFinset [3, 6, 8] (by decide +kernel)
noncomputable def vertices_392 : Finset (Fin 10) := literalFinset [3, 7, 8] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_835, vertices_181, vertices_337, vertices_913, vertices_590, vertices_364, vertices_932, vertices_836, vertices_184, vertices_472, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_53, vertices_133, vertices_81, vertices_145, vertices_273, vertices_321, vertices_641, vertices_769, vertices_14, vertices_518, vertices_74, vertices_578, vertices_44, vertices_76, vertices_164, vertices_292, vertices_324, vertices_580, vertices_644, vertices_772, vertices_56, vertices_88, vertices_152, vertices_168, vertices_296, vertices_328, vertices_392, vertices_176, vertices_336, vertices_400, vertices_416, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_337), (false, vertices_913), (true, vertices_76), (true, vertices_292), (true, vertices_324), (true, vertices_580), (true, vertices_772), (true, vertices_152), (true, vertices_168), (true, vertices_296), (true, vertices_328), (true, vertices_392), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![15, 12, 19, 20, 22, 23, 24, 25, 26]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_647) then 13 else
  if p.val = (false, vertices_91) then 17 else
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_181) then 14 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (false, vertices_913) then 21 else
  if p.val = (true, vertices_76) then 1 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_324) then 3 else
  if p.val = (true, vertices_580) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_416) then 11 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_337), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
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
  frame := ![0, 1, 2, 5]
  vertex := 8
  face := Sum.inl ⟨vertices_590, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_590, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
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

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 4, 5]
  vertex := 7
  face := Sum.inl ⟨vertices_364, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_364, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![2, 3, 5, 6]
  vertex := 7
  face := Sum.inl ⟨vertices_472, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_88, (by decide +kernel)⟩ ⟨vertices_472, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 8, 1, 2]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_590, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_590, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_364, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![1, 2, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_364, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_932, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![1, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_164, (by decide +kernel)⟩ ⟨vertices_932, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_836, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![1, 5, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_324, (by decide +kernel)⟩ ⟨vertices_836, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_184, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![2, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_184, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_472, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![2, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_88, (by decide +kernel)⟩ ⟨vertices_472, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_424, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![2, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_168, (by decide +kernel)⟩ ⟨vertices_424, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1370

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_one_six_1371.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1371

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_647 : Finset (Fin 10) := literalFinset [0, 1, 2, 7, 9] (by decide +kernel)
noncomputable def vertices_779 : Finset (Fin 10) := literalFinset [0, 1, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_181 : Finset (Fin 10) := literalFinset [0, 2, 4, 5, 7] (by decide +kernel)
noncomputable def vertices_361 : Finset (Fin 10) := literalFinset [0, 3, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_929 : Finset (Fin 10) := literalFinset [0, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_94 : Finset (Fin 10) := literalFinset [1, 2, 3, 4, 6] (by decide +kernel)
noncomputable def vertices_838 : Finset (Fin 10) := literalFinset [1, 2, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_330 : Finset (Fin 10) := literalFinset [1, 3, 6, 8] (by decide +kernel)
noncomputable def vertices_340 : Finset (Fin 10) := literalFinset [2, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_916 : Finset (Fin 10) := literalFinset [2, 4, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_248 : Finset (Fin 10) := literalFinset [3, 4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_464 : Finset (Fin 10) := literalFinset [4, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_480 : Finset (Fin 10) := literalFinset [5, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_515 : Finset (Fin 10) := literalFinset [0, 1, 9] (by decide +kernel)
noncomputable def vertices_53 : Finset (Fin 10) := literalFinset [0, 2, 4, 5] (by decide +kernel)
noncomputable def vertices_133 : Finset (Fin 10) := literalFinset [0, 2, 7] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_265 : Finset (Fin 10) := literalFinset [0, 3, 8] (by decide +kernel)
noncomputable def vertices_161 : Finset (Fin 10) := literalFinset [0, 5, 7] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_30 : Finset (Fin 10) := literalFinset [1, 2, 3, 4] (by decide +kernel)
noncomputable def vertices_70 : Finset (Fin 10) := literalFinset [1, 2, 6] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_74 : Finset (Fin 10) := literalFinset [1, 3, 6] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_322 : Finset (Fin 10) := literalFinset [1, 6, 8] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_148 : Finset (Fin 10) := literalFinset [2, 4, 7] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_324 : Finset (Fin 10) := literalFinset [2, 6, 8] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_56 : Finset (Fin 10) := literalFinset [3, 4, 5] (by decide +kernel)
noncomputable def vertices_88 : Finset (Fin 10) := literalFinset [3, 4, 6] (by decide +kernel)
noncomputable def vertices_104 : Finset (Fin 10) := literalFinset [3, 5, 6] (by decide +kernel)
noncomputable def vertices_328 : Finset (Fin 10) := literalFinset [3, 6, 8] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_208 : Finset (Fin 10) := literalFinset [4, 6, 7] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_224 : Finset (Fin 10) := literalFinset [5, 6, 7] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_779, vertices_181, vertices_361, vertices_929, vertices_94, vertices_838, vertices_330, vertices_340, vertices_916, vertices_248, vertices_464, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_53, vertices_133, vertices_41, vertices_265, vertices_161, vertices_289, vertices_641, vertices_769, vertices_30, vertices_70, vertices_518, vertices_74, vertices_266, vertices_322, vertices_770, vertices_84, vertices_148, vertices_276, vertices_324, vertices_644, vertices_772, vertices_56, vertices_88, vertices_104, vertices_328, vertices_176, vertices_208, vertices_336, vertices_400, vertices_224, vertices_352, vertices_416, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_779), (false, vertices_181), (false, vertices_361), (false, vertices_929), (true, vertices_70), (true, vertices_74), (true, vertices_322), (true, vertices_84), (true, vertices_276), (true, vertices_324), (true, vertices_772), (true, vertices_88), (true, vertices_208), (true, vertices_336), (true, vertices_400), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 16, 19, 21, 22, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_647) then 14 else
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_181) then 18 else
  if p.val = (false, vertices_361) then 20 else
  if p.val = (false, vertices_929) then 23 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_276) then 4 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_772) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_448) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 4
  frame := ![2, 3, 4, 5]
  vertex := 6
  face := Sum.inl ⟨vertices_248, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_248, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 3
  frame := ![0, 1, 2]
  vertex := 3
  face := Sum.inr ⟨vertices_30, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_30, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 5, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_838, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_70, (by decide +kernel)⟩ ⟨vertices_838, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 3, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_916, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_148, (by decide +kernel)⟩ ⟨vertices_916, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![4, 2, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_94, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_30, (by decide +kernel)⟩ ⟨vertices_94, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_838, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_70, (by decide +kernel)⟩ ⟨vertices_838, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_330, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 2, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_74, (by decide +kernel)⟩ ⟨vertices_330, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_340, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![1, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_340, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_916, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![1, 3, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_148, (by decide +kernel)⟩ ⟨vertices_916, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_248, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![2, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_248, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_464, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![3, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_208, (by decide +kernel)⟩ ⟨vertices_464, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_480, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![4, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_224, (by decide +kernel)⟩ ⟨vertices_480, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1371

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_one_six_1373.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1373

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_91 : Finset (Fin 10) := literalFinset [0, 1, 3, 4, 6] (by decide +kernel)
noncomputable def vertices_173 : Finset (Fin 10) := literalFinset [0, 2, 3, 5, 7] (by decide +kernel)
noncomputable def vertices_457 : Finset (Fin 10) := literalFinset [0, 3, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_369 : Finset (Fin 10) := literalFinset [0, 4, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_929 : Finset (Fin 10) := literalFinset [0, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_654 : Finset (Fin 10) := literalFinset [1, 2, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_86 : Finset (Fin 10) := literalFinset [1, 2, 4, 6] (by decide +kernel)
noncomputable def vertices_582 : Finset (Fin 10) := literalFinset [1, 2, 6, 9] (by decide +kernel)
noncomputable def vertices_202 : Finset (Fin 10) := literalFinset [1, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_962 : Finset (Fin 10) := literalFinset [1, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_692 : Finset (Fin 10) := literalFinset [2, 4, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_852 : Finset (Fin 10) := literalFinset [2, 4, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_816 : Finset (Fin 10) := literalFinset [4, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_27 : Finset (Fin 10) := literalFinset [0, 1, 3, 4] (by decide +kernel)
noncomputable def vertices_45 : Finset (Fin 10) := literalFinset [0, 2, 3, 5] (by decide +kernel)
noncomputable def vertices_73 : Finset (Fin 10) := literalFinset [0, 3, 6] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_161 : Finset (Fin 10) := literalFinset [0, 5, 7] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_385 : Finset (Fin 10) := literalFinset [0, 7, 8] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_22 : Finset (Fin 10) := literalFinset [1, 2, 4] (by decide +kernel)
noncomputable def vertices_70 : Finset (Fin 10) := literalFinset [1, 2, 6] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_74 : Finset (Fin 10) := literalFinset [1, 3, 6] (by decide +kernel)
noncomputable def vertices_138 : Finset (Fin 10) := literalFinset [1, 3, 7] (by decide +kernel)
noncomputable def vertices_82 : Finset (Fin 10) := literalFinset [1, 4, 6] (by decide +kernel)
noncomputable def vertices_194 : Finset (Fin 10) := literalFinset [1, 6, 7] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_140 : Finset (Fin 10) := literalFinset [2, 3, 7] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_532 : Finset (Fin 10) := literalFinset [2, 4, 9] (by decide +kernel)
noncomputable def vertices_164 : Finset (Fin 10) := literalFinset [2, 5, 7] (by decide +kernel)
noncomputable def vertices_580 : Finset (Fin 10) := literalFinset [2, 6, 9] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_200 : Finset (Fin 10) := literalFinset [3, 6, 7] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_784 : Finset (Fin 10) := literalFinset [4, 8, 9] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_369, vertices_929, vertices_654, vertices_86, vertices_582, vertices_202, vertices_962, vertices_692, vertices_852, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_161, vertices_289, vertices_321, vertices_385, vertices_14, vertices_22, vertices_70, vertices_518, vertices_74, vertices_138, vertices_82, vertices_194, vertices_578, vertices_642, vertices_140, vertices_52, vertices_84, vertices_532, vertices_164, vertices_580, vertices_644, vertices_200, vertices_304, vertices_560, vertices_336, vertices_784, vertices_672, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_369), (false, vertices_929), (true, vertices_70), (true, vertices_518), (true, vertices_138), (true, vertices_194), (true, vertices_578), (true, vertices_642), (true, vertices_84), (true, vertices_532), (true, vertices_580), (true, vertices_644), (true, vertices_560), (true, vertices_784), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 15, 18, 20, 22, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_173) then 17 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (false, vertices_929) then 23 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
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

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 3, 5, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_852, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_852, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![2, 0, 4, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_654, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_654, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_86, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 1, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_86, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_582, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 1, 5, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_70, (by decide +kernel)⟩ ⟨vertices_582, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_202, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 2, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_74, (by decide +kernel)⟩ ⟨vertices_202, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_962, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![0, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_194, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_692, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![1, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_692, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_852, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![1, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_852, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_816, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![3, 4, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_304, (by decide +kernel)⟩ ⟨vertices_816, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1373

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_one_six_1374.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1374

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_91 : Finset (Fin 10) := literalFinset [0, 1, 3, 4, 6] (by decide +kernel)
noncomputable def vertices_173 : Finset (Fin 10) := literalFinset [0, 2, 3, 5, 7] (by decide +kernel)
noncomputable def vertices_457 : Finset (Fin 10) := literalFinset [0, 3, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_433 : Finset (Fin 10) := literalFinset [0, 4, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_849 : Finset (Fin 10) := literalFinset [0, 4, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_654 : Finset (Fin 10) := literalFinset [1, 2, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_86 : Finset (Fin 10) := literalFinset [1, 2, 4, 6] (by decide +kernel)
noncomputable def vertices_582 : Finset (Fin 10) := literalFinset [1, 2, 6, 9] (by decide +kernel)
noncomputable def vertices_202 : Finset (Fin 10) := literalFinset [1, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_962 : Finset (Fin 10) := literalFinset [1, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_628 : Finset (Fin 10) := literalFinset [2, 4, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_932 : Finset (Fin 10) := literalFinset [2, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_816 : Finset (Fin 10) := literalFinset [4, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_27 : Finset (Fin 10) := literalFinset [0, 1, 3, 4] (by decide +kernel)
noncomputable def vertices_45 : Finset (Fin 10) := literalFinset [0, 2, 3, 5] (by decide +kernel)
noncomputable def vertices_73 : Finset (Fin 10) := literalFinset [0, 3, 6] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_273 : Finset (Fin 10) := literalFinset [0, 4, 8] (by decide +kernel)
noncomputable def vertices_161 : Finset (Fin 10) := literalFinset [0, 5, 7] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_385 : Finset (Fin 10) := literalFinset [0, 7, 8] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_22 : Finset (Fin 10) := literalFinset [1, 2, 4] (by decide +kernel)
noncomputable def vertices_70 : Finset (Fin 10) := literalFinset [1, 2, 6] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_74 : Finset (Fin 10) := literalFinset [1, 3, 6] (by decide +kernel)
noncomputable def vertices_138 : Finset (Fin 10) := literalFinset [1, 3, 7] (by decide +kernel)
noncomputable def vertices_82 : Finset (Fin 10) := literalFinset [1, 4, 6] (by decide +kernel)
noncomputable def vertices_194 : Finset (Fin 10) := literalFinset [1, 6, 7] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_140 : Finset (Fin 10) := literalFinset [2, 3, 7] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_164 : Finset (Fin 10) := literalFinset [2, 5, 7] (by decide +kernel)
noncomputable def vertices_548 : Finset (Fin 10) := literalFinset [2, 5, 9] (by decide +kernel)
noncomputable def vertices_580 : Finset (Fin 10) := literalFinset [2, 6, 9] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_200 : Finset (Fin 10) := literalFinset [3, 6, 7] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_784 : Finset (Fin 10) := literalFinset [4, 8, 9] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_433, vertices_849, vertices_654, vertices_86, vertices_582, vertices_202, vertices_962, vertices_628, vertices_932, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_273, vertices_161, vertices_321, vertices_385, vertices_14, vertices_22, vertices_70, vertices_518, vertices_74, vertices_138, vertices_82, vertices_194, vertices_578, vertices_642, vertices_140, vertices_52, vertices_84, vertices_164, vertices_548, vertices_580, vertices_644, vertices_200, vertices_304, vertices_560, vertices_592, vertices_784, vertices_416, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_433), (false, vertices_849), (true, vertices_70), (true, vertices_518), (true, vertices_138), (true, vertices_194), (true, vertices_578), (true, vertices_642), (true, vertices_84), (true, vertices_548), (true, vertices_580), (true, vertices_644), (true, vertices_560), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 15, 18, 20, 23, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_173) then 17 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (false, vertices_433) then 21 else
  if p.val = (false, vertices_849) then 22 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_800) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
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
  frameSize := 4
  frame := ![1, 3, 4, 5]
  vertex := 8
  face := Sum.inl ⟨vertices_628, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_628, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
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

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![2, 0, 3, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_654, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_654, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_86, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 1, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_86, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_582, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 1, 5, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_70, (by decide +kernel)⟩ ⟨vertices_582, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_202, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 2, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_74, (by decide +kernel)⟩ ⟨vertices_202, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_962, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![0, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_194, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_628, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![1, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_628, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_932, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![1, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_164, (by decide +kernel)⟩ ⟨vertices_932, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_816, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![3, 4, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_304, (by decide +kernel)⟩ ⟨vertices_816, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1374

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_one_six_1375.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1375

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_91 : Finset (Fin 10) := literalFinset [0, 1, 3, 4, 6] (by decide +kernel)
noncomputable def vertices_173 : Finset (Fin 10) := literalFinset [0, 2, 3, 5, 7] (by decide +kernel)
noncomputable def vertices_457 : Finset (Fin 10) := literalFinset [0, 3, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_369 : Finset (Fin 10) := literalFinset [0, 4, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_929 : Finset (Fin 10) := literalFinset [0, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_654 : Finset (Fin 10) := literalFinset [1, 2, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_342 : Finset (Fin 10) := literalFinset [1, 2, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_774 : Finset (Fin 10) := literalFinset [1, 2, 8, 9] (by decide +kernel)
noncomputable def vertices_202 : Finset (Fin 10) := literalFinset [1, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_962 : Finset (Fin 10) := literalFinset [1, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_692 : Finset (Fin 10) := literalFinset [2, 4, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_788 : Finset (Fin 10) := literalFinset [2, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_816 : Finset (Fin 10) := literalFinset [4, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_27 : Finset (Fin 10) := literalFinset [0, 1, 3, 4] (by decide +kernel)
noncomputable def vertices_45 : Finset (Fin 10) := literalFinset [0, 2, 3, 5] (by decide +kernel)
noncomputable def vertices_73 : Finset (Fin 10) := literalFinset [0, 3, 6] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_161 : Finset (Fin 10) := literalFinset [0, 5, 7] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_385 : Finset (Fin 10) := literalFinset [0, 7, 8] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_22 : Finset (Fin 10) := literalFinset [1, 2, 4] (by decide +kernel)
noncomputable def vertices_262 : Finset (Fin 10) := literalFinset [1, 2, 8] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_74 : Finset (Fin 10) := literalFinset [1, 3, 6] (by decide +kernel)
noncomputable def vertices_138 : Finset (Fin 10) := literalFinset [1, 3, 7] (by decide +kernel)
noncomputable def vertices_82 : Finset (Fin 10) := literalFinset [1, 4, 6] (by decide +kernel)
noncomputable def vertices_194 : Finset (Fin 10) := literalFinset [1, 6, 7] (by decide +kernel)
noncomputable def vertices_322 : Finset (Fin 10) := literalFinset [1, 6, 8] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_140 : Finset (Fin 10) := literalFinset [2, 3, 7] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_532 : Finset (Fin 10) := literalFinset [2, 4, 9] (by decide +kernel)
noncomputable def vertices_164 : Finset (Fin 10) := literalFinset [2, 5, 7] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_200 : Finset (Fin 10) := literalFinset [3, 6, 7] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_784 : Finset (Fin 10) := literalFinset [4, 8, 9] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_369, vertices_929, vertices_654, vertices_342, vertices_774, vertices_202, vertices_962, vertices_692, vertices_788, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_161, vertices_289, vertices_321, vertices_385, vertices_14, vertices_22, vertices_262, vertices_518, vertices_74, vertices_138, vertices_82, vertices_194, vertices_322, vertices_642, vertices_770, vertices_140, vertices_52, vertices_276, vertices_532, vertices_164, vertices_644, vertices_772, vertices_200, vertices_304, vertices_560, vertices_336, vertices_784, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_369), (false, vertices_929), (true, vertices_262), (true, vertices_518), (true, vertices_138), (true, vertices_194), (true, vertices_322), (true, vertices_642), (true, vertices_770), (true, vertices_276), (true, vertices_532), (true, vertices_644), (true, vertices_772), (true, vertices_560), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 15, 18, 20, 22, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_173) then 17 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (false, vertices_929) then 23 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_784) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
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
  frame := ![0, 1, 3, 5]
  vertex := 7
  face := Sum.inl ⟨vertices_342, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_342, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
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

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![2, 4, 1, 0]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_654, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_654, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_342, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_342, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_774, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 1, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_262, (by decide +kernel)⟩ ⟨vertices_774, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_202, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 2, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_74, (by decide +kernel)⟩ ⟨vertices_202, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_962, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![0, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_194, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_692, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![1, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_692, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_788, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![1, 3, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_276, (by decide +kernel)⟩ ⟨vertices_788, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_816, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![3, 4, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_304, (by decide +kernel)⟩ ⟨vertices_816, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1375

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_one_six_1376.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1376

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_527 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 9] (by decide +kernel)
noncomputable def vertices_59 : Finset (Fin 10) := literalFinset [0, 1, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_787 : Finset (Fin 10) := literalFinset [0, 1, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_141 : Finset (Fin 10) := literalFinset [0, 2, 3, 7] (by decide +kernel)
noncomputable def vertices_901 : Finset (Fin 10) := literalFinset [0, 2, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_425 : Finset (Fin 10) := literalFinset [0, 3, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_369 : Finset (Fin 10) := literalFinset [0, 4, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_126 : Finset (Fin 10) := literalFinset [1, 2, 3, 4, 5, 6] (by decide +kernel)
noncomputable def vertices_662 : Finset (Fin 10) := literalFinset [1, 2, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_236 : Finset (Fin 10) := literalFinset [2, 3, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_212 : Finset (Fin 10) := literalFinset [2, 4, 6, 7] (by decide +kernel)
noncomputable def vertices_720 : Finset (Fin 10) := literalFinset [4, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_848 : Finset (Fin 10) := literalFinset [4, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_992 : Finset (Fin 10) := literalFinset [5, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_19 : Finset (Fin 10) := literalFinset [0, 1, 4] (by decide +kernel)
noncomputable def vertices_515 : Finset (Fin 10) := literalFinset [0, 1, 9] (by decide +kernel)
noncomputable def vertices_13 : Finset (Fin 10) := literalFinset [0, 2, 3] (by decide +kernel)
noncomputable def vertices_133 : Finset (Fin 10) := literalFinset [0, 2, 7] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_273 : Finset (Fin 10) := literalFinset [0, 4, 8] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_385 : Finset (Fin 10) := literalFinset [0, 7, 8] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_22 : Finset (Fin 10) := literalFinset [1, 2, 4] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_58 : Finset (Fin 10) := literalFinset [1, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_530 : Finset (Fin 10) := literalFinset [1, 4, 9] (by decide +kernel)
noncomputable def vertices_108 : Finset (Fin 10) := literalFinset [2, 3, 5, 6] (by decide +kernel)
noncomputable def vertices_140 : Finset (Fin 10) := literalFinset [2, 3, 7] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_148 : Finset (Fin 10) := literalFinset [2, 4, 7] (by decide +kernel)
noncomputable def vertices_196 : Finset (Fin 10) := literalFinset [2, 6, 7] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_208 : Finset (Fin 10) := literalFinset [4, 6, 7] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_784 : Finset (Fin 10) := literalFinset [4, 8, 9] (by decide +kernel)
noncomputable def vertices_224 : Finset (Fin 10) := literalFinset [5, 6, 7] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_527, vertices_59, vertices_787, vertices_141, vertices_901, vertices_425, vertices_369, vertices_126, vertices_662, vertices_236, vertices_212, vertices_720, vertices_848, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_515, vertices_13, vertices_133, vertices_517, vertices_41, vertices_137, vertices_49, vertices_273, vertices_289, vertices_385, vertices_769, vertices_14, vertices_22, vertices_518, vertices_58, vertices_530, vertices_108, vertices_140, vertices_84, vertices_148, vertices_196, vertices_644, vertices_168, vertices_112, vertices_208, vertices_336, vertices_592, vertices_656, vertices_784, vertices_224, vertices_352, vertices_416, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_527), (false, vertices_59), (false, vertices_787), (false, vertices_141), (false, vertices_901), (false, vertices_425), (false, vertices_369), (true, vertices_22), (true, vertices_108), (true, vertices_84), (true, vertices_148), (true, vertices_196), (true, vertices_208), (true, vertices_592), (true, vertices_656), (true, vertices_224), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![11, 15, 18, 20, 22, 23, 24, 25, 26]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_527) then 12 else
  if p.val = (false, vertices_59) then 13 else
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_141) then 0 else
  if p.val = (false, vertices_901) then 16 else
  if p.val = (false, vertices_425) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_108) then 17 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_208) then 5 else
  if p.val = (true, vertices_592) then 6 else
  if p.val = (true, vertices_656) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_141), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_59), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_108), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
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
  frame := ![4, 5, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_992, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_224, (by decide +kernel)⟩ ⟨vertices_992, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 2, 3]
  vertex := 4
  face := Sum.inl ⟨vertices_126, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_126, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 2, 3]
  vertex := 5
  face := Sum.inl ⟨vertices_126, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_126, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 3, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_662, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_662, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![7, 4, 2, 0]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_126, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .fundamental ![0, 1, 2, 3] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_126, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_662, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_662, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_236, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fromLargerFacet ![1, 2, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_108, (by decide +kernel)⟩ ⟨vertices_236, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_108, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_126, by decide +kernel⟩ ![0, 1, 2, 3]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_126, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_212, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![1, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_212, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_720, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![3, 5, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_208, (by decide +kernel)⟩ ⟨vertices_720, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_848, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![3, 5, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_336, (by decide +kernel)⟩ ⟨vertices_848, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_992, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![4, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_224, (by decide +kernel)⟩ ⟨vertices_992, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1376

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_one_six_1377.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1377

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_91 : Finset (Fin 10) := literalFinset [0, 1, 3, 4, 6] (by decide +kernel)
noncomputable def vertices_173 : Finset (Fin 10) := literalFinset [0, 2, 3, 5, 7] (by decide +kernel)
noncomputable def vertices_457 : Finset (Fin 10) := literalFinset [0, 3, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_369 : Finset (Fin 10) := literalFinset [0, 4, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_929 : Finset (Fin 10) := literalFinset [0, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_590 : Finset (Fin 10) := literalFinset [1, 2, 3, 6, 9] (by decide +kernel)
noncomputable def vertices_790 : Finset (Fin 10) := literalFinset [1, 2, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_338 : Finset (Fin 10) := literalFinset [1, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_962 : Finset (Fin 10) := literalFinset [1, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_204 : Finset (Fin 10) := literalFinset [2, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_692 : Finset (Fin 10) := literalFinset [2, 4, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_708 : Finset (Fin 10) := literalFinset [2, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_816 : Finset (Fin 10) := literalFinset [4, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_27 : Finset (Fin 10) := literalFinset [0, 1, 3, 4] (by decide +kernel)
noncomputable def vertices_45 : Finset (Fin 10) := literalFinset [0, 2, 3, 5] (by decide +kernel)
noncomputable def vertices_73 : Finset (Fin 10) := literalFinset [0, 3, 6] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_161 : Finset (Fin 10) := literalFinset [0, 5, 7] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_385 : Finset (Fin 10) := literalFinset [0, 7, 8] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_22 : Finset (Fin 10) := literalFinset [1, 2, 4] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_74 : Finset (Fin 10) := literalFinset [1, 3, 6] (by decide +kernel)
noncomputable def vertices_82 : Finset (Fin 10) := literalFinset [1, 4, 6] (by decide +kernel)
noncomputable def vertices_274 : Finset (Fin 10) := literalFinset [1, 4, 8] (by decide +kernel)
noncomputable def vertices_322 : Finset (Fin 10) := literalFinset [1, 6, 8] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_76 : Finset (Fin 10) := literalFinset [2, 3, 6] (by decide +kernel)
noncomputable def vertices_140 : Finset (Fin 10) := literalFinset [2, 3, 7] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_532 : Finset (Fin 10) := literalFinset [2, 4, 9] (by decide +kernel)
noncomputable def vertices_164 : Finset (Fin 10) := literalFinset [2, 5, 7] (by decide +kernel)
noncomputable def vertices_196 : Finset (Fin 10) := literalFinset [2, 6, 7] (by decide +kernel)
noncomputable def vertices_580 : Finset (Fin 10) := literalFinset [2, 6, 9] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_200 : Finset (Fin 10) := literalFinset [3, 6, 7] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_784 : Finset (Fin 10) := literalFinset [4, 8, 9] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_369, vertices_929, vertices_590, vertices_790, vertices_338, vertices_962, vertices_204, vertices_692, vertices_708, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_161, vertices_289, vertices_321, vertices_385, vertices_14, vertices_22, vertices_518, vertices_74, vertices_82, vertices_274, vertices_322, vertices_578, vertices_770, vertices_76, vertices_140, vertices_52, vertices_532, vertices_164, vertices_196, vertices_580, vertices_644, vertices_200, vertices_304, vertices_560, vertices_336, vertices_784, vertices_672, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_369), (false, vertices_929), (true, vertices_518), (true, vertices_274), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_76), (true, vertices_532), (true, vertices_196), (true, vertices_580), (true, vertices_644), (true, vertices_560), (true, vertices_784), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 15, 18, 20, 22, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_173) then 17 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (false, vertices_929) then 23 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_704) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 2, 5]
  vertex := 8
  face := Sum.inl ⟨vertices_590, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_590, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
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
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_322, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
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

noncomputable def row3 : HeightRow boundary where
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

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![2, 5, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_590, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_590, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_790, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_790, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_338, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_82, (by decide +kernel)⟩ ⟨vertices_338, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_962, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![0, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_322, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_204, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![1, 2, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_76, (by decide +kernel)⟩ ⟨vertices_204, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_692, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![1, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_692, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_708, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![1, 5, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_196, (by decide +kernel)⟩ ⟨vertices_708, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_816, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![3, 4, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_304, (by decide +kernel)⟩ ⟨vertices_816, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1377

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_one_six_1379.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1379

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_91 : Finset (Fin 10) := literalFinset [0, 1, 3, 4, 6] (by decide +kernel)
noncomputable def vertices_173 : Finset (Fin 10) := literalFinset [0, 2, 3, 5, 7] (by decide +kernel)
noncomputable def vertices_457 : Finset (Fin 10) := literalFinset [0, 3, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_369 : Finset (Fin 10) := literalFinset [0, 4, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_929 : Finset (Fin 10) := literalFinset [0, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_590 : Finset (Fin 10) := literalFinset [1, 2, 3, 6, 9] (by decide +kernel)
noncomputable def vertices_790 : Finset (Fin 10) := literalFinset [1, 2, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_338 : Finset (Fin 10) := literalFinset [1, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_962 : Finset (Fin 10) := literalFinset [1, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_652 : Finset (Fin 10) := literalFinset [2, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_692 : Finset (Fin 10) := literalFinset [2, 4, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_712 : Finset (Fin 10) := literalFinset [3, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_816 : Finset (Fin 10) := literalFinset [4, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_27 : Finset (Fin 10) := literalFinset [0, 1, 3, 4] (by decide +kernel)
noncomputable def vertices_45 : Finset (Fin 10) := literalFinset [0, 2, 3, 5] (by decide +kernel)
noncomputable def vertices_73 : Finset (Fin 10) := literalFinset [0, 3, 6] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_161 : Finset (Fin 10) := literalFinset [0, 5, 7] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_385 : Finset (Fin 10) := literalFinset [0, 7, 8] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_22 : Finset (Fin 10) := literalFinset [1, 2, 4] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_74 : Finset (Fin 10) := literalFinset [1, 3, 6] (by decide +kernel)
noncomputable def vertices_82 : Finset (Fin 10) := literalFinset [1, 4, 6] (by decide +kernel)
noncomputable def vertices_274 : Finset (Fin 10) := literalFinset [1, 4, 8] (by decide +kernel)
noncomputable def vertices_322 : Finset (Fin 10) := literalFinset [1, 6, 8] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_140 : Finset (Fin 10) := literalFinset [2, 3, 7] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_532 : Finset (Fin 10) := literalFinset [2, 4, 9] (by decide +kernel)
noncomputable def vertices_164 : Finset (Fin 10) := literalFinset [2, 5, 7] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_200 : Finset (Fin 10) := literalFinset [3, 6, 7] (by decide +kernel)
noncomputable def vertices_584 : Finset (Fin 10) := literalFinset [3, 6, 9] (by decide +kernel)
noncomputable def vertices_648 : Finset (Fin 10) := literalFinset [3, 7, 9] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_784 : Finset (Fin 10) := literalFinset [4, 8, 9] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_369, vertices_929, vertices_590, vertices_790, vertices_338, vertices_962, vertices_652, vertices_692, vertices_712, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_161, vertices_289, vertices_321, vertices_385, vertices_14, vertices_22, vertices_518, vertices_74, vertices_82, vertices_274, vertices_322, vertices_578, vertices_770, vertices_140, vertices_524, vertices_52, vertices_532, vertices_164, vertices_644, vertices_200, vertices_584, vertices_648, vertices_304, vertices_560, vertices_336, vertices_784, vertices_672, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_369), (false, vertices_929), (true, vertices_518), (true, vertices_274), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_524), (true, vertices_532), (true, vertices_644), (true, vertices_584), (true, vertices_648), (true, vertices_560), (true, vertices_784), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 15, 18, 20, 22, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_173) then 17 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (false, vertices_929) then 23 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_584) then 8 else
  if p.val = (true, vertices_648) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_704) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 2, 5]
  vertex := 8
  face := Sum.inl ⟨vertices_590, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_590, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
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
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_322, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
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

noncomputable def row3 : HeightRow boundary where
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

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![2, 5, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_590, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_590, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_790, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_790, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_338, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_82, (by decide +kernel)⟩ ⟨vertices_338, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_962, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![0, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_322, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_652, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![1, 2, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_140, (by decide +kernel)⟩ ⟨vertices_652, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_692, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![1, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_692, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_712, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![2, 5, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_200, (by decide +kernel)⟩ ⟨vertices_712, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_816, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![3, 4, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_304, (by decide +kernel)⟩ ⟨vertices_816, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1379

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_one_six_1383.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1383

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_91 : Finset (Fin 10) := literalFinset [0, 1, 3, 4, 6] (by decide +kernel)
noncomputable def vertices_173 : Finset (Fin 10) := literalFinset [0, 2, 3, 5, 7] (by decide +kernel)
noncomputable def vertices_457 : Finset (Fin 10) := literalFinset [0, 3, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_369 : Finset (Fin 10) := literalFinset [0, 4, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_929 : Finset (Fin 10) := literalFinset [0, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_526 : Finset (Fin 10) := literalFinset [1, 2, 3, 9] (by decide +kernel)
noncomputable def vertices_790 : Finset (Fin 10) := literalFinset [1, 2, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_586 : Finset (Fin 10) := literalFinset [1, 3, 6, 9] (by decide +kernel)
noncomputable def vertices_338 : Finset (Fin 10) := literalFinset [1, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_962 : Finset (Fin 10) := literalFinset [1, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_716 : Finset (Fin 10) := literalFinset [2, 3, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_692 : Finset (Fin 10) := literalFinset [2, 4, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_816 : Finset (Fin 10) := literalFinset [4, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_27 : Finset (Fin 10) := literalFinset [0, 1, 3, 4] (by decide +kernel)
noncomputable def vertices_45 : Finset (Fin 10) := literalFinset [0, 2, 3, 5] (by decide +kernel)
noncomputable def vertices_73 : Finset (Fin 10) := literalFinset [0, 3, 6] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_161 : Finset (Fin 10) := literalFinset [0, 5, 7] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_385 : Finset (Fin 10) := literalFinset [0, 7, 8] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_22 : Finset (Fin 10) := literalFinset [1, 2, 4] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_74 : Finset (Fin 10) := literalFinset [1, 3, 6] (by decide +kernel)
noncomputable def vertices_522 : Finset (Fin 10) := literalFinset [1, 3, 9] (by decide +kernel)
noncomputable def vertices_82 : Finset (Fin 10) := literalFinset [1, 4, 6] (by decide +kernel)
noncomputable def vertices_274 : Finset (Fin 10) := literalFinset [1, 4, 8] (by decide +kernel)
noncomputable def vertices_322 : Finset (Fin 10) := literalFinset [1, 6, 8] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_140 : Finset (Fin 10) := literalFinset [2, 3, 7] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_532 : Finset (Fin 10) := literalFinset [2, 4, 9] (by decide +kernel)
noncomputable def vertices_164 : Finset (Fin 10) := literalFinset [2, 5, 7] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_200 : Finset (Fin 10) := literalFinset [3, 6, 7] (by decide +kernel)
noncomputable def vertices_584 : Finset (Fin 10) := literalFinset [3, 6, 9] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_784 : Finset (Fin 10) := literalFinset [4, 8, 9] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_369, vertices_929, vertices_526, vertices_790, vertices_586, vertices_338, vertices_962, vertices_716, vertices_692, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_161, vertices_289, vertices_321, vertices_385, vertices_14, vertices_22, vertices_518, vertices_74, vertices_522, vertices_82, vertices_274, vertices_322, vertices_578, vertices_770, vertices_140, vertices_524, vertices_52, vertices_532, vertices_164, vertices_644, vertices_200, vertices_584, vertices_304, vertices_560, vertices_336, vertices_784, vertices_672, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_369), (false, vertices_929), (true, vertices_518), (true, vertices_522), (true, vertices_274), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_524), (true, vertices_532), (true, vertices_644), (true, vertices_584), (true, vertices_560), (true, vertices_784), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 15, 18, 20, 22, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_173) then 17 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (false, vertices_929) then 23 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_704) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 5, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_716, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_140, (by decide +kernel)⟩ ⟨vertices_716, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
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
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_322, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
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

noncomputable def row3 : HeightRow boundary where
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

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![2, 5, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_526, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .fundamental ![0, 1, 2, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_526, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_790, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_790, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_586, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 2, 5, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_74, (by decide +kernel)⟩ ⟨vertices_586, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_338, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_82, (by decide +kernel)⟩ ⟨vertices_338, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_962, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![0, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_322, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_716, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![1, 2, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_140, (by decide +kernel)⟩ ⟨vertices_716, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_692, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![1, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_692, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_816, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![3, 4, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_304, (by decide +kernel)⟩ ⟨vertices_816, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1383

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_one_six_1384.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1384

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_91 : Finset (Fin 10) := literalFinset [0, 1, 3, 4, 6] (by decide +kernel)
noncomputable def vertices_173 : Finset (Fin 10) := literalFinset [0, 2, 3, 5, 7] (by decide +kernel)
noncomputable def vertices_457 : Finset (Fin 10) := literalFinset [0, 3, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_369 : Finset (Fin 10) := literalFinset [0, 4, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_929 : Finset (Fin 10) := literalFinset [0, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_78 : Finset (Fin 10) := literalFinset [1, 2, 3, 6] (by decide +kernel)
noncomputable def vertices_790 : Finset (Fin 10) := literalFinset [1, 2, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_582 : Finset (Fin 10) := literalFinset [1, 2, 6, 9] (by decide +kernel)
noncomputable def vertices_338 : Finset (Fin 10) := literalFinset [1, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_962 : Finset (Fin 10) := literalFinset [1, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_716 : Finset (Fin 10) := literalFinset [2, 3, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_692 : Finset (Fin 10) := literalFinset [2, 4, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_816 : Finset (Fin 10) := literalFinset [4, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_27 : Finset (Fin 10) := literalFinset [0, 1, 3, 4] (by decide +kernel)
noncomputable def vertices_45 : Finset (Fin 10) := literalFinset [0, 2, 3, 5] (by decide +kernel)
noncomputable def vertices_73 : Finset (Fin 10) := literalFinset [0, 3, 6] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_161 : Finset (Fin 10) := literalFinset [0, 5, 7] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_385 : Finset (Fin 10) := literalFinset [0, 7, 8] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_22 : Finset (Fin 10) := literalFinset [1, 2, 4] (by decide +kernel)
noncomputable def vertices_70 : Finset (Fin 10) := literalFinset [1, 2, 6] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_74 : Finset (Fin 10) := literalFinset [1, 3, 6] (by decide +kernel)
noncomputable def vertices_82 : Finset (Fin 10) := literalFinset [1, 4, 6] (by decide +kernel)
noncomputable def vertices_274 : Finset (Fin 10) := literalFinset [1, 4, 8] (by decide +kernel)
noncomputable def vertices_322 : Finset (Fin 10) := literalFinset [1, 6, 8] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_76 : Finset (Fin 10) := literalFinset [2, 3, 6] (by decide +kernel)
noncomputable def vertices_140 : Finset (Fin 10) := literalFinset [2, 3, 7] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_532 : Finset (Fin 10) := literalFinset [2, 4, 9] (by decide +kernel)
noncomputable def vertices_164 : Finset (Fin 10) := literalFinset [2, 5, 7] (by decide +kernel)
noncomputable def vertices_580 : Finset (Fin 10) := literalFinset [2, 6, 9] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_200 : Finset (Fin 10) := literalFinset [3, 6, 7] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_784 : Finset (Fin 10) := literalFinset [4, 8, 9] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_369, vertices_929, vertices_78, vertices_790, vertices_582, vertices_338, vertices_962, vertices_716, vertices_692, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_161, vertices_289, vertices_321, vertices_385, vertices_14, vertices_22, vertices_70, vertices_518, vertices_74, vertices_82, vertices_274, vertices_322, vertices_578, vertices_770, vertices_76, vertices_140, vertices_52, vertices_532, vertices_164, vertices_580, vertices_644, vertices_200, vertices_304, vertices_560, vertices_336, vertices_784, vertices_672, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_369), (false, vertices_929), (true, vertices_70), (true, vertices_518), (true, vertices_274), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_76), (true, vertices_532), (true, vertices_580), (true, vertices_644), (true, vertices_560), (true, vertices_784), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 15, 18, 20, 22, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_173) then 17 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (false, vertices_929) then 23 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_704) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 5, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_716, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_76, (by decide +kernel)⟩ ⟨vertices_716, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
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
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_322, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
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

noncomputable def row3 : HeightRow boundary where
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

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![2, 5, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_78, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .fundamental ![0, 1, 2, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_78, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_790, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_790, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_582, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 1, 5, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_70, (by decide +kernel)⟩ ⟨vertices_582, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_338, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_82, (by decide +kernel)⟩ ⟨vertices_338, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_962, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![0, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_322, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_716, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![1, 2, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_76, (by decide +kernel)⟩ ⟨vertices_716, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_692, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![1, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_692, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_816, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![3, 4, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_304, (by decide +kernel)⟩ ⟨vertices_816, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1384

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_one_six_1385.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1385

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_139 : Finset (Fin 10) := literalFinset [0, 1, 3, 7] (by decide +kernel)
noncomputable def vertices_779 : Finset (Fin 10) := literalFinset [0, 1, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_659 : Finset (Fin 10) := literalFinset [0, 1, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_837 : Finset (Fin 10) := literalFinset [0, 2, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_425 : Finset (Fin 10) := literalFinset [0, 3, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_737 : Finset (Fin 10) := literalFinset [0, 5, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_353 : Finset (Fin 10) := literalFinset [0, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_126 : Finset (Fin 10) := literalFinset [1, 2, 3, 4, 5, 6] (by decide +kernel)
noncomputable def vertices_270 : Finset (Fin 10) := literalFinset [1, 2, 3, 8] (by decide +kernel)
noncomputable def vertices_790 : Finset (Fin 10) := literalFinset [1, 2, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_186 : Finset (Fin 10) := literalFinset [1, 3, 4, 5, 7] (by decide +kernel)
noncomputable def vertices_364 : Finset (Fin 10) := literalFinset [2, 3, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_724 : Finset (Fin 10) := literalFinset [2, 4, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_240 : Finset (Fin 10) := literalFinset [4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_131 : Finset (Fin 10) := literalFinset [0, 1, 7] (by decide +kernel)
noncomputable def vertices_515 : Finset (Fin 10) := literalFinset [0, 1, 9] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_265 : Finset (Fin 10) := literalFinset [0, 3, 8] (by decide +kernel)
noncomputable def vertices_97 : Finset (Fin 10) := literalFinset [0, 5, 6] (by decide +kernel)
noncomputable def vertices_161 : Finset (Fin 10) := literalFinset [0, 5, 7] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_22 : Finset (Fin 10) := literalFinset [1, 2, 4] (by decide +kernel)
noncomputable def vertices_262 : Finset (Fin 10) := literalFinset [1, 2, 8] (by decide +kernel)
noncomputable def vertices_58 : Finset (Fin 10) := literalFinset [1, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_138 : Finset (Fin 10) := literalFinset [1, 3, 7] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_146 : Finset (Fin 10) := literalFinset [1, 4, 7] (by decide +kernel)
noncomputable def vertices_530 : Finset (Fin 10) := literalFinset [1, 4, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_108 : Finset (Fin 10) := literalFinset [2, 3, 5, 6] (by decide +kernel)
noncomputable def vertices_268 : Finset (Fin 10) := literalFinset [2, 3, 8] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_532 : Finset (Fin 10) := literalFinset [2, 4, 9] (by decide +kernel)
noncomputable def vertices_324 : Finset (Fin 10) := literalFinset [2, 6, 8] (by decide +kernel)
noncomputable def vertices_580 : Finset (Fin 10) := literalFinset [2, 6, 9] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_208 : Finset (Fin 10) := literalFinset [4, 6, 7] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_224 : Finset (Fin 10) := literalFinset [5, 6, 7] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_139, vertices_779, vertices_659, vertices_837, vertices_425, vertices_737, vertices_353, vertices_126, vertices_270, vertices_790, vertices_186, vertices_364, vertices_724, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_131, vertices_515, vertices_137, vertices_265, vertices_97, vertices_161, vertices_289, vertices_321, vertices_577, vertices_641, vertices_769, vertices_14, vertices_22, vertices_262, vertices_58, vertices_138, vertices_266, vertices_146, vertices_530, vertices_770, vertices_108, vertices_268, vertices_84, vertices_532, vertices_324, vertices_580, vertices_772, vertices_168, vertices_296, vertices_112, vertices_176, vertices_208, vertices_656, vertices_224, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_139), (false, vertices_779), (false, vertices_659), (false, vertices_837), (false, vertices_425), (false, vertices_737), (false, vertices_353), (true, vertices_14), (true, vertices_22), (true, vertices_262), (true, vertices_58), (true, vertices_108), (true, vertices_268), (true, vertices_84), (true, vertices_532), (true, vertices_112), (true, vertices_176), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![11, 15, 18, 20, 21, 23, 24, 25, 26]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_139) then 0 else
  if p.val = (false, vertices_779) then 12 else
  if p.val = (false, vertices_659) then 13 else
  if p.val = (false, vertices_837) then 16 else
  if p.val = (false, vertices_425) then 19 else
  if p.val = (false, vertices_737) then 22 else
  if p.val = (false, vertices_353) then 1 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_22) then 3 else
  if p.val = (true, vertices_262) then 4 else
  if p.val = (true, vertices_58) then 14 else
  if p.val = (true, vertices_108) then 17 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_208) then 10 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_139), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_353), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_58), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_108), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 23 => Sum.inl 5
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
  frame := ![0, 1, 2, 3]
  vertex := 4
  face := Sum.inl ⟨vertices_126, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_126, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 2, 3]
  vertex := 5
  face := Sum.inl ⟨vertices_126, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_126, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
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

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 3, 5, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_724, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_724, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![4, 2, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_126, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .fundamental ![0, 1, 2, 3] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_126, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_270, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 1, 2, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_270, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_790, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 1, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_790, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_186, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fromLargerFacet ![0, 2, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_186, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_58, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_126, by decide +kernel⟩ ![0, 1, 2, 3]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_126, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_364, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fromLargerFacet ![1, 2, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_108, (by decide +kernel)⟩ ⟨vertices_364, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_108, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_126, by decide +kernel⟩ ![0, 1, 2, 3]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_126, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_724, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![1, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_724, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_240, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![3, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_240, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1385

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_one_six_1386.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1386

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_327 : Finset (Fin 10) := literalFinset [0, 1, 2, 6, 8] (by decide +kernel)
noncomputable def vertices_91 : Finset (Fin 10) := literalFinset [0, 1, 3, 4, 6] (by decide +kernel)
noncomputable def vertices_181 : Finset (Fin 10) := literalFinset [0, 2, 4, 5, 7] (by decide +kernel)
noncomputable def vertices_901 : Finset (Fin 10) := literalFinset [0, 2, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_465 : Finset (Fin 10) := literalFinset [0, 4, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_654 : Finset (Fin 10) := literalFinset [1, 2, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_774 : Finset (Fin 10) := literalFinset [1, 2, 8, 9] (by decide +kernel)
noncomputable def vertices_842 : Finset (Fin 10) := literalFinset [1, 3, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_172 : Finset (Fin 10) := literalFinset [2, 3, 5, 7] (by decide +kernel)
noncomputable def vertices_632 : Finset (Fin 10) := literalFinset [3, 4, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_680 : Finset (Fin 10) := literalFinset [3, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_944 : Finset (Fin 10) := literalFinset [4, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_848 : Finset (Fin 10) := literalFinset [4, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_27 : Finset (Fin 10) := literalFinset [0, 1, 3, 4] (by decide +kernel)
noncomputable def vertices_67 : Finset (Fin 10) := literalFinset [0, 1, 6] (by decide +kernel)
noncomputable def vertices_53 : Finset (Fin 10) := literalFinset [0, 2, 4, 5] (by decide +kernel)
noncomputable def vertices_133 : Finset (Fin 10) := literalFinset [0, 2, 7] (by decide +kernel)
noncomputable def vertices_261 : Finset (Fin 10) := literalFinset [0, 2, 8] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_145 : Finset (Fin 10) := literalFinset [0, 4, 7] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_385 : Finset (Fin 10) := literalFinset [0, 7, 8] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_262 : Finset (Fin 10) := literalFinset [1, 2, 8] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_74 : Finset (Fin 10) := literalFinset [1, 3, 6] (by decide +kernel)
noncomputable def vertices_522 : Finset (Fin 10) := literalFinset [1, 3, 9] (by decide +kernel)
noncomputable def vertices_322 : Finset (Fin 10) := literalFinset [1, 6, 8] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_140 : Finset (Fin 10) := literalFinset [2, 3, 7] (by decide +kernel)
noncomputable def vertices_164 : Finset (Fin 10) := literalFinset [2, 5, 7] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_56 : Finset (Fin 10) := literalFinset [3, 4, 5] (by decide +kernel)
noncomputable def vertices_88 : Finset (Fin 10) := literalFinset [3, 4, 6] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_552 : Finset (Fin 10) := literalFinset [3, 5, 9] (by decide +kernel)
noncomputable def vertices_584 : Finset (Fin 10) := literalFinset [3, 6, 9] (by decide +kernel)
noncomputable def vertices_648 : Finset (Fin 10) := literalFinset [3, 7, 9] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_784 : Finset (Fin 10) := literalFinset [4, 8, 9] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_91, vertices_181, vertices_901, vertices_465, vertices_654, vertices_774, vertices_842, vertices_172, vertices_632, vertices_680, vertices_944, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_53, vertices_133, vertices_261, vertices_81, vertices_145, vertices_321, vertices_385, vertices_14, vertices_262, vertices_518, vertices_74, vertices_522, vertices_322, vertices_770, vertices_44, vertices_140, vertices_164, vertices_644, vertices_772, vertices_56, vertices_88, vertices_168, vertices_552, vertices_584, vertices_648, vertices_176, vertices_560, vertices_336, vertices_592, vertices_400, vertices_784, vertices_672, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_91), (false, vertices_181), (false, vertices_901), (false, vertices_465), (true, vertices_518), (true, vertices_522), (true, vertices_770), (true, vertices_140), (true, vertices_168), (true, vertices_552), (true, vertices_584), (true, vertices_648), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_672), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 16, 20, 21, 23, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_327) then 14 else
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_181) then 18 else
  if p.val = (false, vertices_901) then 19 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
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

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 5, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_842, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_74, (by decide +kernel)⟩ ⟨vertices_842, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![2, 3, 4, 5]
  vertex := 8
  face := Sum.inl ⟨vertices_632, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_632, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
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

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![1, 0, 2, 3]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_654, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_654, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_774, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 1, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_262, (by decide +kernel)⟩ ⟨vertices_774, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_842, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 2, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_74, (by decide +kernel)⟩ ⟨vertices_842, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_172, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![1, 2, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_172, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_632, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![2, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_632, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_680, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![2, 4, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_168, (by decide +kernel)⟩ ⟨vertices_680, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_944, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![3, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_176, (by decide +kernel)⟩ ⟨vertices_944, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_848, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![3, 5, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_336, (by decide +kernel)⟩ ⟨vertices_848, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1386

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_one_six_1387.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1387

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_327 : Finset (Fin 10) := literalFinset [0, 1, 2, 6, 8] (by decide +kernel)
noncomputable def vertices_91 : Finset (Fin 10) := literalFinset [0, 1, 3, 4, 6] (by decide +kernel)
noncomputable def vertices_181 : Finset (Fin 10) := literalFinset [0, 2, 4, 5, 7] (by decide +kernel)
noncomputable def vertices_901 : Finset (Fin 10) := literalFinset [0, 2, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_465 : Finset (Fin 10) := literalFinset [0, 4, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_654 : Finset (Fin 10) := literalFinset [1, 2, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_774 : Finset (Fin 10) := literalFinset [1, 2, 8, 9] (by decide +kernel)
noncomputable def vertices_842 : Finset (Fin 10) := literalFinset [1, 3, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_172 : Finset (Fin 10) := literalFinset [2, 3, 5, 7] (by decide +kernel)
noncomputable def vertices_376 : Finset (Fin 10) := literalFinset [3, 4, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_680 : Finset (Fin 10) := literalFinset [3, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_808 : Finset (Fin 10) := literalFinset [3, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_944 : Finset (Fin 10) := literalFinset [4, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_27 : Finset (Fin 10) := literalFinset [0, 1, 3, 4] (by decide +kernel)
noncomputable def vertices_67 : Finset (Fin 10) := literalFinset [0, 1, 6] (by decide +kernel)
noncomputable def vertices_53 : Finset (Fin 10) := literalFinset [0, 2, 4, 5] (by decide +kernel)
noncomputable def vertices_133 : Finset (Fin 10) := literalFinset [0, 2, 7] (by decide +kernel)
noncomputable def vertices_261 : Finset (Fin 10) := literalFinset [0, 2, 8] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_145 : Finset (Fin 10) := literalFinset [0, 4, 7] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_385 : Finset (Fin 10) := literalFinset [0, 7, 8] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_262 : Finset (Fin 10) := literalFinset [1, 2, 8] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_74 : Finset (Fin 10) := literalFinset [1, 3, 6] (by decide +kernel)
noncomputable def vertices_522 : Finset (Fin 10) := literalFinset [1, 3, 9] (by decide +kernel)
noncomputable def vertices_322 : Finset (Fin 10) := literalFinset [1, 6, 8] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_140 : Finset (Fin 10) := literalFinset [2, 3, 7] (by decide +kernel)
noncomputable def vertices_164 : Finset (Fin 10) := literalFinset [2, 5, 7] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_56 : Finset (Fin 10) := literalFinset [3, 4, 5] (by decide +kernel)
noncomputable def vertices_88 : Finset (Fin 10) := literalFinset [3, 4, 6] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_552 : Finset (Fin 10) := literalFinset [3, 5, 9] (by decide +kernel)
noncomputable def vertices_328 : Finset (Fin 10) := literalFinset [3, 6, 8] (by decide +kernel)
noncomputable def vertices_648 : Finset (Fin 10) := literalFinset [3, 7, 9] (by decide +kernel)
noncomputable def vertices_776 : Finset (Fin 10) := literalFinset [3, 8, 9] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_327, vertices_91, vertices_181, vertices_901, vertices_465, vertices_654, vertices_774, vertices_842, vertices_172, vertices_376, vertices_680, vertices_808, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_53, vertices_133, vertices_261, vertices_81, vertices_145, vertices_321, vertices_385, vertices_14, vertices_262, vertices_518, vertices_74, vertices_522, vertices_322, vertices_770, vertices_44, vertices_140, vertices_164, vertices_644, vertices_772, vertices_56, vertices_88, vertices_168, vertices_296, vertices_552, vertices_328, vertices_648, vertices_776, vertices_176, vertices_304, vertices_336, vertices_400, vertices_672, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_327), (false, vertices_91), (false, vertices_181), (false, vertices_901), (false, vertices_465), (true, vertices_518), (true, vertices_522), (true, vertices_770), (true, vertices_140), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_328), (true, vertices_648), (true, vertices_776), (true, vertices_304), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 16, 20, 21, 23, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_327) then 14 else
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_181) then 18 else
  if p.val = (false, vertices_901) then 19 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_328) then 7 else
  if p.val = (true, vertices_648) then 8 else
  if p.val = (true, vertices_776) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
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

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 5, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_842, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_74, (by decide +kernel)⟩ ⟨vertices_842, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![2, 3, 4, 5]
  vertex := 7
  face := Sum.inl ⟨vertices_376, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_376, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
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

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![1, 0, 2, 3]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_654, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_654, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_774, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 1, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_262, (by decide +kernel)⟩ ⟨vertices_774, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_842, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 2, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_74, (by decide +kernel)⟩ ⟨vertices_842, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_172, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![1, 2, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_172, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_376, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![2, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_376, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_680, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![2, 4, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_168, (by decide +kernel)⟩ ⟨vertices_680, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_808, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![2, 4, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_296, (by decide +kernel)⟩ ⟨vertices_808, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_944, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .oneRow ![3, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_176, (by decide +kernel)⟩ ⟨vertices_944, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1387

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_one_six_1388.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1388

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_583 : Finset (Fin 10) := literalFinset [0, 1, 2, 6, 9] (by decide +kernel)
noncomputable def vertices_91 : Finset (Fin 10) := literalFinset [0, 1, 3, 4, 6] (by decide +kernel)
noncomputable def vertices_181 : Finset (Fin 10) := literalFinset [0, 2, 4, 5, 7] (by decide +kernel)
noncomputable def vertices_901 : Finset (Fin 10) := literalFinset [0, 2, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_465 : Finset (Fin 10) := literalFinset [0, 4, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_833 : Finset (Fin 10) := literalFinset [0, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_654 : Finset (Fin 10) := literalFinset [1, 2, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_842 : Finset (Fin 10) := literalFinset [1, 3, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_172 : Finset (Fin 10) := literalFinset [2, 3, 5, 7] (by decide +kernel)
noncomputable def vertices_376 : Finset (Fin 10) := literalFinset [3, 4, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_680 : Finset (Fin 10) := literalFinset [3, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_808 : Finset (Fin 10) := literalFinset [3, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_944 : Finset (Fin 10) := literalFinset [4, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_27 : Finset (Fin 10) := literalFinset [0, 1, 3, 4] (by decide +kernel)
noncomputable def vertices_67 : Finset (Fin 10) := literalFinset [0, 1, 6] (by decide +kernel)
noncomputable def vertices_53 : Finset (Fin 10) := literalFinset [0, 2, 4, 5] (by decide +kernel)
noncomputable def vertices_133 : Finset (Fin 10) := literalFinset [0, 2, 7] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_145 : Finset (Fin 10) := literalFinset [0, 4, 7] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_385 : Finset (Fin 10) := literalFinset [0, 7, 8] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_74 : Finset (Fin 10) := literalFinset [1, 3, 6] (by decide +kernel)
noncomputable def vertices_522 : Finset (Fin 10) := literalFinset [1, 3, 9] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_140 : Finset (Fin 10) := literalFinset [2, 3, 7] (by decide +kernel)
noncomputable def vertices_164 : Finset (Fin 10) := literalFinset [2, 5, 7] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_56 : Finset (Fin 10) := literalFinset [3, 4, 5] (by decide +kernel)
noncomputable def vertices_88 : Finset (Fin 10) := literalFinset [3, 4, 6] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_552 : Finset (Fin 10) := literalFinset [3, 5, 9] (by decide +kernel)
noncomputable def vertices_328 : Finset (Fin 10) := literalFinset [3, 6, 8] (by decide +kernel)
noncomputable def vertices_648 : Finset (Fin 10) := literalFinset [3, 7, 9] (by decide +kernel)
noncomputable def vertices_776 : Finset (Fin 10) := literalFinset [3, 8, 9] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_91, vertices_181, vertices_901, vertices_465, vertices_833, vertices_654, vertices_842, vertices_172, vertices_376, vertices_680, vertices_808, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_53, vertices_133, vertices_517, vertices_81, vertices_145, vertices_321, vertices_577, vertices_385, vertices_769, vertices_14, vertices_518, vertices_74, vertices_522, vertices_578, vertices_44, vertices_140, vertices_164, vertices_644, vertices_56, vertices_88, vertices_168, vertices_296, vertices_552, vertices_328, vertices_648, vertices_776, vertices_176, vertices_304, vertices_336, vertices_400, vertices_672, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_91), (false, vertices_181), (false, vertices_901), (false, vertices_465), (false, vertices_833), (true, vertices_522), (true, vertices_140), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_328), (true, vertices_648), (true, vertices_776), (true, vertices_304), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![12, 15, 19, 20, 22, 23, 24, 25, 26]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_583) then 13 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_181) then 17 else
  if p.val = (false, vertices_901) then 18 else
  if p.val = (false, vertices_465) then 21 else
  if p.val = (false, vertices_833) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_168) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_833), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
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
  frame := ![0, 1, 2, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_654, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_654, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 5, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_842, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_74, (by decide +kernel)⟩ ⟨vertices_842, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![2, 3, 4, 5]
  vertex := 7
  face := Sum.inl ⟨vertices_376, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_376, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
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

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![1, 0, 2, 3]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_654, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_654, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_842, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 2, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_74, (by decide +kernel)⟩ ⟨vertices_842, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_172, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![1, 2, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_172, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_376, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![2, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_376, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_680, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![2, 4, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_168, (by decide +kernel)⟩ ⟨vertices_680, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_808, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![2, 4, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_296, (by decide +kernel)⟩ ⟨vertices_808, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_944, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![3, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_176, (by decide +kernel)⟩ ⟨vertices_944, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1388

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_one_six_1389.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1389

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_91 : Finset (Fin 10) := literalFinset [0, 1, 3, 4, 6] (by decide +kernel)
noncomputable def vertices_173 : Finset (Fin 10) := literalFinset [0, 2, 3, 5, 7] (by decide +kernel)
noncomputable def vertices_457 : Finset (Fin 10) := literalFinset [0, 3, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_369 : Finset (Fin 10) := literalFinset [0, 4, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_929 : Finset (Fin 10) := literalFinset [0, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_654 : Finset (Fin 10) := literalFinset [1, 2, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_86 : Finset (Fin 10) := literalFinset [1, 2, 4, 6] (by decide +kernel)
noncomputable def vertices_582 : Finset (Fin 10) := literalFinset [1, 2, 6, 9] (by decide +kernel)
noncomputable def vertices_842 : Finset (Fin 10) := literalFinset [1, 3, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_692 : Finset (Fin 10) := literalFinset [2, 4, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_852 : Finset (Fin 10) := literalFinset [2, 4, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_904 : Finset (Fin 10) := literalFinset [3, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_816 : Finset (Fin 10) := literalFinset [4, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_27 : Finset (Fin 10) := literalFinset [0, 1, 3, 4] (by decide +kernel)
noncomputable def vertices_45 : Finset (Fin 10) := literalFinset [0, 2, 3, 5] (by decide +kernel)
noncomputable def vertices_73 : Finset (Fin 10) := literalFinset [0, 3, 6] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_161 : Finset (Fin 10) := literalFinset [0, 5, 7] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_385 : Finset (Fin 10) := literalFinset [0, 7, 8] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_22 : Finset (Fin 10) := literalFinset [1, 2, 4] (by decide +kernel)
noncomputable def vertices_70 : Finset (Fin 10) := literalFinset [1, 2, 6] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_74 : Finset (Fin 10) := literalFinset [1, 3, 6] (by decide +kernel)
noncomputable def vertices_522 : Finset (Fin 10) := literalFinset [1, 3, 9] (by decide +kernel)
noncomputable def vertices_82 : Finset (Fin 10) := literalFinset [1, 4, 6] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_140 : Finset (Fin 10) := literalFinset [2, 3, 7] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_532 : Finset (Fin 10) := literalFinset [2, 4, 9] (by decide +kernel)
noncomputable def vertices_164 : Finset (Fin 10) := literalFinset [2, 5, 7] (by decide +kernel)
noncomputable def vertices_580 : Finset (Fin 10) := literalFinset [2, 6, 9] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_328 : Finset (Fin 10) := literalFinset [3, 6, 8] (by decide +kernel)
noncomputable def vertices_392 : Finset (Fin 10) := literalFinset [3, 7, 8] (by decide +kernel)
noncomputable def vertices_648 : Finset (Fin 10) := literalFinset [3, 7, 9] (by decide +kernel)
noncomputable def vertices_776 : Finset (Fin 10) := literalFinset [3, 8, 9] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_784 : Finset (Fin 10) := literalFinset [4, 8, 9] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_369, vertices_929, vertices_654, vertices_86, vertices_582, vertices_842, vertices_692, vertices_852, vertices_904, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_161, vertices_289, vertices_321, vertices_385, vertices_14, vertices_22, vertices_70, vertices_518, vertices_74, vertices_522, vertices_82, vertices_578, vertices_140, vertices_52, vertices_84, vertices_532, vertices_164, vertices_580, vertices_644, vertices_328, vertices_392, vertices_648, vertices_776, vertices_304, vertices_560, vertices_336, vertices_784, vertices_672, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_369), (false, vertices_929), (true, vertices_70), (true, vertices_518), (true, vertices_522), (true, vertices_578), (true, vertices_84), (true, vertices_532), (true, vertices_580), (true, vertices_644), (true, vertices_648), (true, vertices_776), (true, vertices_560), (true, vertices_784), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 15, 18, 20, 22, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_173) then 17 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (false, vertices_929) then 23 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_580) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_648) then 8 else
  if p.val = (true, vertices_776) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
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
  frame := ![0, 2, 5, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_842, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_74, (by decide +kernel)⟩ ⟨vertices_842, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 3, 5, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_852, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_852, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![4, 6, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_654, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_654, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_86, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 1, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_86, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_582, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 1, 5, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_70, (by decide +kernel)⟩ ⟨vertices_582, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_842, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![0, 2, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_74, (by decide +kernel)⟩ ⟨vertices_842, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_692, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![1, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_692, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_852, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![1, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_852, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_904, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![2, 6, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_392, (by decide +kernel)⟩ ⟨vertices_904, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_816, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![3, 4, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_304, (by decide +kernel)⟩ ⟨vertices_816, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1389

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_one_six_1390.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1390

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_391 : Finset (Fin 10) := literalFinset [0, 1, 2, 7, 8] (by decide +kernel)
noncomputable def vertices_91 : Finset (Fin 10) := literalFinset [0, 1, 3, 4, 6] (by decide +kernel)
noncomputable def vertices_835 : Finset (Fin 10) := literalFinset [0, 1, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_181 : Finset (Fin 10) := literalFinset [0, 2, 4, 5, 7] (by decide +kernel)
noncomputable def vertices_465 : Finset (Fin 10) := literalFinset [0, 4, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_654 : Finset (Fin 10) := literalFinset [1, 2, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_586 : Finset (Fin 10) := literalFinset [1, 3, 6, 9] (by decide +kernel)
noncomputable def vertices_898 : Finset (Fin 10) := literalFinset [1, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_620 : Finset (Fin 10) := literalFinset [2, 3, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_676 : Finset (Fin 10) := literalFinset [2, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_376 : Finset (Fin 10) := literalFinset [3, 4, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_944 : Finset (Fin 10) := literalFinset [4, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_864 : Finset (Fin 10) := literalFinset [5, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_27 : Finset (Fin 10) := literalFinset [0, 1, 3, 4] (by decide +kernel)
noncomputable def vertices_67 : Finset (Fin 10) := literalFinset [0, 1, 6] (by decide +kernel)
noncomputable def vertices_259 : Finset (Fin 10) := literalFinset [0, 1, 8] (by decide +kernel)
noncomputable def vertices_53 : Finset (Fin 10) := literalFinset [0, 2, 4, 5] (by decide +kernel)
noncomputable def vertices_133 : Finset (Fin 10) := literalFinset [0, 2, 7] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_145 : Finset (Fin 10) := literalFinset [0, 4, 7] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_385 : Finset (Fin 10) := literalFinset [0, 7, 8] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_134 : Finset (Fin 10) := literalFinset [1, 2, 7] (by decide +kernel)
noncomputable def vertices_74 : Finset (Fin 10) := literalFinset [1, 3, 6] (by decide +kernel)
noncomputable def vertices_522 : Finset (Fin 10) := literalFinset [1, 3, 9] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_164 : Finset (Fin 10) := literalFinset [2, 5, 7] (by decide +kernel)
noncomputable def vertices_548 : Finset (Fin 10) := literalFinset [2, 5, 9] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_56 : Finset (Fin 10) := literalFinset [3, 4, 5] (by decide +kernel)
noncomputable def vertices_88 : Finset (Fin 10) := literalFinset [3, 4, 6] (by decide +kernel)
noncomputable def vertices_104 : Finset (Fin 10) := literalFinset [3, 5, 6] (by decide +kernel)
noncomputable def vertices_584 : Finset (Fin 10) := literalFinset [3, 6, 9] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_608 : Finset (Fin 10) := literalFinset [5, 6, 9] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_835, vertices_181, vertices_465, vertices_654, vertices_586, vertices_898, vertices_620, vertices_676, vertices_376, vertices_944, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_259, vertices_53, vertices_133, vertices_81, vertices_145, vertices_321, vertices_385, vertices_14, vertices_134, vertices_74, vertices_522, vertices_578, vertices_386, vertices_642, vertices_770, vertices_44, vertices_524, vertices_164, vertices_548, vertices_644, vertices_56, vertices_88, vertices_104, vertices_584, vertices_176, vertices_304, vertices_336, vertices_400, vertices_352, vertices_608, vertices_672, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_465), (true, vertices_522), (true, vertices_642), (true, vertices_524), (true, vertices_548), (true, vertices_644), (true, vertices_104), (true, vertices_584), (true, vertices_304), (true, vertices_352), (true, vertices_608), (true, vertices_672), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![16, 13, 20, 21, 23, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_91) then 18 else
  if p.val = (false, vertices_835) then 19 else
  if p.val = (false, vertices_181) then 15 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (true, vertices_522) then 0 else
  if p.val = (true, vertices_642) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_352) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_800) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
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

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 4, 5]
  vertex := 8
  face := Sum.inl ⟨vertices_620, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_620, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![2, 3, 4, 5]
  vertex := 7
  face := Sum.inl ⟨vertices_376, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_376, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
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

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 1, 2, 3]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_654, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_654, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_586, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 2, 5, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_74, (by decide +kernel)⟩ ⟨vertices_586, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_898, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 6, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_386, (by decide +kernel)⟩ ⟨vertices_898, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_620, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 2, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_620, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_676, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![1, 4, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_164, (by decide +kernel)⟩ ⟨vertices_676, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_376, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![2, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_376, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_944, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![3, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_176, (by decide +kernel)⟩ ⟨vertices_944, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_864, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![4, 5, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_352, (by decide +kernel)⟩ ⟨vertices_864, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1390

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_one_six_1391.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1391

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_91 : Finset (Fin 10) := literalFinset [0, 1, 3, 4, 6] (by decide +kernel)
noncomputable def vertices_173 : Finset (Fin 10) := literalFinset [0, 2, 3, 5, 7] (by decide +kernel)
noncomputable def vertices_457 : Finset (Fin 10) := literalFinset [0, 3, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_369 : Finset (Fin 10) := literalFinset [0, 4, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_929 : Finset (Fin 10) := literalFinset [0, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_142 : Finset (Fin 10) := literalFinset [1, 2, 3, 7] (by decide +kernel)
noncomputable def vertices_598 : Finset (Fin 10) := literalFinset [1, 2, 4, 6, 9] (by decide +kernel)
noncomputable def vertices_902 : Finset (Fin 10) := literalFinset [1, 2, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_842 : Finset (Fin 10) := literalFinset [1, 3, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_394 : Finset (Fin 10) := literalFinset [1, 3, 7, 8] (by decide +kernel)
noncomputable def vertices_692 : Finset (Fin 10) := literalFinset [2, 4, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_816 : Finset (Fin 10) := literalFinset [4, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_848 : Finset (Fin 10) := literalFinset [4, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_27 : Finset (Fin 10) := literalFinset [0, 1, 3, 4] (by decide +kernel)
noncomputable def vertices_45 : Finset (Fin 10) := literalFinset [0, 2, 3, 5] (by decide +kernel)
noncomputable def vertices_73 : Finset (Fin 10) := literalFinset [0, 3, 6] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_161 : Finset (Fin 10) := literalFinset [0, 5, 7] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_385 : Finset (Fin 10) := literalFinset [0, 7, 8] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_22 : Finset (Fin 10) := literalFinset [1, 2, 4] (by decide +kernel)
noncomputable def vertices_134 : Finset (Fin 10) := literalFinset [1, 2, 7] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_74 : Finset (Fin 10) := literalFinset [1, 3, 6] (by decide +kernel)
noncomputable def vertices_138 : Finset (Fin 10) := literalFinset [1, 3, 7] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_82 : Finset (Fin 10) := literalFinset [1, 4, 6] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_140 : Finset (Fin 10) := literalFinset [2, 3, 7] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_532 : Finset (Fin 10) := literalFinset [2, 4, 9] (by decide +kernel)
noncomputable def vertices_164 : Finset (Fin 10) := literalFinset [2, 5, 7] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_328 : Finset (Fin 10) := literalFinset [3, 6, 8] (by decide +kernel)
noncomputable def vertices_392 : Finset (Fin 10) := literalFinset [3, 7, 8] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_784 : Finset (Fin 10) := literalFinset [4, 8, 9] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_369, vertices_929, vertices_142, vertices_598, vertices_902, vertices_842, vertices_394, vertices_692, vertices_816, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_161, vertices_289, vertices_321, vertices_385, vertices_14, vertices_22, vertices_134, vertices_518, vertices_74, vertices_138, vertices_266, vertices_82, vertices_578, vertices_386, vertices_770, vertices_140, vertices_52, vertices_532, vertices_164, vertices_644, vertices_328, vertices_392, vertices_304, vertices_560, vertices_336, vertices_592, vertices_784, vertices_672, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_369), (false, vertices_929), (true, vertices_134), (true, vertices_518), (true, vertices_138), (true, vertices_266), (true, vertices_578), (true, vertices_386), (true, vertices_770), (true, vertices_532), (true, vertices_644), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 15, 18, 20, 22, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_173) then 17 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (false, vertices_929) then 23 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 5, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_842, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_74, (by decide +kernel)⟩ ⟨vertices_842, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 3, 5]
  vertex := 8
  face := Sum.inl ⟨vertices_598, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_598, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_902, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_134, (by decide +kernel)⟩ ⟨vertices_902, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
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

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![2, 5, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_142, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .fundamental ![0, 1, 2, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_142, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_598, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_598, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_902, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 1, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_134, (by decide +kernel)⟩ ⟨vertices_902, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_842, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![0, 2, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_74, (by decide +kernel)⟩ ⟨vertices_842, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_394, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![0, 2, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_138, (by decide +kernel)⟩ ⟨vertices_394, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_692, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![1, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_692, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_816, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![3, 4, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_304, (by decide +kernel)⟩ ⟨vertices_816, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_848, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![3, 5, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_336, (by decide +kernel)⟩ ⟨vertices_848, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1391

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_one_six_1392.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1392

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_91 : Finset (Fin 10) := literalFinset [0, 1, 3, 4, 6] (by decide +kernel)
noncomputable def vertices_173 : Finset (Fin 10) := literalFinset [0, 2, 3, 5, 7] (by decide +kernel)
noncomputable def vertices_457 : Finset (Fin 10) := literalFinset [0, 3, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_369 : Finset (Fin 10) := literalFinset [0, 4, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_929 : Finset (Fin 10) := literalFinset [0, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_142 : Finset (Fin 10) := literalFinset [1, 2, 3, 7] (by decide +kernel)
noncomputable def vertices_598 : Finset (Fin 10) := literalFinset [1, 2, 4, 6, 9] (by decide +kernel)
noncomputable def vertices_902 : Finset (Fin 10) := literalFinset [1, 2, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_842 : Finset (Fin 10) := literalFinset [1, 3, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_394 : Finset (Fin 10) := literalFinset [1, 3, 7, 8] (by decide +kernel)
noncomputable def vertices_692 : Finset (Fin 10) := literalFinset [2, 4, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_624 : Finset (Fin 10) := literalFinset [4, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_864 : Finset (Fin 10) := literalFinset [5, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_27 : Finset (Fin 10) := literalFinset [0, 1, 3, 4] (by decide +kernel)
noncomputable def vertices_45 : Finset (Fin 10) := literalFinset [0, 2, 3, 5] (by decide +kernel)
noncomputable def vertices_73 : Finset (Fin 10) := literalFinset [0, 3, 6] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_161 : Finset (Fin 10) := literalFinset [0, 5, 7] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_385 : Finset (Fin 10) := literalFinset [0, 7, 8] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_22 : Finset (Fin 10) := literalFinset [1, 2, 4] (by decide +kernel)
noncomputable def vertices_134 : Finset (Fin 10) := literalFinset [1, 2, 7] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_74 : Finset (Fin 10) := literalFinset [1, 3, 6] (by decide +kernel)
noncomputable def vertices_138 : Finset (Fin 10) := literalFinset [1, 3, 7] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_82 : Finset (Fin 10) := literalFinset [1, 4, 6] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_140 : Finset (Fin 10) := literalFinset [2, 3, 7] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_532 : Finset (Fin 10) := literalFinset [2, 4, 9] (by decide +kernel)
noncomputable def vertices_164 : Finset (Fin 10) := literalFinset [2, 5, 7] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_328 : Finset (Fin 10) := literalFinset [3, 6, 8] (by decide +kernel)
noncomputable def vertices_392 : Finset (Fin 10) := literalFinset [3, 7, 8] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_608 : Finset (Fin 10) := literalFinset [5, 6, 9] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_369, vertices_929, vertices_142, vertices_598, vertices_902, vertices_842, vertices_394, vertices_692, vertices_624, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_161, vertices_289, vertices_321, vertices_385, vertices_14, vertices_22, vertices_134, vertices_518, vertices_74, vertices_138, vertices_266, vertices_82, vertices_578, vertices_386, vertices_770, vertices_140, vertices_52, vertices_532, vertices_164, vertices_644, vertices_328, vertices_392, vertices_112, vertices_560, vertices_592, vertices_352, vertices_608, vertices_672, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_369), (false, vertices_929), (true, vertices_134), (true, vertices_518), (true, vertices_138), (true, vertices_266), (true, vertices_578), (true, vertices_386), (true, vertices_770), (true, vertices_532), (true, vertices_644), (true, vertices_560), (true, vertices_592), (true, vertices_608), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 15, 18, 20, 22, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_173) then 17 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (false, vertices_929) then 23 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_608) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 5, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_842, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_74, (by decide +kernel)⟩ ⟨vertices_842, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 3, 5]
  vertex := 8
  face := Sum.inl ⟨vertices_598, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_598, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_902, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_134, (by decide +kernel)⟩ ⟨vertices_902, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
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

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![2, 5, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_142, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .fundamental ![0, 1, 2, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_142, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_598, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_598, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_902, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 1, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_134, (by decide +kernel)⟩ ⟨vertices_902, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_842, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![0, 2, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_74, (by decide +kernel)⟩ ⟨vertices_842, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_394, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![0, 2, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_138, (by decide +kernel)⟩ ⟨vertices_394, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_692, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![1, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_692, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_624, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![3, 4, 5, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_624, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_864, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![4, 5, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_352, (by decide +kernel)⟩ ⟨vertices_864, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1392

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_one_six_1393.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1393

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_775 : Finset (Fin 10) := literalFinset [0, 1, 2, 8, 9] (by decide +kernel)
noncomputable def vertices_651 : Finset (Fin 10) := literalFinset [0, 1, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_267 : Finset (Fin 10) := literalFinset [0, 1, 3, 8] (by decide +kernel)
noncomputable def vertices_425 : Finset (Fin 10) := literalFinset [0, 3, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_721 : Finset (Fin 10) := literalFinset [0, 4, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_225 : Finset (Fin 10) := literalFinset [0, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_865 : Finset (Fin 10) := literalFinset [0, 5, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_126 : Finset (Fin 10) := literalFinset [1, 2, 3, 4, 5, 6] (by decide +kernel)
noncomputable def vertices_270 : Finset (Fin 10) := literalFinset [1, 2, 3, 8] (by decide +kernel)
noncomputable def vertices_662 : Finset (Fin 10) := literalFinset [1, 2, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_186 : Finset (Fin 10) := literalFinset [1, 3, 4, 5, 7] (by decide +kernel)
noncomputable def vertices_364 : Finset (Fin 10) := literalFinset [2, 3, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_852 : Finset (Fin 10) := literalFinset [2, 4, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_240 : Finset (Fin 10) := literalFinset [4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_259 : Finset (Fin 10) := literalFinset [0, 1, 8] (by decide +kernel)
noncomputable def vertices_515 : Finset (Fin 10) := literalFinset [0, 1, 9] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_265 : Finset (Fin 10) := literalFinset [0, 3, 8] (by decide +kernel)
noncomputable def vertices_97 : Finset (Fin 10) := literalFinset [0, 5, 6] (by decide +kernel)
noncomputable def vertices_161 : Finset (Fin 10) := literalFinset [0, 5, 7] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_193 : Finset (Fin 10) := literalFinset [0, 6, 7] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_22 : Finset (Fin 10) := literalFinset [1, 2, 4] (by decide +kernel)
noncomputable def vertices_262 : Finset (Fin 10) := literalFinset [1, 2, 8] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_58 : Finset (Fin 10) := literalFinset [1, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_138 : Finset (Fin 10) := literalFinset [1, 3, 7] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_146 : Finset (Fin 10) := literalFinset [1, 4, 7] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_108 : Finset (Fin 10) := literalFinset [2, 3, 5, 6] (by decide +kernel)
noncomputable def vertices_268 : Finset (Fin 10) := literalFinset [2, 3, 8] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_532 : Finset (Fin 10) := literalFinset [2, 4, 9] (by decide +kernel)
noncomputable def vertices_324 : Finset (Fin 10) := literalFinset [2, 6, 8] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_208 : Finset (Fin 10) := literalFinset [4, 6, 7] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_224 : Finset (Fin 10) := literalFinset [5, 6, 7] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_651, vertices_267, vertices_425, vertices_721, vertices_225, vertices_865, vertices_126, vertices_270, vertices_662, vertices_186, vertices_364, vertices_852, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_259, vertices_515, vertices_137, vertices_265, vertices_97, vertices_161, vertices_289, vertices_193, vertices_577, vertices_641, vertices_769, vertices_14, vertices_22, vertices_262, vertices_518, vertices_58, vertices_138, vertices_266, vertices_146, vertices_642, vertices_108, vertices_268, vertices_84, vertices_532, vertices_324, vertices_772, vertices_168, vertices_296, vertices_112, vertices_176, vertices_208, vertices_592, vertices_656, vertices_224, vertices_352, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_651), (false, vertices_267), (false, vertices_425), (false, vertices_721), (false, vertices_225), (false, vertices_865), (true, vertices_14), (true, vertices_22), (true, vertices_58), (true, vertices_146), (true, vertices_108), (true, vertices_268), (true, vertices_84), (true, vertices_532), (true, vertices_324), (true, vertices_112), (true, vertices_176)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![11, 15, 17, 19, 21, 23, 24, 25, 26]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 12 else
  if p.val = (false, vertices_651) then 13 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_425) then 18 else
  if p.val = (false, vertices_721) then 20 else
  if p.val = (false, vertices_225) then 1 else
  if p.val = (false, vertices_865) then 22 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_22) then 3 else
  if p.val = (true, vertices_58) then 14 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_108) then 16 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_176) then 10 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_225), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_58), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(true, vertices_108), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 23 => Sum.inl 5
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
  frame := ![0, 1, 2, 3]
  vertex := 4
  face := Sum.inl ⟨vertices_126, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_126, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 2, 3]
  vertex := 5
  face := Sum.inl ⟨vertices_126, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_126, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 3, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_662, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_662, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 3, 5, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_852, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_852, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![4, 2, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_126, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .fundamental ![0, 1, 2, 3] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_126, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_270, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 1, 2, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_270, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_662, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 1, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_662, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_186, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fromLargerFacet ![0, 2, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_186, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_58, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_126, by decide +kernel⟩ ![0, 1, 2, 3]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_126, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_364, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fromLargerFacet ![1, 2, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_108, (by decide +kernel)⟩ ⟨vertices_364, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_108, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_126, by decide +kernel⟩ ![0, 1, 2, 3]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_126, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_852, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![1, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_852, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_240, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![3, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_240, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1393

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_one_six_1394.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1394

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_775 : Finset (Fin 10) := literalFinset [0, 1, 2, 8, 9] (by decide +kernel)
noncomputable def vertices_651 : Finset (Fin 10) := literalFinset [0, 1, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_267 : Finset (Fin 10) := literalFinset [0, 1, 3, 8] (by decide +kernel)
noncomputable def vertices_425 : Finset (Fin 10) := literalFinset [0, 3, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_113 : Finset (Fin 10) := literalFinset [0, 4, 5, 6] (by decide +kernel)
noncomputable def vertices_177 : Finset (Fin 10) := literalFinset [0, 4, 5, 7] (by decide +kernel)
noncomputable def vertices_721 : Finset (Fin 10) := literalFinset [0, 4, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_865 : Finset (Fin 10) := literalFinset [0, 5, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_126 : Finset (Fin 10) := literalFinset [1, 2, 3, 4, 5, 6] (by decide +kernel)
noncomputable def vertices_270 : Finset (Fin 10) := literalFinset [1, 2, 3, 8] (by decide +kernel)
noncomputable def vertices_662 : Finset (Fin 10) := literalFinset [1, 2, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_186 : Finset (Fin 10) := literalFinset [1, 3, 4, 5, 7] (by decide +kernel)
noncomputable def vertices_364 : Finset (Fin 10) := literalFinset [2, 3, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_852 : Finset (Fin 10) := literalFinset [2, 4, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_259 : Finset (Fin 10) := literalFinset [0, 1, 8] (by decide +kernel)
noncomputable def vertices_515 : Finset (Fin 10) := literalFinset [0, 1, 9] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_265 : Finset (Fin 10) := literalFinset [0, 3, 8] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_145 : Finset (Fin 10) := literalFinset [0, 4, 7] (by decide +kernel)
noncomputable def vertices_97 : Finset (Fin 10) := literalFinset [0, 5, 6] (by decide +kernel)
noncomputable def vertices_161 : Finset (Fin 10) := literalFinset [0, 5, 7] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_22 : Finset (Fin 10) := literalFinset [1, 2, 4] (by decide +kernel)
noncomputable def vertices_262 : Finset (Fin 10) := literalFinset [1, 2, 8] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_58 : Finset (Fin 10) := literalFinset [1, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_138 : Finset (Fin 10) := literalFinset [1, 3, 7] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_146 : Finset (Fin 10) := literalFinset [1, 4, 7] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_108 : Finset (Fin 10) := literalFinset [2, 3, 5, 6] (by decide +kernel)
noncomputable def vertices_268 : Finset (Fin 10) := literalFinset [2, 3, 8] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_532 : Finset (Fin 10) := literalFinset [2, 4, 9] (by decide +kernel)
noncomputable def vertices_324 : Finset (Fin 10) := literalFinset [2, 6, 8] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_651, vertices_267, vertices_425, vertices_113, vertices_177, vertices_721, vertices_865, vertices_126, vertices_270, vertices_662, vertices_186, vertices_364, vertices_852] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_259, vertices_515, vertices_137, vertices_265, vertices_49, vertices_81, vertices_145, vertices_97, vertices_161, vertices_289, vertices_577, vertices_641, vertices_769, vertices_14, vertices_22, vertices_262, vertices_518, vertices_58, vertices_138, vertices_266, vertices_146, vertices_642, vertices_108, vertices_268, vertices_84, vertices_532, vertices_324, vertices_772, vertices_168, vertices_296, vertices_112, vertices_176, vertices_592, vertices_656, vertices_352, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_651), (false, vertices_267), (false, vertices_425), (false, vertices_113), (false, vertices_177), (false, vertices_721), (false, vertices_865), (true, vertices_14), (true, vertices_22), (true, vertices_58), (true, vertices_146), (true, vertices_108), (true, vertices_268), (true, vertices_84), (true, vertices_532), (true, vertices_324)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![10, 14, 16, 18, 20, 22, 23, 24, 25]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 11 else
  if p.val = (false, vertices_651) then 12 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_425) then 17 else
  if p.val = (false, vertices_113) then 1 else
  if p.val = (false, vertices_177) then 2 else
  if p.val = (false, vertices_721) then 19 else
  if p.val = (false, vertices_865) then 21 else
  if p.val = (true, vertices_14) then 3 else
  if p.val = (true, vertices_22) then 4 else
  if p.val = (true, vertices_58) then 13 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_108) then 15 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_324) then 9 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_113), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_177), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_58), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(true, vertices_108), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
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
  frameSize := 4
  frame := ![0, 1, 2, 3]
  vertex := 4
  face := Sum.inl ⟨vertices_126, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_126, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 2, 3]
  vertex := 5
  face := Sum.inl ⟨vertices_126, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_126, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 3, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_662, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_662, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 3, 5, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_852, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_852, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![4, 2, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_126, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .fundamental ![0, 1, 2, 3] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_126, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_270, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 1, 2, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_270, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_662, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 1, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_662, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_186, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fromLargerFacet ![0, 2, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_186, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_58, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_126, by decide +kernel⟩ ![0, 1, 2, 3]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_126, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_364, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fromLargerFacet ![1, 2, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_108, (by decide +kernel)⟩ ⟨vertices_364, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_108, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_126, by decide +kernel⟩ ![0, 1, 2, 3]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_126, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_852, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![1, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_852, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1394

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_one_six_1395.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1395

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_91 : Finset (Fin 10) := literalFinset [0, 1, 3, 4, 6] (by decide +kernel)
noncomputable def vertices_173 : Finset (Fin 10) := literalFinset [0, 2, 3, 5, 7] (by decide +kernel)
noncomputable def vertices_457 : Finset (Fin 10) := literalFinset [0, 3, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_369 : Finset (Fin 10) := literalFinset [0, 4, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_929 : Finset (Fin 10) := literalFinset [0, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_270 : Finset (Fin 10) := literalFinset [1, 2, 3, 8] (by decide +kernel)
noncomputable def vertices_598 : Finset (Fin 10) := literalFinset [1, 2, 4, 6, 9] (by decide +kernel)
noncomputable def vertices_902 : Finset (Fin 10) := literalFinset [1, 2, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_842 : Finset (Fin 10) := literalFinset [1, 3, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_396 : Finset (Fin 10) := literalFinset [2, 3, 7, 8] (by decide +kernel)
noncomputable def vertices_692 : Finset (Fin 10) := literalFinset [2, 4, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_816 : Finset (Fin 10) := literalFinset [4, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_848 : Finset (Fin 10) := literalFinset [4, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_27 : Finset (Fin 10) := literalFinset [0, 1, 3, 4] (by decide +kernel)
noncomputable def vertices_45 : Finset (Fin 10) := literalFinset [0, 2, 3, 5] (by decide +kernel)
noncomputable def vertices_73 : Finset (Fin 10) := literalFinset [0, 3, 6] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_161 : Finset (Fin 10) := literalFinset [0, 5, 7] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_385 : Finset (Fin 10) := literalFinset [0, 7, 8] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_22 : Finset (Fin 10) := literalFinset [1, 2, 4] (by decide +kernel)
noncomputable def vertices_262 : Finset (Fin 10) := literalFinset [1, 2, 8] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_74 : Finset (Fin 10) := literalFinset [1, 3, 6] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_82 : Finset (Fin 10) := literalFinset [1, 4, 6] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_140 : Finset (Fin 10) := literalFinset [2, 3, 7] (by decide +kernel)
noncomputable def vertices_268 : Finset (Fin 10) := literalFinset [2, 3, 8] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_532 : Finset (Fin 10) := literalFinset [2, 4, 9] (by decide +kernel)
noncomputable def vertices_164 : Finset (Fin 10) := literalFinset [2, 5, 7] (by decide +kernel)
noncomputable def vertices_388 : Finset (Fin 10) := literalFinset [2, 7, 8] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_328 : Finset (Fin 10) := literalFinset [3, 6, 8] (by decide +kernel)
noncomputable def vertices_392 : Finset (Fin 10) := literalFinset [3, 7, 8] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_784 : Finset (Fin 10) := literalFinset [4, 8, 9] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_369, vertices_929, vertices_270, vertices_598, vertices_902, vertices_842, vertices_396, vertices_692, vertices_816, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_161, vertices_289, vertices_321, vertices_385, vertices_14, vertices_22, vertices_262, vertices_518, vertices_74, vertices_266, vertices_82, vertices_578, vertices_770, vertices_140, vertices_268, vertices_52, vertices_532, vertices_164, vertices_388, vertices_644, vertices_328, vertices_392, vertices_304, vertices_560, vertices_336, vertices_592, vertices_784, vertices_672, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_369), (false, vertices_929), (true, vertices_262), (true, vertices_518), (true, vertices_266), (true, vertices_578), (true, vertices_770), (true, vertices_268), (true, vertices_532), (true, vertices_388), (true, vertices_644), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 15, 18, 20, 22, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_173) then 17 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (false, vertices_929) then 23 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 5, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_842, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_74, (by decide +kernel)⟩ ⟨vertices_842, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 3, 5]
  vertex := 8
  face := Sum.inl ⟨vertices_598, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_598, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_902, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_262, (by decide +kernel)⟩ ⟨vertices_902, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
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

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![2, 5, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_270, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .fundamental ![0, 1, 2, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_270, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_598, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_598, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_902, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 1, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_262, (by decide +kernel)⟩ ⟨vertices_902, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_842, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![0, 2, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_74, (by decide +kernel)⟩ ⟨vertices_842, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_396, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![1, 2, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_140, (by decide +kernel)⟩ ⟨vertices_396, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_692, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![1, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_692, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_816, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![3, 4, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_304, (by decide +kernel)⟩ ⟨vertices_816, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_848, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![3, 5, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_336, (by decide +kernel)⟩ ⟨vertices_848, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1395

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_one_six_1396.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1396

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_91 : Finset (Fin 10) := literalFinset [0, 1, 3, 4, 6] (by decide +kernel)
noncomputable def vertices_173 : Finset (Fin 10) := literalFinset [0, 2, 3, 5, 7] (by decide +kernel)
noncomputable def vertices_457 : Finset (Fin 10) := literalFinset [0, 3, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_369 : Finset (Fin 10) := literalFinset [0, 4, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_929 : Finset (Fin 10) := literalFinset [0, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_270 : Finset (Fin 10) := literalFinset [1, 2, 3, 8] (by decide +kernel)
noncomputable def vertices_598 : Finset (Fin 10) := literalFinset [1, 2, 4, 6, 9] (by decide +kernel)
noncomputable def vertices_902 : Finset (Fin 10) := literalFinset [1, 2, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_842 : Finset (Fin 10) := literalFinset [1, 3, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_396 : Finset (Fin 10) := literalFinset [2, 3, 7, 8] (by decide +kernel)
noncomputable def vertices_692 : Finset (Fin 10) := literalFinset [2, 4, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_624 : Finset (Fin 10) := literalFinset [4, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_864 : Finset (Fin 10) := literalFinset [5, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_27 : Finset (Fin 10) := literalFinset [0, 1, 3, 4] (by decide +kernel)
noncomputable def vertices_45 : Finset (Fin 10) := literalFinset [0, 2, 3, 5] (by decide +kernel)
noncomputable def vertices_73 : Finset (Fin 10) := literalFinset [0, 3, 6] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_161 : Finset (Fin 10) := literalFinset [0, 5, 7] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_385 : Finset (Fin 10) := literalFinset [0, 7, 8] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_22 : Finset (Fin 10) := literalFinset [1, 2, 4] (by decide +kernel)
noncomputable def vertices_262 : Finset (Fin 10) := literalFinset [1, 2, 8] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_74 : Finset (Fin 10) := literalFinset [1, 3, 6] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_82 : Finset (Fin 10) := literalFinset [1, 4, 6] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_140 : Finset (Fin 10) := literalFinset [2, 3, 7] (by decide +kernel)
noncomputable def vertices_268 : Finset (Fin 10) := literalFinset [2, 3, 8] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_532 : Finset (Fin 10) := literalFinset [2, 4, 9] (by decide +kernel)
noncomputable def vertices_164 : Finset (Fin 10) := literalFinset [2, 5, 7] (by decide +kernel)
noncomputable def vertices_388 : Finset (Fin 10) := literalFinset [2, 7, 8] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_328 : Finset (Fin 10) := literalFinset [3, 6, 8] (by decide +kernel)
noncomputable def vertices_392 : Finset (Fin 10) := literalFinset [3, 7, 8] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_608 : Finset (Fin 10) := literalFinset [5, 6, 9] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_91, vertices_173, vertices_457, vertices_369, vertices_929, vertices_270, vertices_598, vertices_902, vertices_842, vertices_396, vertices_692, vertices_624, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_45, vertices_73, vertices_137, vertices_49, vertices_81, vertices_161, vertices_289, vertices_321, vertices_385, vertices_14, vertices_22, vertices_262, vertices_518, vertices_74, vertices_266, vertices_82, vertices_578, vertices_770, vertices_140, vertices_268, vertices_52, vertices_532, vertices_164, vertices_388, vertices_644, vertices_328, vertices_392, vertices_112, vertices_560, vertices_592, vertices_352, vertices_608, vertices_672, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_91), (false, vertices_173), (false, vertices_457), (false, vertices_369), (false, vertices_929), (true, vertices_262), (true, vertices_518), (true, vertices_266), (true, vertices_578), (true, vertices_770), (true, vertices_268), (true, vertices_532), (true, vertices_388), (true, vertices_644), (true, vertices_560), (true, vertices_592), (true, vertices_608), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 15, 18, 20, 22, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_173) then 17 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (false, vertices_929) then 23 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_608) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 5, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_842, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_74, (by decide +kernel)⟩ ⟨vertices_842, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 3, 5]
  vertex := 8
  face := Sum.inl ⟨vertices_598, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_598, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_902, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_262, (by decide +kernel)⟩ ⟨vertices_902, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
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

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![2, 5, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_270, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .fundamental ![0, 1, 2, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_270, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_598, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_598, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_902, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 1, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_262, (by decide +kernel)⟩ ⟨vertices_902, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_842, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![0, 2, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_74, (by decide +kernel)⟩ ⟨vertices_842, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_396, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![1, 2, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_140, (by decide +kernel)⟩ ⟨vertices_396, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_692, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![1, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_692, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_624, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![3, 4, 5, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_624, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_864, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![4, 5, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_352, (by decide +kernel)⟩ ⟨vertices_864, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1396

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_one_six_1397.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1397

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_15 : Finset (Fin 10) := literalFinset [0, 1, 2, 3] (by decide +kernel)
noncomputable def vertices_775 : Finset (Fin 10) := literalFinset [0, 1, 2, 8, 9] (by decide +kernel)
noncomputable def vertices_651 : Finset (Fin 10) := literalFinset [0, 1, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_269 : Finset (Fin 10) := literalFinset [0, 2, 3, 8] (by decide +kernel)
noncomputable def vertices_425 : Finset (Fin 10) := literalFinset [0, 3, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_113 : Finset (Fin 10) := literalFinset [0, 4, 5, 6] (by decide +kernel)
noncomputable def vertices_177 : Finset (Fin 10) := literalFinset [0, 4, 5, 7] (by decide +kernel)
noncomputable def vertices_721 : Finset (Fin 10) := literalFinset [0, 4, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_865 : Finset (Fin 10) := literalFinset [0, 5, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_126 : Finset (Fin 10) := literalFinset [1, 2, 3, 4, 5, 6] (by decide +kernel)
noncomputable def vertices_662 : Finset (Fin 10) := literalFinset [1, 2, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_186 : Finset (Fin 10) := literalFinset [1, 3, 4, 5, 7] (by decide +kernel)
noncomputable def vertices_364 : Finset (Fin 10) := literalFinset [2, 3, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_852 : Finset (Fin 10) := literalFinset [2, 4, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_515 : Finset (Fin 10) := literalFinset [0, 1, 9] (by decide +kernel)
noncomputable def vertices_13 : Finset (Fin 10) := literalFinset [0, 2, 3] (by decide +kernel)
noncomputable def vertices_261 : Finset (Fin 10) := literalFinset [0, 2, 8] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_265 : Finset (Fin 10) := literalFinset [0, 3, 8] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_145 : Finset (Fin 10) := literalFinset [0, 4, 7] (by decide +kernel)
noncomputable def vertices_97 : Finset (Fin 10) := literalFinset [0, 5, 6] (by decide +kernel)
noncomputable def vertices_161 : Finset (Fin 10) := literalFinset [0, 5, 7] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_22 : Finset (Fin 10) := literalFinset [1, 2, 4] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_58 : Finset (Fin 10) := literalFinset [1, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_138 : Finset (Fin 10) := literalFinset [1, 3, 7] (by decide +kernel)
noncomputable def vertices_146 : Finset (Fin 10) := literalFinset [1, 4, 7] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_108 : Finset (Fin 10) := literalFinset [2, 3, 5, 6] (by decide +kernel)
noncomputable def vertices_268 : Finset (Fin 10) := literalFinset [2, 3, 8] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_532 : Finset (Fin 10) := literalFinset [2, 4, 9] (by decide +kernel)
noncomputable def vertices_324 : Finset (Fin 10) := literalFinset [2, 6, 8] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_15, vertices_775, vertices_651, vertices_269, vertices_425, vertices_113, vertices_177, vertices_721, vertices_865, vertices_126, vertices_662, vertices_186, vertices_364, vertices_852] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_13, vertices_261, vertices_137, vertices_265, vertices_49, vertices_81, vertices_145, vertices_97, vertices_161, vertices_289, vertices_577, vertices_641, vertices_769, vertices_14, vertices_22, vertices_518, vertices_58, vertices_138, vertices_146, vertices_642, vertices_108, vertices_268, vertices_84, vertices_532, vertices_324, vertices_772, vertices_168, vertices_296, vertices_112, vertices_176, vertices_592, vertices_656, vertices_352, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_15), (false, vertices_775), (false, vertices_651), (false, vertices_269), (false, vertices_425), (false, vertices_113), (false, vertices_177), (false, vertices_721), (false, vertices_865), (true, vertices_22), (true, vertices_58), (true, vertices_146), (true, vertices_108), (true, vertices_84), (true, vertices_532), (true, vertices_324)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![9, 13, 15, 17, 19, 21, 22, 23, 24]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_15) then 0 else
  if p.val = (false, vertices_775) then 10 else
  if p.val = (false, vertices_651) then 11 else
  if p.val = (false, vertices_269) then 1 else
  if p.val = (false, vertices_425) then 16 else
  if p.val = (false, vertices_113) then 2 else
  if p.val = (false, vertices_177) then 3 else
  if p.val = (false, vertices_721) then 18 else
  if p.val = (false, vertices_865) then 20 else
  if p.val = (true, vertices_22) then 4 else
  if p.val = (true, vertices_58) then 12 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_108) then 14 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_324) then 8 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_15), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_269), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_113), by decide +kernel⟩
  | 3 => Sum.inr ⟨(false, vertices_177), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_58), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(true, vertices_108), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
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
  frame := ![0, 1, 2, 3]
  vertex := 4
  face := Sum.inl ⟨vertices_126, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_126, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 2, 3]
  vertex := 5
  face := Sum.inl ⟨vertices_126, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_126, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 3, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_662, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_662, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 3, 5, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_852, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_852, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![4, 2, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_126, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .fundamental ![0, 1, 2, 3] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_126, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_662, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_662, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_186, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fromLargerFacet ![0, 2, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_58, (by decide +kernel)⟩ ⟨vertices_186, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_58, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_126, by decide +kernel⟩ ![0, 1, 2, 3]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_126, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_364, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fromLargerFacet ![1, 2, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_108, (by decide +kernel)⟩ ⟨vertices_364, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    ⟨vertices_108, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨vertices_126, by decide +kernel⟩ ![0, 1, 2, 3]
    (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_126, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_852, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![1, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_852, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1397

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_one_six_1398.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1398

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_391 : Finset (Fin 10) := literalFinset [0, 1, 2, 7, 8] (by decide +kernel)
noncomputable def vertices_91 : Finset (Fin 10) := literalFinset [0, 1, 3, 4, 6] (by decide +kernel)
noncomputable def vertices_835 : Finset (Fin 10) := literalFinset [0, 1, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_181 : Finset (Fin 10) := literalFinset [0, 2, 4, 5, 7] (by decide +kernel)
noncomputable def vertices_465 : Finset (Fin 10) := literalFinset [0, 4, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_590 : Finset (Fin 10) := literalFinset [1, 2, 3, 6, 9] (by decide +kernel)
noncomputable def vertices_774 : Finset (Fin 10) := literalFinset [1, 2, 8, 9] (by decide +kernel)
noncomputable def vertices_684 : Finset (Fin 10) := literalFinset [2, 3, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_900 : Finset (Fin 10) := literalFinset [2, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_376 : Finset (Fin 10) := literalFinset [3, 4, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_808 : Finset (Fin 10) := literalFinset [3, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_840 : Finset (Fin 10) := literalFinset [3, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_944 : Finset (Fin 10) := literalFinset [4, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_27 : Finset (Fin 10) := literalFinset [0, 1, 3, 4] (by decide +kernel)
noncomputable def vertices_67 : Finset (Fin 10) := literalFinset [0, 1, 6] (by decide +kernel)
noncomputable def vertices_259 : Finset (Fin 10) := literalFinset [0, 1, 8] (by decide +kernel)
noncomputable def vertices_53 : Finset (Fin 10) := literalFinset [0, 2, 4, 5] (by decide +kernel)
noncomputable def vertices_133 : Finset (Fin 10) := literalFinset [0, 2, 7] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_145 : Finset (Fin 10) := literalFinset [0, 4, 7] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_385 : Finset (Fin 10) := literalFinset [0, 7, 8] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_262 : Finset (Fin 10) := literalFinset [1, 2, 8] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_74 : Finset (Fin 10) := literalFinset [1, 3, 6] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_164 : Finset (Fin 10) := literalFinset [2, 5, 7] (by decide +kernel)
noncomputable def vertices_388 : Finset (Fin 10) := literalFinset [2, 7, 8] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_56 : Finset (Fin 10) := literalFinset [3, 4, 5] (by decide +kernel)
noncomputable def vertices_88 : Finset (Fin 10) := literalFinset [3, 4, 6] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_552 : Finset (Fin 10) := literalFinset [3, 5, 9] (by decide +kernel)
noncomputable def vertices_328 : Finset (Fin 10) := literalFinset [3, 6, 8] (by decide +kernel)
noncomputable def vertices_584 : Finset (Fin 10) := literalFinset [3, 6, 9] (by decide +kernel)
noncomputable def vertices_776 : Finset (Fin 10) := literalFinset [3, 8, 9] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_835, vertices_181, vertices_465, vertices_590, vertices_774, vertices_684, vertices_900, vertices_376, vertices_808, vertices_840, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_259, vertices_53, vertices_133, vertices_81, vertices_145, vertices_321, vertices_385, vertices_14, vertices_262, vertices_518, vertices_74, vertices_578, vertices_770, vertices_44, vertices_524, vertices_164, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_296, vertices_552, vertices_328, vertices_584, vertices_776, vertices_176, vertices_304, vertices_336, vertices_400, vertices_672, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_465), (true, vertices_518), (true, vertices_524), (true, vertices_644), (true, vertices_772), (true, vertices_296), (true, vertices_552), (true, vertices_328), (true, vertices_584), (true, vertices_776), (true, vertices_304), (true, vertices_672), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![16, 13, 20, 21, 23, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_91) then 18 else
  if p.val = (false, vertices_835) then 19 else
  if p.val = (false, vertices_181) then 15 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_644) then 2 else
  if p.val = (true, vertices_772) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_584) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_800) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 2, 5]
  vertex := 8
  face := Sum.inl ⟨vertices_590, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_590, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 4, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_684, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_684, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![2, 3, 4, 5]
  vertex := 7
  face := Sum.inl ⟨vertices_376, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_376, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
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

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 1, 2, 3]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_590, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_590, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_774, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 1, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_262, (by decide +kernel)⟩ ⟨vertices_774, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_684, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![1, 2, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_684, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_900, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![1, 6, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_388, (by decide +kernel)⟩ ⟨vertices_900, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_376, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![2, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_376, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_808, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![2, 4, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_296, (by decide +kernel)⟩ ⟨vertices_808, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_840, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![2, 5, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_328, (by decide +kernel)⟩ ⟨vertices_840, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_944, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .oneRow ![3, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_176, (by decide +kernel)⟩ ⟨vertices_944, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1398

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_one_six_1399.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1399

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_391 : Finset (Fin 10) := literalFinset [0, 1, 2, 7, 8] (by decide +kernel)
noncomputable def vertices_91 : Finset (Fin 10) := literalFinset [0, 1, 3, 4, 6] (by decide +kernel)
noncomputable def vertices_835 : Finset (Fin 10) := literalFinset [0, 1, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_181 : Finset (Fin 10) := literalFinset [0, 2, 4, 5, 7] (by decide +kernel)
noncomputable def vertices_465 : Finset (Fin 10) := literalFinset [0, 4, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_590 : Finset (Fin 10) := literalFinset [1, 2, 3, 6, 9] (by decide +kernel)
noncomputable def vertices_774 : Finset (Fin 10) := literalFinset [1, 2, 8, 9] (by decide +kernel)
noncomputable def vertices_684 : Finset (Fin 10) := literalFinset [2, 3, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_900 : Finset (Fin 10) := literalFinset [2, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_376 : Finset (Fin 10) := literalFinset [3, 4, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_616 : Finset (Fin 10) := literalFinset [3, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_944 : Finset (Fin 10) := literalFinset [4, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_864 : Finset (Fin 10) := literalFinset [5, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_27 : Finset (Fin 10) := literalFinset [0, 1, 3, 4] (by decide +kernel)
noncomputable def vertices_67 : Finset (Fin 10) := literalFinset [0, 1, 6] (by decide +kernel)
noncomputable def vertices_259 : Finset (Fin 10) := literalFinset [0, 1, 8] (by decide +kernel)
noncomputable def vertices_53 : Finset (Fin 10) := literalFinset [0, 2, 4, 5] (by decide +kernel)
noncomputable def vertices_133 : Finset (Fin 10) := literalFinset [0, 2, 7] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_145 : Finset (Fin 10) := literalFinset [0, 4, 7] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_385 : Finset (Fin 10) := literalFinset [0, 7, 8] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_262 : Finset (Fin 10) := literalFinset [1, 2, 8] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_74 : Finset (Fin 10) := literalFinset [1, 3, 6] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_164 : Finset (Fin 10) := literalFinset [2, 5, 7] (by decide +kernel)
noncomputable def vertices_388 : Finset (Fin 10) := literalFinset [2, 7, 8] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_56 : Finset (Fin 10) := literalFinset [3, 4, 5] (by decide +kernel)
noncomputable def vertices_88 : Finset (Fin 10) := literalFinset [3, 4, 6] (by decide +kernel)
noncomputable def vertices_104 : Finset (Fin 10) := literalFinset [3, 5, 6] (by decide +kernel)
noncomputable def vertices_552 : Finset (Fin 10) := literalFinset [3, 5, 9] (by decide +kernel)
noncomputable def vertices_584 : Finset (Fin 10) := literalFinset [3, 6, 9] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_608 : Finset (Fin 10) := literalFinset [5, 6, 9] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_91, vertices_835, vertices_181, vertices_465, vertices_590, vertices_774, vertices_684, vertices_900, vertices_376, vertices_616, vertices_944, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_259, vertices_53, vertices_133, vertices_81, vertices_145, vertices_321, vertices_385, vertices_14, vertices_262, vertices_518, vertices_74, vertices_578, vertices_770, vertices_44, vertices_524, vertices_164, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_104, vertices_552, vertices_584, vertices_176, vertices_304, vertices_336, vertices_400, vertices_352, vertices_608, vertices_672, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_91), (false, vertices_835), (false, vertices_181), (false, vertices_465), (true, vertices_518), (true, vertices_524), (true, vertices_644), (true, vertices_772), (true, vertices_104), (true, vertices_552), (true, vertices_584), (true, vertices_304), (true, vertices_352), (true, vertices_608), (true, vertices_672), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![16, 13, 20, 21, 23, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_91) then 18 else
  if p.val = (false, vertices_835) then 19 else
  if p.val = (false, vertices_181) then 15 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_644) then 2 else
  if p.val = (true, vertices_772) then 3 else
  if p.val = (true, vertices_104) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_352) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_800) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 2, 5]
  vertex := 8
  face := Sum.inl ⟨vertices_590, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_590, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 4, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_684, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_684, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![2, 3, 4, 5]
  vertex := 7
  face := Sum.inl ⟨vertices_376, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_376, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
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

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 1, 2, 3]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_590, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_590, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_774, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 1, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_262, (by decide +kernel)⟩ ⟨vertices_774, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_684, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![1, 2, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_684, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_900, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![1, 6, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_388, (by decide +kernel)⟩ ⟨vertices_900, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_376, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![2, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_376, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_616, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![2, 4, 5, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_104, (by decide +kernel)⟩ ⟨vertices_616, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_944, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![3, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_176, (by decide +kernel)⟩ ⟨vertices_944, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_864, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![4, 5, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_352, (by decide +kernel)⟩ ⟨vertices_864, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1399

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_1590 : Certifies 1590 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1365.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1591 : Certifies 1591 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1366.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1592 : Certifies 1592 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1367.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1593 : Certifies 1593 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1368.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1594 : Certifies 1594 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1369.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1595 : Certifies 1595 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1370.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1596 : Certifies 1596 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1371.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1597 : Certifies 1597 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1373.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1598 : Certifies 1598 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1374.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1599 : Certifies 1599 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1375.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1600 : Certifies 1600 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1376.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1601 : Certifies 1601 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1377.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1602 : Certifies 1602 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1379.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1603 : Certifies 1603 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1383.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1604 : Certifies 1604 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1384.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1605 : Certifies 1605 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1385.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1606 : Certifies 1606 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1386.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1607 : Certifies 1607 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1387.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1608 : Certifies 1608 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1388.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1609 : Certifies 1609 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1389.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1610 : Certifies 1610 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1390.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1611 : Certifies 1611 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1391.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1612 : Certifies 1612 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1392.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1613 : Certifies 1613 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1393.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1614 : Certifies 1614 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1394.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1615 : Certifies 1615 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1395.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1616 : Certifies 1616 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1396.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1617 : Certifies 1617 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1397.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1618 : Certifies 1618 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1398.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1619 : Certifies 1619 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1399.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B053 (j : Fin 30) :
    Certifies (1590 + j.val) := by
  fin_cases j
  · exact projection_1590
  · exact projection_1591
  · exact projection_1592
  · exact projection_1593
  · exact projection_1594
  · exact projection_1595
  · exact projection_1596
  · exact projection_1597
  · exact projection_1598
  · exact projection_1599
  · exact projection_1600
  · exact projection_1601
  · exact projection_1602
  · exact projection_1603
  · exact projection_1604
  · exact projection_1605
  · exact projection_1606
  · exact projection_1607
  · exact projection_1608
  · exact projection_1609
  · exact projection_1610
  · exact projection_1611
  · exact projection_1612
  · exact projection_1613
  · exact projection_1614
  · exact projection_1615
  · exact projection_1616
  · exact projection_1617
  · exact projection_1618
  · exact projection_1619

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
