module
public import TerminalGeometry
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Papers.FiniteProjectionChecks

section
set_option debug.skipKernelTC false

section BundlePart0
/- Source: ProjectionCertificates/R_one_six_1161.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1161

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_391 : Finset (Fin 10) := literalFinset [0, 1, 2, 7, 8] (by decide +kernel)
noncomputable def vertices_779 : Finset (Fin 10) := literalFinset [0, 1, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_149 : Finset (Fin 10) := literalFinset [0, 2, 4, 7] (by decide +kernel)
noncomputable def vertices_553 : Finset (Fin 10) := literalFinset [0, 3, 5, 9] (by decide +kernel)
noncomputable def vertices_625 : Finset (Fin 10) := literalFinset [0, 4, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_913 : Finset (Fin 10) := literalFinset [0, 4, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_206 : Finset (Fin 10) := literalFinset [1, 2, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_458 : Finset (Fin 10) := literalFinset [1, 3, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_124 : Finset (Fin 10) := literalFinset [2, 3, 4, 5, 6] (by decide +kernel)
noncomputable def vertices_724 : Finset (Fin 10) := literalFinset [2, 4, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_360 : Finset (Fin 10) := literalFinset [3, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_808 : Finset (Fin 10) := literalFinset [3, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_992 : Finset (Fin 10) := literalFinset [5, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_259 : Finset (Fin 10) := literalFinset [0, 1, 8] (by decide +kernel)
noncomputable def vertices_21 : Finset (Fin 10) := literalFinset [0, 2, 4] (by decide +kernel)
noncomputable def vertices_133 : Finset (Fin 10) := literalFinset [0, 2, 7] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_521 : Finset (Fin 10) := literalFinset [0, 3, 9] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_145 : Finset (Fin 10) := literalFinset [0, 4, 7] (by decide +kernel)
noncomputable def vertices_529 : Finset (Fin 10) := literalFinset [0, 4, 9] (by decide +kernel)
noncomputable def vertices_545 : Finset (Fin 10) := literalFinset [0, 5, 9] (by decide +kernel)
noncomputable def vertices_385 : Finset (Fin 10) := literalFinset [0, 7, 8] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_134 : Finset (Fin 10) := literalFinset [1, 2, 7] (by decide +kernel)
noncomputable def vertices_202 : Finset (Fin 10) := literalFinset [1, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_60 : Finset (Fin 10) := literalFinset [2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_76 : Finset (Fin 10) := literalFinset [2, 3, 6] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_148 : Finset (Fin 10) := literalFinset [2, 4, 7] (by decide +kernel)
noncomputable def vertices_196 : Finset (Fin 10) := literalFinset [2, 6, 7] (by decide +kernel)
noncomputable def vertices_104 : Finset (Fin 10) := literalFinset [3, 5, 6] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_552 : Finset (Fin 10) := literalFinset [3, 5, 9] (by decide +kernel)
noncomputable def vertices_328 : Finset (Fin 10) := literalFinset [3, 6, 8] (by decide +kernel)
noncomputable def vertices_776 : Finset (Fin 10) := literalFinset [3, 8, 9] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_608 : Finset (Fin 10) := literalFinset [5, 6, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_779, vertices_149, vertices_553, vertices_625, vertices_913, vertices_206, vertices_458, vertices_124, vertices_724, vertices_360, vertices_808, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_133, vertices_41, vertices_521, vertices_49, vertices_145, vertices_529, vertices_545, vertices_385, vertices_769, vertices_14, vertices_134, vertices_202, vertices_266, vertices_386, vertices_60, vertices_76, vertices_84, vertices_148, vertices_196, vertices_104, vertices_296, vertices_552, vertices_328, vertices_776, vertices_112, vertices_592, vertices_656, vertices_352, vertices_608, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_779), (false, vertices_149), (false, vertices_553), (false, vertices_625), (false, vertices_913), (true, vertices_202), (true, vertices_76), (true, vertices_84), (true, vertices_196), (true, vertices_104), (true, vertices_296), (true, vertices_328), (true, vertices_352), (true, vertices_800), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![18, 12, 21, 14, 22, 23, 24, 25, 26]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 13 else
  if p.val = (false, vertices_779) then 19 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_553) then 1 else
  if p.val = (false, vertices_625) then 16 else
  if p.val = (false, vertices_913) then 17 else
  if p.val = (true, vertices_202) then 20 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_328) then 7 else
  if p.val = (true, vertices_352) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_704) then 11 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 21 => Sum.inl 2
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
  frameSize := 3
  frame := ![0, 2, 5]
  vertex := 6
  face := Sum.inr ⟨vertices_202, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_202, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 3
  frame := ![1, 2, 3]
  vertex := 4
  face := Sum.inr ⟨vertices_60, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
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
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 2, 1, 4]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_206, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_206, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_458, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 2, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_202, (by decide +kernel)⟩ ⟨vertices_458, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_124, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![1, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_124, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_724, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_724, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_360, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![2, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_104, (by decide +kernel)⟩ ⟨vertices_360, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_808, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![2, 4, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_296, (by decide +kernel)⟩ ⟨vertices_808, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1161

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_one_six_1162.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1162

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_391 : Finset (Fin 10) := literalFinset [0, 1, 2, 7, 8] (by decide +kernel)
noncomputable def vertices_203 : Finset (Fin 10) := literalFinset [0, 1, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_789 : Finset (Fin 10) := literalFinset [0, 2, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_121 : Finset (Fin 10) := literalFinset [0, 3, 4, 5, 6] (by decide +kernel)
noncomputable def vertices_721 : Finset (Fin 10) := literalFinset [0, 4, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_897 : Finset (Fin 10) := literalFinset [0, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_782 : Finset (Fin 10) := literalFinset [1, 2, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_458 : Finset (Fin 10) := literalFinset [1, 3, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_556 : Finset (Fin 10) := literalFinset [2, 3, 5, 9] (by decide +kernel)
noncomputable def vertices_628 : Finset (Fin 10) := literalFinset [2, 4, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_360 : Finset (Fin 10) := literalFinset [3, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_808 : Finset (Fin 10) := literalFinset [3, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_992 : Finset (Fin 10) := literalFinset [5, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_131 : Finset (Fin 10) := literalFinset [0, 1, 7] (by decide +kernel)
noncomputable def vertices_21 : Finset (Fin 10) := literalFinset [0, 2, 4] (by decide +kernel)
noncomputable def vertices_261 : Finset (Fin 10) := literalFinset [0, 2, 8] (by decide +kernel)
noncomputable def vertices_57 : Finset (Fin 10) := literalFinset [0, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_73 : Finset (Fin 10) := literalFinset [0, 3, 6] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_529 : Finset (Fin 10) := literalFinset [0, 4, 9] (by decide +kernel)
noncomputable def vertices_193 : Finset (Fin 10) := literalFinset [0, 6, 7] (by decide +kernel)
noncomputable def vertices_385 : Finset (Fin 10) := literalFinset [0, 7, 8] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_262 : Finset (Fin 10) := literalFinset [1, 2, 8] (by decide +kernel)
noncomputable def vertices_202 : Finset (Fin 10) := literalFinset [1, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_532 : Finset (Fin 10) := literalFinset [2, 4, 9] (by decide +kernel)
noncomputable def vertices_548 : Finset (Fin 10) := literalFinset [2, 5, 9] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_104 : Finset (Fin 10) := literalFinset [3, 5, 6] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_552 : Finset (Fin 10) := literalFinset [3, 5, 9] (by decide +kernel)
noncomputable def vertices_328 : Finset (Fin 10) := literalFinset [3, 6, 8] (by decide +kernel)
noncomputable def vertices_776 : Finset (Fin 10) := literalFinset [3, 8, 9] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_608 : Finset (Fin 10) := literalFinset [5, 6, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_789, vertices_121, vertices_721, vertices_897, vertices_782, vertices_458, vertices_556, vertices_628, vertices_360, vertices_808, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_529, vertices_193, vertices_385, vertices_641, vertices_769, vertices_14, vertices_262, vertices_202, vertices_266, vertices_386, vertices_44, vertices_524, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_296, vertices_552, vertices_328, vertices_776, vertices_112, vertices_592, vertices_352, vertices_608, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_789), (false, vertices_121), (false, vertices_721), (false, vertices_897), (true, vertices_266), (true, vertices_524), (true, vertices_548), (true, vertices_296), (true, vertices_552), (true, vertices_328), (true, vertices_776), (true, vertices_352), (true, vertices_608), (true, vertices_800), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![12, 15, 17, 20, 22, 23, 24, 25, 26]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_391) then 13 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_789) then 16 else
  if p.val = (false, vertices_121) then 19 else
  if p.val = (false, vertices_721) then 21 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_352) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_448) then 11 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
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
  frame := ![1, 3, 4, 5]
  vertex := 8
  face := Sum.inl ⟨vertices_628, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_628, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 2, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_782, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_782, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 3
  frame := ![0, 2, 5]
  vertex := 6
  face := Sum.inr ⟨vertices_202, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_202, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
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
noncomputable def pivot : Fin 4 → Fin 9 := ![3, 1, 0, 4]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_782, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_782, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_458, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 2, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_202, (by decide +kernel)⟩ ⟨vertices_458, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_556, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![1, 2, 4, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_556, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_628, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_628, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_360, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![2, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_104, (by decide +kernel)⟩ ⟨vertices_360, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_808, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![2, 4, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_296, (by decide +kernel)⟩ ⟨vertices_808, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1162

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_one_six_1163.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1163

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_391 : Finset (Fin 10) := literalFinset [0, 1, 2, 7, 8] (by decide +kernel)
noncomputable def vertices_779 : Finset (Fin 10) := literalFinset [0, 1, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_277 : Finset (Fin 10) := literalFinset [0, 2, 4, 8] (by decide +kernel)
noncomputable def vertices_617 : Finset (Fin 10) := literalFinset [0, 3, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_817 : Finset (Fin 10) := literalFinset [0, 4, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_206 : Finset (Fin 10) := literalFinset [1, 2, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_458 : Finset (Fin 10) := literalFinset [1, 3, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_124 : Finset (Fin 10) := literalFinset [2, 3, 4, 5, 6] (by decide +kernel)
noncomputable def vertices_212 : Finset (Fin 10) := literalFinset [2, 4, 6, 7] (by decide +kernel)
noncomputable def vertices_916 : Finset (Fin 10) := literalFinset [2, 4, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_840 : Finset (Fin 10) := literalFinset [3, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_752 : Finset (Fin 10) := literalFinset [4, 5, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_960 : Finset (Fin 10) := literalFinset [6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_259 : Finset (Fin 10) := literalFinset [0, 1, 8] (by decide +kernel)
noncomputable def vertices_21 : Finset (Fin 10) := literalFinset [0, 2, 4] (by decide +kernel)
noncomputable def vertices_261 : Finset (Fin 10) := literalFinset [0, 2, 8] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_521 : Finset (Fin 10) := literalFinset [0, 3, 9] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_273 : Finset (Fin 10) := literalFinset [0, 4, 8] (by decide +kernel)
noncomputable def vertices_545 : Finset (Fin 10) := literalFinset [0, 5, 9] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_134 : Finset (Fin 10) := literalFinset [1, 2, 7] (by decide +kernel)
noncomputable def vertices_202 : Finset (Fin 10) := literalFinset [1, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_60 : Finset (Fin 10) := literalFinset [2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_76 : Finset (Fin 10) := literalFinset [2, 3, 6] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_148 : Finset (Fin 10) := literalFinset [2, 4, 7] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_196 : Finset (Fin 10) := literalFinset [2, 6, 7] (by decide +kernel)
noncomputable def vertices_388 : Finset (Fin 10) := literalFinset [2, 7, 8] (by decide +kernel)
noncomputable def vertices_104 : Finset (Fin 10) := literalFinset [3, 5, 6] (by decide +kernel)
noncomputable def vertices_328 : Finset (Fin 10) := literalFinset [3, 6, 8] (by decide +kernel)
noncomputable def vertices_584 : Finset (Fin 10) := literalFinset [3, 6, 9] (by decide +kernel)
noncomputable def vertices_776 : Finset (Fin 10) := literalFinset [3, 8, 9] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_208 : Finset (Fin 10) := literalFinset [4, 6, 7] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_784 : Finset (Fin 10) := literalFinset [4, 8, 9] (by decide +kernel)
noncomputable def vertices_608 : Finset (Fin 10) := literalFinset [5, 6, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_779, vertices_277, vertices_617, vertices_817, vertices_206, vertices_458, vertices_124, vertices_212, vertices_916, vertices_840, vertices_752, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_261, vertices_41, vertices_521, vertices_49, vertices_273, vertices_545, vertices_769, vertices_14, vertices_134, vertices_202, vertices_266, vertices_386, vertices_60, vertices_76, vertices_84, vertices_148, vertices_276, vertices_196, vertices_388, vertices_104, vertices_328, vertices_584, vertices_776, vertices_112, vertices_560, vertices_208, vertices_656, vertices_784, vertices_608, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_779), (false, vertices_277), (false, vertices_617), (false, vertices_817), (true, vertices_202), (true, vertices_76), (true, vertices_84), (true, vertices_148), (true, vertices_196), (true, vertices_328), (true, vertices_112), (true, vertices_208), (true, vertices_656), (true, vertices_448), (true, vertices_704), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![18, 13, 21, 15, 23, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_779) then 19 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_617) then 22 else
  if p.val = (false, vertices_817) then 17 else
  if p.val = (true, vertices_202) then 20 else
  if p.val = (true, vertices_76) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_656) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
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
  frameSize := 3
  frame := ![0, 2, 5]
  vertex := 6
  face := Sum.inr ⟨vertices_202, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_202, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 3
  frame := ![1, 2, 3]
  vertex := 4
  face := Sum.inr ⟨vertices_60, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
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
  frame := ![3, 4, 5, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_752, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_752, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 2, 1, 3]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_206, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_206, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_458, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 2, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_202, (by decide +kernel)⟩ ⟨vertices_458, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_124, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![1, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_124, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_212, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![1, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_212, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_916, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![1, 3, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_148, (by decide +kernel)⟩ ⟨vertices_916, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_840, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![2, 5, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_328, (by decide +kernel)⟩ ⟨vertices_840, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_752, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![3, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_752, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1163

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_one_six_1164.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1164

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_647 : Finset (Fin 10) := literalFinset [0, 1, 2, 7, 9] (by decide +kernel)
noncomputable def vertices_779 : Finset (Fin 10) := literalFinset [0, 1, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_149 : Finset (Fin 10) := literalFinset [0, 2, 4, 7] (by decide +kernel)
noncomputable def vertices_617 : Finset (Fin 10) := literalFinset [0, 3, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_689 : Finset (Fin 10) := literalFinset [0, 4, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_206 : Finset (Fin 10) := literalFinset [1, 2, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_458 : Finset (Fin 10) := literalFinset [1, 3, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_898 : Finset (Fin 10) := literalFinset [1, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_124 : Finset (Fin 10) := literalFinset [2, 3, 4, 5, 6] (by decide +kernel)
noncomputable def vertices_468 : Finset (Fin 10) := literalFinset [2, 4, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_840 : Finset (Fin 10) := literalFinset [3, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_880 : Finset (Fin 10) := literalFinset [4, 5, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_912 : Finset (Fin 10) := literalFinset [4, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_515 : Finset (Fin 10) := literalFinset [0, 1, 9] (by decide +kernel)
noncomputable def vertices_21 : Finset (Fin 10) := literalFinset [0, 2, 4] (by decide +kernel)
noncomputable def vertices_133 : Finset (Fin 10) := literalFinset [0, 2, 7] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_521 : Finset (Fin 10) := literalFinset [0, 3, 9] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_145 : Finset (Fin 10) := literalFinset [0, 4, 7] (by decide +kernel)
noncomputable def vertices_545 : Finset (Fin 10) := literalFinset [0, 5, 9] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_134 : Finset (Fin 10) := literalFinset [1, 2, 7] (by decide +kernel)
noncomputable def vertices_202 : Finset (Fin 10) := literalFinset [1, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_60 : Finset (Fin 10) := literalFinset [2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_76 : Finset (Fin 10) := literalFinset [2, 3, 6] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_148 : Finset (Fin 10) := literalFinset [2, 4, 7] (by decide +kernel)
noncomputable def vertices_196 : Finset (Fin 10) := literalFinset [2, 6, 7] (by decide +kernel)
noncomputable def vertices_104 : Finset (Fin 10) := literalFinset [3, 5, 6] (by decide +kernel)
noncomputable def vertices_328 : Finset (Fin 10) := literalFinset [3, 6, 8] (by decide +kernel)
noncomputable def vertices_584 : Finset (Fin 10) := literalFinset [3, 6, 9] (by decide +kernel)
noncomputable def vertices_776 : Finset (Fin 10) := literalFinset [3, 8, 9] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_784 : Finset (Fin 10) := literalFinset [4, 8, 9] (by decide +kernel)
noncomputable def vertices_608 : Finset (Fin 10) := literalFinset [5, 6, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_779, vertices_149, vertices_617, vertices_689, vertices_206, vertices_458, vertices_898, vertices_124, vertices_468, vertices_840, vertices_880, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_133, vertices_41, vertices_521, vertices_49, vertices_145, vertices_545, vertices_641, vertices_14, vertices_134, vertices_202, vertices_266, vertices_386, vertices_642, vertices_770, vertices_60, vertices_76, vertices_84, vertices_148, vertices_196, vertices_104, vertices_328, vertices_584, vertices_776, vertices_112, vertices_560, vertices_336, vertices_400, vertices_656, vertices_784, vertices_608, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_779), (false, vertices_149), (false, vertices_617), (false, vertices_689), (true, vertices_202), (true, vertices_386), (true, vertices_76), (true, vertices_84), (true, vertices_196), (true, vertices_328), (true, vertices_112), (true, vertices_336), (true, vertices_400), (true, vertices_784), (true, vertices_448), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![18, 13, 21, 15, 23, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_647) then 14 else
  if p.val = (false, vertices_779) then 19 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_617) then 22 else
  if p.val = (false, vertices_689) then 17 else
  if p.val = (true, vertices_202) then 20 else
  if p.val = (true, vertices_386) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_832) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
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
  frameSize := 3
  frame := ![0, 2, 5]
  vertex := 6
  face := Sum.inr ⟨vertices_202, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_202, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 3
  frame := ![1, 2, 3]
  vertex := 4
  face := Sum.inr ⟨vertices_60, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 3, 5, 6]
  vertex := 7
  face := Sum.inl ⟨vertices_468, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_468, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![3, 4, 5, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_880, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_880, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 2, 1, 3]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_206, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_206, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_458, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 2, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_202, (by decide +kernel)⟩ ⟨vertices_458, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_898, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 6, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_386, (by decide +kernel)⟩ ⟨vertices_898, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_124, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_124, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_468, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![1, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_468, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_840, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![2, 5, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_328, (by decide +kernel)⟩ ⟨vertices_840, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_880, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![3, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_880, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_912, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![3, 6, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_400, (by decide +kernel)⟩ ⟨vertices_912, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1164

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_one_six_1165.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1165

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_199 : Finset (Fin 10) := literalFinset [0, 1, 2, 6, 7] (by decide +kernel)
noncomputable def vertices_779 : Finset (Fin 10) := literalFinset [0, 1, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_451 : Finset (Fin 10) := literalFinset [0, 1, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_117 : Finset (Fin 10) := literalFinset [0, 2, 4, 5, 6] (by decide +kernel)
noncomputable def vertices_553 : Finset (Fin 10) := literalFinset [0, 3, 5, 9] (by decide +kernel)
noncomputable def vertices_865 : Finset (Fin 10) := literalFinset [0, 5, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_526 : Finset (Fin 10) := literalFinset [1, 2, 3, 9] (by decide +kernel)
noncomputable def vertices_902 : Finset (Fin 10) := literalFinset [1, 2, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_220 : Finset (Fin 10) := literalFinset [2, 3, 4, 6, 7] (by decide +kernel)
noncomputable def vertices_652 : Finset (Fin 10) := literalFinset [2, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_696 : Finset (Fin 10) := literalFinset [3, 4, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_624 : Finset (Fin 10) := literalFinset [4, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_976 : Finset (Fin 10) := literalFinset [4, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_195 : Finset (Fin 10) := literalFinset [0, 1, 6, 7] (by decide +kernel)
noncomputable def vertices_259 : Finset (Fin 10) := literalFinset [0, 1, 8] (by decide +kernel)
noncomputable def vertices_53 : Finset (Fin 10) := literalFinset [0, 2, 4, 5] (by decide +kernel)
noncomputable def vertices_69 : Finset (Fin 10) := literalFinset [0, 2, 6] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_521 : Finset (Fin 10) := literalFinset [0, 3, 9] (by decide +kernel)
noncomputable def vertices_97 : Finset (Fin 10) := literalFinset [0, 5, 6] (by decide +kernel)
noncomputable def vertices_545 : Finset (Fin 10) := literalFinset [0, 5, 9] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_134 : Finset (Fin 10) := literalFinset [1, 2, 7] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_522 : Finset (Fin 10) := literalFinset [1, 3, 9] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_28 : Finset (Fin 10) := literalFinset [2, 3, 4] (by decide +kernel)
noncomputable def vertices_140 : Finset (Fin 10) := literalFinset [2, 3, 7] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_196 : Finset (Fin 10) := literalFinset [2, 6, 7] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_56 : Finset (Fin 10) := literalFinset [3, 4, 5] (by decide +kernel)
noncomputable def vertices_152 : Finset (Fin 10) := literalFinset [3, 4, 7] (by decide +kernel)
noncomputable def vertices_552 : Finset (Fin 10) := literalFinset [3, 5, 9] (by decide +kernel)
noncomputable def vertices_648 : Finset (Fin 10) := literalFinset [3, 7, 9] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_208 : Finset (Fin 10) := literalFinset [4, 6, 7] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_608 : Finset (Fin 10) := literalFinset [5, 6, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_451, vertices_117, vertices_553, vertices_865, vertices_526, vertices_902, vertices_220, vertices_652, vertices_696, vertices_624, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_195, vertices_259, vertices_53, vertices_69, vertices_41, vertices_521, vertices_97, vertices_545, vertices_321, vertices_769, vertices_14, vertices_134, vertices_518, vertices_522, vertices_386, vertices_770, vertices_28, vertices_140, vertices_524, vertices_84, vertices_196, vertices_644, vertices_56, vertices_152, vertices_552, vertices_648, vertices_112, vertices_560, vertices_208, vertices_592, vertices_656, vertices_608, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_451), (false, vertices_117), (false, vertices_553), (false, vertices_865), (true, vertices_518), (true, vertices_140), (true, vertices_524), (true, vertices_644), (true, vertices_152), (true, vertices_648), (true, vertices_560), (true, vertices_208), (true, vertices_592), (true, vertices_656), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![17, 12, 14, 20, 21, 23, 24, 25, 26]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 18 else
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_451) then 19 else
  if p.val = (false, vertices_117) then 13 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_865) then 22 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 20 => Sum.inl 3
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
  frame := ![0, 1, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_902, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_134, (by decide +kernel)⟩ ⟨vertices_902, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 3, 5]
  vertex := 6
  face := Sum.inl ⟨vertices_220, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_28, (by decide +kernel)⟩ ⟨vertices_220, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![2, 3, 4, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_696, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_696, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![3, 5, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_976, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_208, (by decide +kernel)⟩ ⟨vertices_976, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 1, 2, 3]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_526, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .fundamental ![0, 1, 2, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_526, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_902, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_134, (by decide +kernel)⟩ ⟨vertices_902, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_220, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![1, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_28, (by decide +kernel)⟩ ⟨vertices_220, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_652, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![1, 2, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_140, (by decide +kernel)⟩ ⟨vertices_652, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_696, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![2, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_696, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_624, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![3, 4, 5, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_624, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_976, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![3, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_208, (by decide +kernel)⟩ ⟨vertices_976, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1165

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_one_six_1166.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1166

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_199 : Finset (Fin 10) := literalFinset [0, 1, 2, 6, 7] (by decide +kernel)
noncomputable def vertices_779 : Finset (Fin 10) := literalFinset [0, 1, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_451 : Finset (Fin 10) := literalFinset [0, 1, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_117 : Finset (Fin 10) := literalFinset [0, 2, 4, 5, 6] (by decide +kernel)
noncomputable def vertices_553 : Finset (Fin 10) := literalFinset [0, 3, 5, 9] (by decide +kernel)
noncomputable def vertices_865 : Finset (Fin 10) := literalFinset [0, 5, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_526 : Finset (Fin 10) := literalFinset [1, 2, 3, 9] (by decide +kernel)
noncomputable def vertices_902 : Finset (Fin 10) := literalFinset [1, 2, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_220 : Finset (Fin 10) := literalFinset [2, 3, 4, 6, 7] (by decide +kernel)
noncomputable def vertices_652 : Finset (Fin 10) := literalFinset [2, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_696 : Finset (Fin 10) := literalFinset [3, 4, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_496 : Finset (Fin 10) := literalFinset [4, 5, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_928 : Finset (Fin 10) := literalFinset [5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_195 : Finset (Fin 10) := literalFinset [0, 1, 6, 7] (by decide +kernel)
noncomputable def vertices_259 : Finset (Fin 10) := literalFinset [0, 1, 8] (by decide +kernel)
noncomputable def vertices_53 : Finset (Fin 10) := literalFinset [0, 2, 4, 5] (by decide +kernel)
noncomputable def vertices_69 : Finset (Fin 10) := literalFinset [0, 2, 6] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_521 : Finset (Fin 10) := literalFinset [0, 3, 9] (by decide +kernel)
noncomputable def vertices_97 : Finset (Fin 10) := literalFinset [0, 5, 6] (by decide +kernel)
noncomputable def vertices_545 : Finset (Fin 10) := literalFinset [0, 5, 9] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_134 : Finset (Fin 10) := literalFinset [1, 2, 7] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_522 : Finset (Fin 10) := literalFinset [1, 3, 9] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_28 : Finset (Fin 10) := literalFinset [2, 3, 4] (by decide +kernel)
noncomputable def vertices_140 : Finset (Fin 10) := literalFinset [2, 3, 7] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_196 : Finset (Fin 10) := literalFinset [2, 6, 7] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_56 : Finset (Fin 10) := literalFinset [3, 4, 5] (by decide +kernel)
noncomputable def vertices_152 : Finset (Fin 10) := literalFinset [3, 4, 7] (by decide +kernel)
noncomputable def vertices_552 : Finset (Fin 10) := literalFinset [3, 5, 9] (by decide +kernel)
noncomputable def vertices_648 : Finset (Fin 10) := literalFinset [3, 7, 9] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_208 : Finset (Fin 10) := literalFinset [4, 6, 7] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_451, vertices_117, vertices_553, vertices_865, vertices_526, vertices_902, vertices_220, vertices_652, vertices_696, vertices_496, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_195, vertices_259, vertices_53, vertices_69, vertices_41, vertices_521, vertices_97, vertices_545, vertices_321, vertices_769, vertices_14, vertices_134, vertices_518, vertices_522, vertices_386, vertices_770, vertices_28, vertices_140, vertices_524, vertices_84, vertices_196, vertices_644, vertices_56, vertices_152, vertices_552, vertices_648, vertices_112, vertices_176, vertices_208, vertices_352, vertices_416, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_451), (false, vertices_117), (false, vertices_553), (false, vertices_865), (true, vertices_518), (true, vertices_140), (true, vertices_524), (true, vertices_644), (true, vertices_152), (true, vertices_648), (true, vertices_176), (true, vertices_208), (true, vertices_416), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![17, 12, 14, 20, 21, 23, 24, 25, 26]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 18 else
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_451) then 19 else
  if p.val = (false, vertices_117) then 13 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_865) then 22 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 20 => Sum.inl 3
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
  frame := ![0, 1, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_902, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_134, (by decide +kernel)⟩ ⟨vertices_902, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 3, 5]
  vertex := 6
  face := Sum.inl ⟨vertices_220, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_28, (by decide +kernel)⟩ ⟨vertices_220, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![2, 3, 4, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_696, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_696, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![3, 4, 5, 6]
  vertex := 7
  face := Sum.inl ⟨vertices_496, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_496, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 1, 2, 3]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_526, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .fundamental ![0, 1, 2, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_526, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_902, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_134, (by decide +kernel)⟩ ⟨vertices_902, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_220, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![1, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_28, (by decide +kernel)⟩ ⟨vertices_220, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_652, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![1, 2, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_140, (by decide +kernel)⟩ ⟨vertices_652, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_696, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![2, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_696, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_496, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![3, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_496, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1166

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_one_six_1167.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1167

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_647 : Finset (Fin 10) := literalFinset [0, 1, 2, 7, 9] (by decide +kernel)
noncomputable def vertices_779 : Finset (Fin 10) := literalFinset [0, 1, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_149 : Finset (Fin 10) := literalFinset [0, 2, 4, 7] (by decide +kernel)
noncomputable def vertices_361 : Finset (Fin 10) := literalFinset [0, 3, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_689 : Finset (Fin 10) := literalFinset [0, 4, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_801 : Finset (Fin 10) := literalFinset [0, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_206 : Finset (Fin 10) := literalFinset [1, 2, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_458 : Finset (Fin 10) := literalFinset [1, 3, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_898 : Finset (Fin 10) := literalFinset [1, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_124 : Finset (Fin 10) := literalFinset [2, 3, 4, 5, 6] (by decide +kernel)
noncomputable def vertices_468 : Finset (Fin 10) := literalFinset [2, 4, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_880 : Finset (Fin 10) := literalFinset [4, 5, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_912 : Finset (Fin 10) := literalFinset [4, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_515 : Finset (Fin 10) := literalFinset [0, 1, 9] (by decide +kernel)
noncomputable def vertices_21 : Finset (Fin 10) := literalFinset [0, 2, 4] (by decide +kernel)
noncomputable def vertices_133 : Finset (Fin 10) := literalFinset [0, 2, 7] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_265 : Finset (Fin 10) := literalFinset [0, 3, 8] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_145 : Finset (Fin 10) := literalFinset [0, 4, 7] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_545 : Finset (Fin 10) := literalFinset [0, 5, 9] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_134 : Finset (Fin 10) := literalFinset [1, 2, 7] (by decide +kernel)
noncomputable def vertices_202 : Finset (Fin 10) := literalFinset [1, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_60 : Finset (Fin 10) := literalFinset [2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_76 : Finset (Fin 10) := literalFinset [2, 3, 6] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_148 : Finset (Fin 10) := literalFinset [2, 4, 7] (by decide +kernel)
noncomputable def vertices_196 : Finset (Fin 10) := literalFinset [2, 6, 7] (by decide +kernel)
noncomputable def vertices_104 : Finset (Fin 10) := literalFinset [3, 5, 6] (by decide +kernel)
noncomputable def vertices_328 : Finset (Fin 10) := literalFinset [3, 6, 8] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_784 : Finset (Fin 10) := literalFinset [4, 8, 9] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_779, vertices_149, vertices_361, vertices_689, vertices_801, vertices_206, vertices_458, vertices_898, vertices_124, vertices_468, vertices_880, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_133, vertices_41, vertices_265, vertices_49, vertices_145, vertices_289, vertices_545, vertices_641, vertices_769, vertices_14, vertices_134, vertices_202, vertices_266, vertices_386, vertices_642, vertices_770, vertices_60, vertices_76, vertices_84, vertices_148, vertices_196, vertices_104, vertices_328, vertices_112, vertices_560, vertices_336, vertices_400, vertices_656, vertices_784, vertices_352, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_779), (false, vertices_149), (false, vertices_361), (false, vertices_689), (false, vertices_801), (true, vertices_202), (true, vertices_386), (true, vertices_76), (true, vertices_84), (true, vertices_196), (true, vertices_112), (true, vertices_336), (true, vertices_400), (true, vertices_784), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![17, 12, 20, 14, 22, 23, 24, 25, 26]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_647) then 13 else
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_689) then 16 else
  if p.val = (false, vertices_801) then 1 else
  if p.val = (true, vertices_202) then 19 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_801), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
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
  frameSize := 3
  frame := ![0, 2, 5]
  vertex := 6
  face := Sum.inr ⟨vertices_202, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_202, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 3
  frame := ![1, 2, 3]
  vertex := 4
  face := Sum.inr ⟨vertices_60, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 3, 5, 6]
  vertex := 7
  face := Sum.inl ⟨vertices_468, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_468, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![3, 4, 5, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_880, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_880, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 2, 1, 3]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_206, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_206, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_458, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 2, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_202, (by decide +kernel)⟩ ⟨vertices_458, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_898, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 6, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_386, (by decide +kernel)⟩ ⟨vertices_898, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_124, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_124, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_468, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![1, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_468, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_880, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![3, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_880, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1167

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_one_six_1168.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1168

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_647 : Finset (Fin 10) := literalFinset [0, 1, 2, 7, 9] (by decide +kernel)
noncomputable def vertices_779 : Finset (Fin 10) := literalFinset [0, 1, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_789 : Finset (Fin 10) := literalFinset [0, 2, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_361 : Finset (Fin 10) := literalFinset [0, 3, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_305 : Finset (Fin 10) := literalFinset [0, 4, 5, 8] (by decide +kernel)
noncomputable def vertices_206 : Finset (Fin 10) := literalFinset [1, 2, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_458 : Finset (Fin 10) := literalFinset [1, 3, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_898 : Finset (Fin 10) := literalFinset [1, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_124 : Finset (Fin 10) := literalFinset [2, 3, 4, 5, 6] (by decide +kernel)
noncomputable def vertices_724 : Finset (Fin 10) := literalFinset [2, 4, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_624 : Finset (Fin 10) := literalFinset [4, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_816 : Finset (Fin 10) := literalFinset [4, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_992 : Finset (Fin 10) := literalFinset [5, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_515 : Finset (Fin 10) := literalFinset [0, 1, 9] (by decide +kernel)
noncomputable def vertices_21 : Finset (Fin 10) := literalFinset [0, 2, 4] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_265 : Finset (Fin 10) := literalFinset [0, 3, 8] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_273 : Finset (Fin 10) := literalFinset [0, 4, 8] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_134 : Finset (Fin 10) := literalFinset [1, 2, 7] (by decide +kernel)
noncomputable def vertices_202 : Finset (Fin 10) := literalFinset [1, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_60 : Finset (Fin 10) := literalFinset [2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_76 : Finset (Fin 10) := literalFinset [2, 3, 6] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_532 : Finset (Fin 10) := literalFinset [2, 4, 9] (by decide +kernel)
noncomputable def vertices_196 : Finset (Fin 10) := literalFinset [2, 6, 7] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_104 : Finset (Fin 10) := literalFinset [3, 5, 6] (by decide +kernel)
noncomputable def vertices_328 : Finset (Fin 10) := literalFinset [3, 6, 8] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_784 : Finset (Fin 10) := literalFinset [4, 8, 9] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_608 : Finset (Fin 10) := literalFinset [5, 6, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_779, vertices_789, vertices_361, vertices_305, vertices_206, vertices_458, vertices_898, vertices_124, vertices_724, vertices_624, vertices_816, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_517, vertices_41, vertices_265, vertices_49, vertices_273, vertices_289, vertices_769, vertices_14, vertices_134, vertices_202, vertices_266, vertices_386, vertices_642, vertices_770, vertices_60, vertices_76, vertices_84, vertices_532, vertices_196, vertices_644, vertices_104, vertices_328, vertices_112, vertices_304, vertices_560, vertices_592, vertices_784, vertices_352, vertices_608, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_779), (false, vertices_789), (false, vertices_361), (false, vertices_305), (true, vertices_202), (true, vertices_386), (true, vertices_76), (true, vertices_84), (true, vertices_196), (true, vertices_112), (true, vertices_560), (true, vertices_592), (true, vertices_608), (true, vertices_800), (true, vertices_448), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![18, 13, 21, 16, 23, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_647) then 14 else
  if p.val = (false, vertices_779) then 19 else
  if p.val = (false, vertices_789) then 15 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_305) then 0 else
  if p.val = (true, vertices_202) then 20 else
  if p.val = (true, vertices_386) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_112) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_305), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
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
  frameSize := 3
  frame := ![0, 2, 5]
  vertex := 6
  face := Sum.inr ⟨vertices_202, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_202, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 3
  frame := ![1, 2, 3]
  vertex := 4
  face := Sum.inr ⟨vertices_60, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
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
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 2, 1, 4]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_206, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_206, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_458, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 2, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_202, (by decide +kernel)⟩ ⟨vertices_458, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_898, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 6, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_386, (by decide +kernel)⟩ ⟨vertices_898, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_124, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_124, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_724, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![1, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_724, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_624, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![3, 4, 5, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_624, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_816, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![3, 4, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_304, (by decide +kernel)⟩ ⟨vertices_816, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_992, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .oneRow ![4, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_352, (by decide +kernel)⟩ ⟨vertices_992, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1168

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_one_six_1169.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1169

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_647 : Finset (Fin 10) := literalFinset [0, 1, 2, 7, 9] (by decide +kernel)
noncomputable def vertices_203 : Finset (Fin 10) := literalFinset [0, 1, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_789 : Finset (Fin 10) := literalFinset [0, 2, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_121 : Finset (Fin 10) := literalFinset [0, 3, 4, 5, 6] (by decide +kernel)
noncomputable def vertices_721 : Finset (Fin 10) := literalFinset [0, 4, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_782 : Finset (Fin 10) := literalFinset [1, 2, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_458 : Finset (Fin 10) := literalFinset [1, 3, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_898 : Finset (Fin 10) := literalFinset [1, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_364 : Finset (Fin 10) := literalFinset [2, 3, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_308 : Finset (Fin 10) := literalFinset [2, 4, 5, 8] (by decide +kernel)
noncomputable def vertices_240 : Finset (Fin 10) := literalFinset [4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_944 : Finset (Fin 10) := literalFinset [4, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_480 : Finset (Fin 10) := literalFinset [5, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_131 : Finset (Fin 10) := literalFinset [0, 1, 7] (by decide +kernel)
noncomputable def vertices_21 : Finset (Fin 10) := literalFinset [0, 2, 4] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_57 : Finset (Fin 10) := literalFinset [0, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_73 : Finset (Fin 10) := literalFinset [0, 3, 6] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_529 : Finset (Fin 10) := literalFinset [0, 4, 9] (by decide +kernel)
noncomputable def vertices_193 : Finset (Fin 10) := literalFinset [0, 6, 7] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_202 : Finset (Fin 10) := literalFinset [1, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_268 : Finset (Fin 10) := literalFinset [2, 3, 8] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_292 : Finset (Fin 10) := literalFinset [2, 5, 8] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_104 : Finset (Fin 10) := literalFinset [3, 5, 6] (by decide +kernel)
noncomputable def vertices_328 : Finset (Fin 10) := literalFinset [3, 6, 8] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_208 : Finset (Fin 10) := literalFinset [4, 6, 7] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_784 : Finset (Fin 10) := literalFinset [4, 8, 9] (by decide +kernel)
noncomputable def vertices_224 : Finset (Fin 10) := literalFinset [5, 6, 7] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_203, vertices_789, vertices_121, vertices_721, vertices_782, vertices_458, vertices_898, vertices_364, vertices_308, vertices_240, vertices_944, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_517, vertices_57, vertices_73, vertices_81, vertices_529, vertices_193, vertices_641, vertices_14, vertices_518, vertices_202, vertices_266, vertices_386, vertices_642, vertices_770, vertices_44, vertices_268, vertices_52, vertices_276, vertices_292, vertices_772, vertices_104, vertices_328, vertices_112, vertices_176, vertices_304, vertices_208, vertices_656, vertices_784, vertices_224, vertices_352, vertices_416, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_203), (false, vertices_789), (false, vertices_121), (false, vertices_721), (true, vertices_266), (true, vertices_386), (true, vertices_770), (true, vertices_268), (true, vertices_292), (true, vertices_328), (true, vertices_176), (true, vertices_304), (true, vertices_224), (true, vertices_352), (true, vertices_416), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 16, 18, 21, 23, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 19 else
  if p.val = (false, vertices_647) then 14 else
  if p.val = (false, vertices_203) then 15 else
  if p.val = (false, vertices_789) then 17 else
  if p.val = (false, vertices_121) then 20 else
  if p.val = (false, vertices_721) then 22 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_386) then 1 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_352) then 9 else
  if p.val = (true, vertices_416) then 10 else
  if p.val = (true, vertices_448) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
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
  frame := ![3, 4, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_944, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_176, (by decide +kernel)⟩ ⟨vertices_944, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 3
  frame := ![0, 2, 5]
  vertex := 6
  face := Sum.inr ⟨vertices_202, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_202, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 2, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_782, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_782, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
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

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![3, 6, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_782, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_782, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_458, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 2, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_202, (by decide +kernel)⟩ ⟨vertices_458, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_898, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 6, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_386, (by decide +kernel)⟩ ⟨vertices_898, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_364, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 2, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_364, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_308, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![1, 3, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_308, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_240, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![3, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_240, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_944, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![3, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_176, (by decide +kernel)⟩ ⟨vertices_944, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1169

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_one_six_1170.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1170

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_519 : Finset (Fin 10) := literalFinset [0, 1, 2, 9] (by decide +kernel)
noncomputable def vertices_779 : Finset (Fin 10) := literalFinset [0, 1, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_661 : Finset (Fin 10) := literalFinset [0, 2, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_361 : Finset (Fin 10) := literalFinset [0, 3, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_817 : Finset (Fin 10) := literalFinset [0, 4, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_206 : Finset (Fin 10) := literalFinset [1, 2, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_902 : Finset (Fin 10) := literalFinset [1, 2, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_458 : Finset (Fin 10) := literalFinset [1, 3, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_124 : Finset (Fin 10) := literalFinset [2, 3, 4, 5, 6] (by decide +kernel)
noncomputable def vertices_212 : Finset (Fin 10) := literalFinset [2, 4, 6, 7] (by decide +kernel)
noncomputable def vertices_752 : Finset (Fin 10) := literalFinset [4, 5, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_480 : Finset (Fin 10) := literalFinset [5, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_928 : Finset (Fin 10) := literalFinset [5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_515 : Finset (Fin 10) := literalFinset [0, 1, 9] (by decide +kernel)
noncomputable def vertices_21 : Finset (Fin 10) := literalFinset [0, 2, 4] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_265 : Finset (Fin 10) := literalFinset [0, 3, 8] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_529 : Finset (Fin 10) := literalFinset [0, 4, 9] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_134 : Finset (Fin 10) := literalFinset [1, 2, 7] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_202 : Finset (Fin 10) := literalFinset [1, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_60 : Finset (Fin 10) := literalFinset [2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_76 : Finset (Fin 10) := literalFinset [2, 3, 6] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_148 : Finset (Fin 10) := literalFinset [2, 4, 7] (by decide +kernel)
noncomputable def vertices_196 : Finset (Fin 10) := literalFinset [2, 6, 7] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_104 : Finset (Fin 10) := literalFinset [3, 5, 6] (by decide +kernel)
noncomputable def vertices_328 : Finset (Fin 10) := literalFinset [3, 6, 8] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_208 : Finset (Fin 10) := literalFinset [4, 6, 7] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_224 : Finset (Fin 10) := literalFinset [5, 6, 7] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_779, vertices_661, vertices_361, vertices_817, vertices_206, vertices_902, vertices_458, vertices_124, vertices_212, vertices_752, vertices_480, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_517, vertices_41, vertices_265, vertices_49, vertices_529, vertices_289, vertices_769, vertices_14, vertices_134, vertices_518, vertices_202, vertices_266, vertices_386, vertices_770, vertices_60, vertices_76, vertices_84, vertices_148, vertices_196, vertices_644, vertices_104, vertices_328, vertices_112, vertices_560, vertices_208, vertices_656, vertices_224, vertices_352, vertices_416, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_779), (false, vertices_661), (false, vertices_361), (false, vertices_817), (true, vertices_134), (true, vertices_202), (true, vertices_386), (true, vertices_76), (true, vertices_84), (true, vertices_196), (true, vertices_112), (true, vertices_208), (true, vertices_224), (true, vertices_416), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![18, 13, 21, 15, 23, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_779) then 19 else
  if p.val = (false, vertices_661) then 14 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_817) then 17 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_202) then 20 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_448) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
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
  frame := ![0, 1, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_902, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_134, (by decide +kernel)⟩ ⟨vertices_902, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 3
  frame := ![0, 2, 5]
  vertex := 6
  face := Sum.inr ⟨vertices_202, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_202, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 3
  frame := ![1, 2, 3]
  vertex := 4
  face := Sum.inr ⟨vertices_60, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![3, 4, 5, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_752, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_752, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![7, 0, 1, 3]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_206, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_206, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_902, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_134, (by decide +kernel)⟩ ⟨vertices_902, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_458, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 2, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_202, (by decide +kernel)⟩ ⟨vertices_458, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_124, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_124, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_212, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![1, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_212, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_752, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![3, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_752, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_480, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![4, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_224, (by decide +kernel)⟩ ⟨vertices_480, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1170

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_one_six_1171.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1171

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_519 : Finset (Fin 10) := literalFinset [0, 1, 2, 9] (by decide +kernel)
noncomputable def vertices_779 : Finset (Fin 10) := literalFinset [0, 1, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_661 : Finset (Fin 10) := literalFinset [0, 2, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_361 : Finset (Fin 10) := literalFinset [0, 3, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_817 : Finset (Fin 10) := literalFinset [0, 4, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_206 : Finset (Fin 10) := literalFinset [1, 2, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_902 : Finset (Fin 10) := literalFinset [1, 2, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_458 : Finset (Fin 10) := literalFinset [1, 3, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_124 : Finset (Fin 10) := literalFinset [2, 3, 4, 5, 6] (by decide +kernel)
noncomputable def vertices_212 : Finset (Fin 10) := literalFinset [2, 4, 6, 7] (by decide +kernel)
noncomputable def vertices_752 : Finset (Fin 10) := literalFinset [4, 5, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_864 : Finset (Fin 10) := literalFinset [5, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_960 : Finset (Fin 10) := literalFinset [6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_515 : Finset (Fin 10) := literalFinset [0, 1, 9] (by decide +kernel)
noncomputable def vertices_21 : Finset (Fin 10) := literalFinset [0, 2, 4] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_265 : Finset (Fin 10) := literalFinset [0, 3, 8] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_529 : Finset (Fin 10) := literalFinset [0, 4, 9] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_134 : Finset (Fin 10) := literalFinset [1, 2, 7] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_202 : Finset (Fin 10) := literalFinset [1, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_60 : Finset (Fin 10) := literalFinset [2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_76 : Finset (Fin 10) := literalFinset [2, 3, 6] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_148 : Finset (Fin 10) := literalFinset [2, 4, 7] (by decide +kernel)
noncomputable def vertices_196 : Finset (Fin 10) := literalFinset [2, 6, 7] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_104 : Finset (Fin 10) := literalFinset [3, 5, 6] (by decide +kernel)
noncomputable def vertices_328 : Finset (Fin 10) := literalFinset [3, 6, 8] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_208 : Finset (Fin 10) := literalFinset [4, 6, 7] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_608 : Finset (Fin 10) := literalFinset [5, 6, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_779, vertices_661, vertices_361, vertices_817, vertices_206, vertices_902, vertices_458, vertices_124, vertices_212, vertices_752, vertices_864, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_517, vertices_41, vertices_265, vertices_49, vertices_529, vertices_289, vertices_769, vertices_14, vertices_134, vertices_518, vertices_202, vertices_266, vertices_386, vertices_770, vertices_60, vertices_76, vertices_84, vertices_148, vertices_196, vertices_644, vertices_104, vertices_328, vertices_112, vertices_560, vertices_208, vertices_656, vertices_352, vertices_608, vertices_800, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_779), (false, vertices_661), (false, vertices_361), (false, vertices_817), (true, vertices_134), (true, vertices_202), (true, vertices_386), (true, vertices_76), (true, vertices_84), (true, vertices_196), (true, vertices_112), (true, vertices_208), (true, vertices_608), (true, vertices_448), (true, vertices_704), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![18, 13, 21, 15, 23, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_779) then 19 else
  if p.val = (false, vertices_661) then 14 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_817) then 17 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_202) then 20 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
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
  frame := ![0, 1, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_902, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_134, (by decide +kernel)⟩ ⟨vertices_902, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 3
  frame := ![0, 2, 5]
  vertex := 6
  face := Sum.inr ⟨vertices_202, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_202, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 3
  frame := ![1, 2, 3]
  vertex := 4
  face := Sum.inr ⟨vertices_60, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![3, 4, 5, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_752, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_752, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![7, 0, 1, 3]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_206, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_206, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_902, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_134, (by decide +kernel)⟩ ⟨vertices_902, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_458, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 2, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_202, (by decide +kernel)⟩ ⟨vertices_458, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_124, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_124, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_212, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![1, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_212, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_752, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![3, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_752, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_864, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![4, 5, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_352, (by decide +kernel)⟩ ⟨vertices_864, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1171

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_one_six_1172.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1172

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_519 : Finset (Fin 10) := literalFinset [0, 1, 2, 9] (by decide +kernel)
noncomputable def vertices_779 : Finset (Fin 10) := literalFinset [0, 1, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_661 : Finset (Fin 10) := literalFinset [0, 2, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_361 : Finset (Fin 10) := literalFinset [0, 3, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_817 : Finset (Fin 10) := literalFinset [0, 4, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_206 : Finset (Fin 10) := literalFinset [1, 2, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_902 : Finset (Fin 10) := literalFinset [1, 2, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_458 : Finset (Fin 10) := literalFinset [1, 3, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_124 : Finset (Fin 10) := literalFinset [2, 3, 4, 5, 6] (by decide +kernel)
noncomputable def vertices_212 : Finset (Fin 10) := literalFinset [2, 4, 6, 7] (by decide +kernel)
noncomputable def vertices_624 : Finset (Fin 10) := literalFinset [4, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_720 : Finset (Fin 10) := literalFinset [4, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_992 : Finset (Fin 10) := literalFinset [5, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_515 : Finset (Fin 10) := literalFinset [0, 1, 9] (by decide +kernel)
noncomputable def vertices_21 : Finset (Fin 10) := literalFinset [0, 2, 4] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_265 : Finset (Fin 10) := literalFinset [0, 3, 8] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_529 : Finset (Fin 10) := literalFinset [0, 4, 9] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_134 : Finset (Fin 10) := literalFinset [1, 2, 7] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_202 : Finset (Fin 10) := literalFinset [1, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_60 : Finset (Fin 10) := literalFinset [2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_76 : Finset (Fin 10) := literalFinset [2, 3, 6] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_148 : Finset (Fin 10) := literalFinset [2, 4, 7] (by decide +kernel)
noncomputable def vertices_196 : Finset (Fin 10) := literalFinset [2, 6, 7] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_104 : Finset (Fin 10) := literalFinset [3, 5, 6] (by decide +kernel)
noncomputable def vertices_328 : Finset (Fin 10) := literalFinset [3, 6, 8] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_208 : Finset (Fin 10) := literalFinset [4, 6, 7] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_608 : Finset (Fin 10) := literalFinset [5, 6, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_779, vertices_661, vertices_361, vertices_817, vertices_206, vertices_902, vertices_458, vertices_124, vertices_212, vertices_624, vertices_720, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_517, vertices_41, vertices_265, vertices_49, vertices_529, vertices_289, vertices_769, vertices_14, vertices_134, vertices_518, vertices_202, vertices_266, vertices_386, vertices_770, vertices_60, vertices_76, vertices_84, vertices_148, vertices_196, vertices_644, vertices_104, vertices_328, vertices_112, vertices_560, vertices_208, vertices_592, vertices_656, vertices_352, vertices_608, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_779), (false, vertices_661), (false, vertices_361), (false, vertices_817), (true, vertices_134), (true, vertices_202), (true, vertices_386), (true, vertices_76), (true, vertices_84), (true, vertices_196), (true, vertices_112), (true, vertices_208), (true, vertices_592), (true, vertices_608), (true, vertices_448), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![18, 13, 21, 15, 23, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_779) then 19 else
  if p.val = (false, vertices_661) then 14 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_817) then 17 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_202) then 20 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
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
  frameSize := 3
  frame := ![1, 2, 3]
  vertex := 4
  face := Sum.inr ⟨vertices_60, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 3
  frame := ![0, 2, 5]
  vertex := 6
  face := Sum.inr ⟨vertices_202, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_202, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
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
noncomputable def pivot : Fin 4 → Fin 9 := ![3, 2, 0, 4]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_206, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_206, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_902, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_134, (by decide +kernel)⟩ ⟨vertices_902, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_458, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 2, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_202, (by decide +kernel)⟩ ⟨vertices_458, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_124, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_124, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_212, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![1, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_212, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_624, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![3, 4, 5, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_624, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_720, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![3, 5, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_208, (by decide +kernel)⟩ ⟨vertices_720, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_992, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .oneRow ![4, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_352, (by decide +kernel)⟩ ⟨vertices_992, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1172

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_one_six_1173.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1173

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_519 : Finset (Fin 10) := literalFinset [0, 1, 2, 9] (by decide +kernel)
noncomputable def vertices_779 : Finset (Fin 10) := literalFinset [0, 1, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_661 : Finset (Fin 10) := literalFinset [0, 2, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_361 : Finset (Fin 10) := literalFinset [0, 3, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_817 : Finset (Fin 10) := literalFinset [0, 4, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_206 : Finset (Fin 10) := literalFinset [1, 2, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_902 : Finset (Fin 10) := literalFinset [1, 2, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_458 : Finset (Fin 10) := literalFinset [1, 3, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_124 : Finset (Fin 10) := literalFinset [2, 3, 4, 5, 6] (by decide +kernel)
noncomputable def vertices_212 : Finset (Fin 10) := literalFinset [2, 4, 6, 7] (by decide +kernel)
noncomputable def vertices_240 : Finset (Fin 10) := literalFinset [4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_688 : Finset (Fin 10) := literalFinset [4, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_992 : Finset (Fin 10) := literalFinset [5, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_515 : Finset (Fin 10) := literalFinset [0, 1, 9] (by decide +kernel)
noncomputable def vertices_21 : Finset (Fin 10) := literalFinset [0, 2, 4] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_265 : Finset (Fin 10) := literalFinset [0, 3, 8] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_529 : Finset (Fin 10) := literalFinset [0, 4, 9] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_134 : Finset (Fin 10) := literalFinset [1, 2, 7] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_202 : Finset (Fin 10) := literalFinset [1, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_60 : Finset (Fin 10) := literalFinset [2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_76 : Finset (Fin 10) := literalFinset [2, 3, 6] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_148 : Finset (Fin 10) := literalFinset [2, 4, 7] (by decide +kernel)
noncomputable def vertices_196 : Finset (Fin 10) := literalFinset [2, 6, 7] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_104 : Finset (Fin 10) := literalFinset [3, 5, 6] (by decide +kernel)
noncomputable def vertices_328 : Finset (Fin 10) := literalFinset [3, 6, 8] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_208 : Finset (Fin 10) := literalFinset [4, 6, 7] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_224 : Finset (Fin 10) := literalFinset [5, 6, 7] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_779, vertices_661, vertices_361, vertices_817, vertices_206, vertices_902, vertices_458, vertices_124, vertices_212, vertices_240, vertices_688, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_517, vertices_41, vertices_265, vertices_49, vertices_529, vertices_289, vertices_769, vertices_14, vertices_134, vertices_518, vertices_202, vertices_266, vertices_386, vertices_770, vertices_60, vertices_76, vertices_84, vertices_148, vertices_196, vertices_644, vertices_104, vertices_328, vertices_112, vertices_176, vertices_560, vertices_208, vertices_656, vertices_224, vertices_352, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_779), (false, vertices_661), (false, vertices_361), (false, vertices_817), (true, vertices_134), (true, vertices_202), (true, vertices_386), (true, vertices_76), (true, vertices_84), (true, vertices_196), (true, vertices_112), (true, vertices_176), (true, vertices_208), (true, vertices_224), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![18, 13, 21, 15, 23, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_779) then 19 else
  if p.val = (false, vertices_661) then 14 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_817) then 17 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_202) then 20 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_448) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
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
  frameSize := 3
  frame := ![1, 2, 3]
  vertex := 4
  face := Sum.inr ⟨vertices_60, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 3
  frame := ![0, 2, 5]
  vertex := 6
  face := Sum.inr ⟨vertices_202, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_202, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
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
noncomputable def pivot : Fin 4 → Fin 9 := ![3, 2, 0, 4]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_206, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_206, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_902, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_134, (by decide +kernel)⟩ ⟨vertices_902, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_458, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 2, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_202, (by decide +kernel)⟩ ⟨vertices_458, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_124, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_124, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_212, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![1, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_212, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_240, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![3, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_240, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_688, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![3, 4, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_176, (by decide +kernel)⟩ ⟨vertices_688, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_992, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .oneRow ![4, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_224, (by decide +kernel)⟩ ⟨vertices_992, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1173

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_one_six_1174.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1174

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_199 : Finset (Fin 10) := literalFinset [0, 1, 2, 6, 7] (by decide +kernel)
noncomputable def vertices_779 : Finset (Fin 10) := literalFinset [0, 1, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_451 : Finset (Fin 10) := literalFinset [0, 1, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_117 : Finset (Fin 10) := literalFinset [0, 2, 4, 5, 6] (by decide +kernel)
noncomputable def vertices_361 : Finset (Fin 10) := literalFinset [0, 3, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_526 : Finset (Fin 10) := literalFinset [1, 2, 3, 9] (by decide +kernel)
noncomputable def vertices_902 : Finset (Fin 10) := literalFinset [1, 2, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_540 : Finset (Fin 10) := literalFinset [2, 3, 4, 9] (by decide +kernel)
noncomputable def vertices_724 : Finset (Fin 10) := literalFinset [2, 4, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_696 : Finset (Fin 10) := literalFinset [3, 4, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_424 : Finset (Fin 10) := literalFinset [3, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_904 : Finset (Fin 10) := literalFinset [3, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_496 : Finset (Fin 10) := literalFinset [4, 5, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_195 : Finset (Fin 10) := literalFinset [0, 1, 6, 7] (by decide +kernel)
noncomputable def vertices_259 : Finset (Fin 10) := literalFinset [0, 1, 8] (by decide +kernel)
noncomputable def vertices_53 : Finset (Fin 10) := literalFinset [0, 2, 4, 5] (by decide +kernel)
noncomputable def vertices_69 : Finset (Fin 10) := literalFinset [0, 2, 6] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_265 : Finset (Fin 10) := literalFinset [0, 3, 8] (by decide +kernel)
noncomputable def vertices_97 : Finset (Fin 10) := literalFinset [0, 5, 6] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_134 : Finset (Fin 10) := literalFinset [1, 2, 7] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_522 : Finset (Fin 10) := literalFinset [1, 3, 9] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_28 : Finset (Fin 10) := literalFinset [2, 3, 4] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_532 : Finset (Fin 10) := literalFinset [2, 4, 9] (by decide +kernel)
noncomputable def vertices_196 : Finset (Fin 10) := literalFinset [2, 6, 7] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_56 : Finset (Fin 10) := literalFinset [3, 4, 5] (by decide +kernel)
noncomputable def vertices_536 : Finset (Fin 10) := literalFinset [3, 4, 9] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_392 : Finset (Fin 10) := literalFinset [3, 7, 8] (by decide +kernel)
noncomputable def vertices_648 : Finset (Fin 10) := literalFinset [3, 7, 9] (by decide +kernel)
noncomputable def vertices_776 : Finset (Fin 10) := literalFinset [3, 8, 9] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_208 : Finset (Fin 10) := literalFinset [4, 6, 7] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_451, vertices_117, vertices_361, vertices_526, vertices_902, vertices_540, vertices_724, vertices_696, vertices_424, vertices_904, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_195, vertices_259, vertices_53, vertices_69, vertices_41, vertices_265, vertices_97, vertices_321, vertices_14, vertices_134, vertices_518, vertices_522, vertices_386, vertices_770, vertices_28, vertices_524, vertices_84, vertices_532, vertices_196, vertices_644, vertices_56, vertices_536, vertices_168, vertices_296, vertices_392, vertices_648, vertices_776, vertices_112, vertices_176, vertices_208, vertices_656, vertices_352, vertices_416, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_451), (false, vertices_117), (false, vertices_361), (true, vertices_518), (true, vertices_524), (true, vertices_532), (true, vertices_644), (true, vertices_536), (true, vertices_168), (true, vertices_392), (true, vertices_648), (true, vertices_176), (true, vertices_208), (true, vertices_656), (true, vertices_416), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![19, 13, 15, 22, 23, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 20 else
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_451) then 21 else
  if p.val = (false, vertices_117) then 14 else
  if p.val = (false, vertices_361) then 18 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_644) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_416) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 22 => Sum.inl 3
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
  frame := ![0, 1, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_902, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_134, (by decide +kernel)⟩ ⟨vertices_902, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
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

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![2, 3, 4, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_696, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_696, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![3, 4, 5, 6]
  vertex := 7
  face := Sum.inl ⟨vertices_496, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_496, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 1, 2, 3]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_526, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .fundamental ![0, 1, 2, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_526, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_902, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_134, (by decide +kernel)⟩ ⟨vertices_902, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_540, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![1, 2, 3, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_28, (by decide +kernel)⟩ ⟨vertices_540, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_724, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_724, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_696, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![2, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_696, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_424, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![2, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_168, (by decide +kernel)⟩ ⟨vertices_424, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_904, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![2, 6, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_392, (by decide +kernel)⟩ ⟨vertices_904, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_496, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .oneRow ![3, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_496, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1174

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_one_six_1175.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1175

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_199 : Finset (Fin 10) := literalFinset [0, 1, 2, 6, 7] (by decide +kernel)
noncomputable def vertices_779 : Finset (Fin 10) := literalFinset [0, 1, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_451 : Finset (Fin 10) := literalFinset [0, 1, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_117 : Finset (Fin 10) := literalFinset [0, 2, 4, 5, 6] (by decide +kernel)
noncomputable def vertices_361 : Finset (Fin 10) := literalFinset [0, 3, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_526 : Finset (Fin 10) := literalFinset [1, 2, 3, 9] (by decide +kernel)
noncomputable def vertices_902 : Finset (Fin 10) := literalFinset [1, 2, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_540 : Finset (Fin 10) := literalFinset [2, 3, 4, 9] (by decide +kernel)
noncomputable def vertices_724 : Finset (Fin 10) := literalFinset [2, 4, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_696 : Finset (Fin 10) := literalFinset [3, 4, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_808 : Finset (Fin 10) := literalFinset [3, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_496 : Finset (Fin 10) := literalFinset [4, 5, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_928 : Finset (Fin 10) := literalFinset [5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_195 : Finset (Fin 10) := literalFinset [0, 1, 6, 7] (by decide +kernel)
noncomputable def vertices_259 : Finset (Fin 10) := literalFinset [0, 1, 8] (by decide +kernel)
noncomputable def vertices_53 : Finset (Fin 10) := literalFinset [0, 2, 4, 5] (by decide +kernel)
noncomputable def vertices_69 : Finset (Fin 10) := literalFinset [0, 2, 6] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_265 : Finset (Fin 10) := literalFinset [0, 3, 8] (by decide +kernel)
noncomputable def vertices_97 : Finset (Fin 10) := literalFinset [0, 5, 6] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_134 : Finset (Fin 10) := literalFinset [1, 2, 7] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_522 : Finset (Fin 10) := literalFinset [1, 3, 9] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_28 : Finset (Fin 10) := literalFinset [2, 3, 4] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_532 : Finset (Fin 10) := literalFinset [2, 4, 9] (by decide +kernel)
noncomputable def vertices_196 : Finset (Fin 10) := literalFinset [2, 6, 7] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_56 : Finset (Fin 10) := literalFinset [3, 4, 5] (by decide +kernel)
noncomputable def vertices_536 : Finset (Fin 10) := literalFinset [3, 4, 9] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_552 : Finset (Fin 10) := literalFinset [3, 5, 9] (by decide +kernel)
noncomputable def vertices_776 : Finset (Fin 10) := literalFinset [3, 8, 9] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_208 : Finset (Fin 10) := literalFinset [4, 6, 7] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_451, vertices_117, vertices_361, vertices_526, vertices_902, vertices_540, vertices_724, vertices_696, vertices_808, vertices_496, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_195, vertices_259, vertices_53, vertices_69, vertices_41, vertices_265, vertices_97, vertices_321, vertices_14, vertices_134, vertices_518, vertices_522, vertices_386, vertices_770, vertices_28, vertices_524, vertices_84, vertices_532, vertices_196, vertices_644, vertices_56, vertices_536, vertices_296, vertices_552, vertices_776, vertices_112, vertices_176, vertices_208, vertices_656, vertices_352, vertices_416, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_451), (false, vertices_117), (false, vertices_361), (true, vertices_518), (true, vertices_524), (true, vertices_532), (true, vertices_644), (true, vertices_536), (true, vertices_552), (true, vertices_176), (true, vertices_208), (true, vertices_656), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![19, 13, 15, 22, 23, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 20 else
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_451) then 21 else
  if p.val = (false, vertices_117) then 14 else
  if p.val = (false, vertices_361) then 18 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_644) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_656) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_800) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 22 => Sum.inl 3
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
  frame := ![0, 1, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_902, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_134, (by decide +kernel)⟩ ⟨vertices_902, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
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

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![2, 3, 4, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_696, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_696, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![3, 4, 5, 6]
  vertex := 7
  face := Sum.inl ⟨vertices_496, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_496, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 1, 2, 3]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_526, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .fundamental ![0, 1, 2, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_526, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_902, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_134, (by decide +kernel)⟩ ⟨vertices_902, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_540, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![1, 2, 3, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_28, (by decide +kernel)⟩ ⟨vertices_540, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_724, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_724, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_696, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![2, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_696, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_808, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![2, 4, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_296, (by decide +kernel)⟩ ⟨vertices_808, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_496, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![3, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_496, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1175

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_one_six_1176.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1176

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_199 : Finset (Fin 10) := literalFinset [0, 1, 2, 6, 7] (by decide +kernel)
noncomputable def vertices_779 : Finset (Fin 10) := literalFinset [0, 1, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_451 : Finset (Fin 10) := literalFinset [0, 1, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_117 : Finset (Fin 10) := literalFinset [0, 2, 4, 5, 6] (by decide +kernel)
noncomputable def vertices_361 : Finset (Fin 10) := literalFinset [0, 3, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_526 : Finset (Fin 10) := literalFinset [1, 2, 3, 9] (by decide +kernel)
noncomputable def vertices_902 : Finset (Fin 10) := literalFinset [1, 2, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_540 : Finset (Fin 10) := literalFinset [2, 3, 4, 9] (by decide +kernel)
noncomputable def vertices_724 : Finset (Fin 10) := literalFinset [2, 4, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_568 : Finset (Fin 10) := literalFinset [3, 4, 5, 9] (by decide +kernel)
noncomputable def vertices_936 : Finset (Fin 10) := literalFinset [3, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_496 : Finset (Fin 10) := literalFinset [4, 5, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_688 : Finset (Fin 10) := literalFinset [4, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_195 : Finset (Fin 10) := literalFinset [0, 1, 6, 7] (by decide +kernel)
noncomputable def vertices_259 : Finset (Fin 10) := literalFinset [0, 1, 8] (by decide +kernel)
noncomputable def vertices_53 : Finset (Fin 10) := literalFinset [0, 2, 4, 5] (by decide +kernel)
noncomputable def vertices_69 : Finset (Fin 10) := literalFinset [0, 2, 6] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_265 : Finset (Fin 10) := literalFinset [0, 3, 8] (by decide +kernel)
noncomputable def vertices_97 : Finset (Fin 10) := literalFinset [0, 5, 6] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_134 : Finset (Fin 10) := literalFinset [1, 2, 7] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_522 : Finset (Fin 10) := literalFinset [1, 3, 9] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_28 : Finset (Fin 10) := literalFinset [2, 3, 4] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_532 : Finset (Fin 10) := literalFinset [2, 4, 9] (by decide +kernel)
noncomputable def vertices_196 : Finset (Fin 10) := literalFinset [2, 6, 7] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_56 : Finset (Fin 10) := literalFinset [3, 4, 5] (by decide +kernel)
noncomputable def vertices_536 : Finset (Fin 10) := literalFinset [3, 4, 9] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_552 : Finset (Fin 10) := literalFinset [3, 5, 9] (by decide +kernel)
noncomputable def vertices_776 : Finset (Fin 10) := literalFinset [3, 8, 9] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_208 : Finset (Fin 10) := literalFinset [4, 6, 7] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_451, vertices_117, vertices_361, vertices_526, vertices_902, vertices_540, vertices_724, vertices_568, vertices_936, vertices_496, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_195, vertices_259, vertices_53, vertices_69, vertices_41, vertices_265, vertices_97, vertices_321, vertices_14, vertices_134, vertices_518, vertices_522, vertices_386, vertices_770, vertices_28, vertices_524, vertices_84, vertices_532, vertices_196, vertices_644, vertices_56, vertices_536, vertices_296, vertices_552, vertices_776, vertices_112, vertices_176, vertices_560, vertices_208, vertices_656, vertices_352, vertices_416, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_451), (false, vertices_117), (false, vertices_361), (true, vertices_518), (true, vertices_524), (true, vertices_532), (true, vertices_644), (true, vertices_536), (true, vertices_552), (true, vertices_176), (true, vertices_560), (true, vertices_208), (true, vertices_656), (true, vertices_416), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![19, 13, 15, 22, 23, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 20 else
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_451) then 21 else
  if p.val = (false, vertices_117) then 14 else
  if p.val = (false, vertices_361) then 18 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_644) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_416) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 22 => Sum.inl 3
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
  frame := ![0, 1, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_902, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_134, (by decide +kernel)⟩ ⟨vertices_902, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
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

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![2, 4, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_936, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_296, (by decide +kernel)⟩ ⟨vertices_936, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![3, 4, 5, 6]
  vertex := 7
  face := Sum.inl ⟨vertices_496, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_496, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 1, 2, 3]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_526, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .fundamental ![0, 1, 2, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_526, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_902, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_134, (by decide +kernel)⟩ ⟨vertices_902, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_540, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![1, 2, 3, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_28, (by decide +kernel)⟩ ⟨vertices_540, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_724, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_724, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_568, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![2, 3, 4, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_568, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_936, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![2, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_296, (by decide +kernel)⟩ ⟨vertices_936, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_496, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![3, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_496, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_688, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![3, 4, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_176, (by decide +kernel)⟩ ⟨vertices_688, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1176

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_one_six_1177.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1177

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_199 : Finset (Fin 10) := literalFinset [0, 1, 2, 6, 7] (by decide +kernel)
noncomputable def vertices_779 : Finset (Fin 10) := literalFinset [0, 1, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_451 : Finset (Fin 10) := literalFinset [0, 1, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_117 : Finset (Fin 10) := literalFinset [0, 2, 4, 5, 6] (by decide +kernel)
noncomputable def vertices_361 : Finset (Fin 10) := literalFinset [0, 3, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_526 : Finset (Fin 10) := literalFinset [1, 2, 3, 9] (by decide +kernel)
noncomputable def vertices_902 : Finset (Fin 10) := literalFinset [1, 2, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_540 : Finset (Fin 10) := literalFinset [2, 3, 4, 9] (by decide +kernel)
noncomputable def vertices_724 : Finset (Fin 10) := literalFinset [2, 4, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_184 : Finset (Fin 10) := literalFinset [3, 4, 5, 7] (by decide +kernel)
noncomputable def vertices_664 : Finset (Fin 10) := literalFinset [3, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_936 : Finset (Fin 10) := literalFinset [3, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_496 : Finset (Fin 10) := literalFinset [4, 5, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_195 : Finset (Fin 10) := literalFinset [0, 1, 6, 7] (by decide +kernel)
noncomputable def vertices_259 : Finset (Fin 10) := literalFinset [0, 1, 8] (by decide +kernel)
noncomputable def vertices_53 : Finset (Fin 10) := literalFinset [0, 2, 4, 5] (by decide +kernel)
noncomputable def vertices_69 : Finset (Fin 10) := literalFinset [0, 2, 6] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_265 : Finset (Fin 10) := literalFinset [0, 3, 8] (by decide +kernel)
noncomputable def vertices_97 : Finset (Fin 10) := literalFinset [0, 5, 6] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_134 : Finset (Fin 10) := literalFinset [1, 2, 7] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_522 : Finset (Fin 10) := literalFinset [1, 3, 9] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_28 : Finset (Fin 10) := literalFinset [2, 3, 4] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_532 : Finset (Fin 10) := literalFinset [2, 4, 9] (by decide +kernel)
noncomputable def vertices_196 : Finset (Fin 10) := literalFinset [2, 6, 7] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_56 : Finset (Fin 10) := literalFinset [3, 4, 5] (by decide +kernel)
noncomputable def vertices_152 : Finset (Fin 10) := literalFinset [3, 4, 7] (by decide +kernel)
noncomputable def vertices_536 : Finset (Fin 10) := literalFinset [3, 4, 9] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_648 : Finset (Fin 10) := literalFinset [3, 7, 9] (by decide +kernel)
noncomputable def vertices_776 : Finset (Fin 10) := literalFinset [3, 8, 9] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_208 : Finset (Fin 10) := literalFinset [4, 6, 7] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_451, vertices_117, vertices_361, vertices_526, vertices_902, vertices_540, vertices_724, vertices_184, vertices_664, vertices_936, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_195, vertices_259, vertices_53, vertices_69, vertices_41, vertices_265, vertices_97, vertices_321, vertices_14, vertices_134, vertices_518, vertices_522, vertices_386, vertices_770, vertices_28, vertices_524, vertices_84, vertices_532, vertices_196, vertices_644, vertices_56, vertices_152, vertices_536, vertices_168, vertices_296, vertices_648, vertices_776, vertices_112, vertices_176, vertices_208, vertices_656, vertices_352, vertices_416, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_451), (false, vertices_117), (false, vertices_361), (true, vertices_518), (true, vertices_524), (true, vertices_532), (true, vertices_644), (true, vertices_152), (true, vertices_536), (true, vertices_168), (true, vertices_648), (true, vertices_176), (true, vertices_208), (true, vertices_656), (true, vertices_416), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![19, 13, 15, 22, 23, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 20 else
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_451) then 21 else
  if p.val = (false, vertices_117) then 14 else
  if p.val = (false, vertices_361) then 18 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_644) then 3 else
  if p.val = (true, vertices_152) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_416) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 22 => Sum.inl 3
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
  frame := ![0, 1, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_902, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_134, (by decide +kernel)⟩ ⟨vertices_902, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
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

noncomputable def row2 : HeightRow boundary where
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

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![3, 4, 5, 6]
  vertex := 7
  face := Sum.inl ⟨vertices_496, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_496, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 1, 2, 3]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_526, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .fundamental ![0, 1, 2, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_526, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_902, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_134, (by decide +kernel)⟩ ⟨vertices_902, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_540, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![1, 2, 3, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_28, (by decide +kernel)⟩ ⟨vertices_540, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_724, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_724, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_184, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![2, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_184, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_664, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![2, 3, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_152, (by decide +kernel)⟩ ⟨vertices_664, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_936, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![2, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_168, (by decide +kernel)⟩ ⟨vertices_936, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_496, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .oneRow ![3, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_496, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1177

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_one_six_1178.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1178

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
noncomputable def vertices_124 : Finset (Fin 10) := literalFinset [2, 3, 4, 5, 6] (by decide +kernel)
noncomputable def vertices_460 : Finset (Fin 10) := literalFinset [2, 3, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_232 : Finset (Fin 10) := literalFinset [3, 5, 6, 7] (by decide +kernel)
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
noncomputable def vertices_76 : Finset (Fin 10) := literalFinset [2, 3, 6] (by decide +kernel)
noncomputable def vertices_268 : Finset (Fin 10) := literalFinset [2, 3, 8] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_324 : Finset (Fin 10) := literalFinset [2, 6, 8] (by decide +kernel)
noncomputable def vertices_104 : Finset (Fin 10) := literalFinset [3, 5, 6] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_200 : Finset (Fin 10) := literalFinset [3, 6, 7] (by decide +kernel)
noncomputable def vertices_392 : Finset (Fin 10) := literalFinset [3, 7, 8] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_224 : Finset (Fin 10) := literalFinset [5, 6, 7] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_779, vertices_597, vertices_425, vertices_817, vertices_270, vertices_326, vertices_962, vertices_124, vertices_460, vertices_232, vertices_752, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_581, vertices_41, vertices_265, vertices_49, vertices_529, vertices_289, vertices_769, vertices_14, vertices_70, vertices_262, vertices_266, vertices_322, vertices_578, vertices_770, vertices_60, vertices_76, vertices_268, vertices_84, vertices_324, vertices_104, vertices_168, vertices_200, vertices_392, vertices_112, vertices_560, vertices_592, vertices_224, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_779), (false, vertices_597), (false, vertices_425), (false, vertices_817), (true, vertices_262), (true, vertices_322), (true, vertices_76), (true, vertices_268), (true, vertices_324), (true, vertices_104), (true, vertices_200), (true, vertices_112), (true, vertices_224), (true, vertices_672), (true, vertices_448), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 15, 19, 21, 23, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_583) then 17 else
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_597) then 18 else
  if p.val = (false, vertices_425) then 20 else
  if p.val = (false, vertices_817) then 22 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_324) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_200) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
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
  frame := ![1, 2, 5, 6]
  vertex := 7
  face := Sum.inl ⟨vertices_460, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_76, (by decide +kernel)⟩ ⟨vertices_460, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 3
  frame := ![1, 2, 3]
  vertex := 4
  face := Sum.inr ⟨vertices_60, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![3, 4, 5, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_752, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_752, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 7, 1, 3]
noncomputable def heightProof : HeightCertificate boundary 4 :=
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

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_124, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_124, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_460, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![1, 2, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_76, (by decide +kernel)⟩ ⟨vertices_460, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_232, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![2, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_104, (by decide +kernel)⟩ ⟨vertices_232, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_752, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![3, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_752, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1178

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_one_six_1179.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1179

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_583 : Finset (Fin 10) := literalFinset [0, 1, 2, 6, 9] (by decide +kernel)
noncomputable def vertices_779 : Finset (Fin 10) := literalFinset [0, 1, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_597 : Finset (Fin 10) := literalFinset [0, 2, 4, 6, 9] (by decide +kernel)
noncomputable def vertices_425 : Finset (Fin 10) := literalFinset [0, 3, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_177 : Finset (Fin 10) := literalFinset [0, 4, 5, 7] (by decide +kernel)
noncomputable def vertices_913 : Finset (Fin 10) := literalFinset [0, 4, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_270 : Finset (Fin 10) := literalFinset [1, 2, 3, 8] (by decide +kernel)
noncomputable def vertices_326 : Finset (Fin 10) := literalFinset [1, 2, 6, 8] (by decide +kernel)
noncomputable def vertices_962 : Finset (Fin 10) := literalFinset [1, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_124 : Finset (Fin 10) := literalFinset [2, 3, 4, 5, 6] (by decide +kernel)
noncomputable def vertices_460 : Finset (Fin 10) := literalFinset [2, 3, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_232 : Finset (Fin 10) := literalFinset [3, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_752 : Finset (Fin 10) := literalFinset [4, 5, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_515 : Finset (Fin 10) := literalFinset [0, 1, 9] (by decide +kernel)
noncomputable def vertices_21 : Finset (Fin 10) := literalFinset [0, 2, 4] (by decide +kernel)
noncomputable def vertices_581 : Finset (Fin 10) := literalFinset [0, 2, 6, 9] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_265 : Finset (Fin 10) := literalFinset [0, 3, 8] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_145 : Finset (Fin 10) := literalFinset [0, 4, 7] (by decide +kernel)
noncomputable def vertices_529 : Finset (Fin 10) := literalFinset [0, 4, 9] (by decide +kernel)
noncomputable def vertices_161 : Finset (Fin 10) := literalFinset [0, 5, 7] (by decide +kernel)
noncomputable def vertices_385 : Finset (Fin 10) := literalFinset [0, 7, 8] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_70 : Finset (Fin 10) := literalFinset [1, 2, 6] (by decide +kernel)
noncomputable def vertices_262 : Finset (Fin 10) := literalFinset [1, 2, 8] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_322 : Finset (Fin 10) := literalFinset [1, 6, 8] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_60 : Finset (Fin 10) := literalFinset [2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_76 : Finset (Fin 10) := literalFinset [2, 3, 6] (by decide +kernel)
noncomputable def vertices_268 : Finset (Fin 10) := literalFinset [2, 3, 8] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_324 : Finset (Fin 10) := literalFinset [2, 6, 8] (by decide +kernel)
noncomputable def vertices_104 : Finset (Fin 10) := literalFinset [3, 5, 6] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_200 : Finset (Fin 10) := literalFinset [3, 6, 7] (by decide +kernel)
noncomputable def vertices_392 : Finset (Fin 10) := literalFinset [3, 7, 8] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_224 : Finset (Fin 10) := literalFinset [5, 6, 7] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_583, vertices_779, vertices_597, vertices_425, vertices_177, vertices_913, vertices_270, vertices_326, vertices_962, vertices_124, vertices_460, vertices_232, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_581, vertices_41, vertices_265, vertices_49, vertices_145, vertices_529, vertices_161, vertices_385, vertices_769, vertices_14, vertices_70, vertices_262, vertices_266, vertices_322, vertices_578, vertices_770, vertices_60, vertices_76, vertices_268, vertices_84, vertices_324, vertices_104, vertices_168, vertices_200, vertices_392, vertices_112, vertices_176, vertices_592, vertices_656, vertices_224, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_583), (false, vertices_779), (false, vertices_597), (false, vertices_425), (false, vertices_177), (false, vertices_913), (true, vertices_262), (true, vertices_322), (true, vertices_76), (true, vertices_268), (true, vertices_324), (true, vertices_104), (true, vertices_200), (true, vertices_112), (true, vertices_224), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![12, 14, 18, 20, 22, 23, 24, 25, 26]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_583) then 16 else
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_597) then 17 else
  if p.val = (false, vertices_425) then 19 else
  if p.val = (false, vertices_177) then 0 else
  if p.val = (false, vertices_913) then 21 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_704) then 11 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_177), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
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
  frame := ![1, 2, 5, 6]
  vertex := 7
  face := Sum.inl ⟨vertices_460, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_76, (by decide +kernel)⟩ ⟨vertices_460, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 3
  frame := ![1, 2, 3]
  vertex := 4
  face := Sum.inr ⟨vertices_60, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![3, 4, 5, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_752, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_752, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 7, 1, 3]
noncomputable def heightProof : HeightCertificate boundary 4 :=
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

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_124, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_124, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_460, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![1, 2, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_76, (by decide +kernel)⟩ ⟨vertices_460, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_232, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![2, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_104, (by decide +kernel)⟩ ⟨vertices_232, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_752, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![3, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_752, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1179

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_one_six_1180.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1180

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_775 : Finset (Fin 10) := literalFinset [0, 1, 2, 8, 9] (by decide +kernel)
noncomputable def vertices_267 : Finset (Fin 10) := literalFinset [0, 1, 3, 8] (by decide +kernel)
noncomputable def vertices_341 : Finset (Fin 10) := literalFinset [0, 2, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_121 : Finset (Fin 10) := literalFinset [0, 3, 4, 5, 6] (by decide +kernel)
noncomputable def vertices_457 : Finset (Fin 10) := literalFinset [0, 3, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_654 : Finset (Fin 10) := literalFinset [1, 2, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_394 : Finset (Fin 10) := literalFinset [1, 3, 7, 8] (by decide +kernel)
noncomputable def vertices_962 : Finset (Fin 10) := literalFinset [1, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_684 : Finset (Fin 10) := literalFinset [2, 3, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_820 : Finset (Fin 10) := literalFinset [2, 4, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_232 : Finset (Fin 10) := literalFinset [3, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_752 : Finset (Fin 10) := literalFinset [4, 5, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_848 : Finset (Fin 10) := literalFinset [4, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_259 : Finset (Fin 10) := literalFinset [0, 1, 8] (by decide +kernel)
noncomputable def vertices_21 : Finset (Fin 10) := literalFinset [0, 2, 4] (by decide +kernel)
noncomputable def vertices_261 : Finset (Fin 10) := literalFinset [0, 2, 8] (by decide +kernel)
noncomputable def vertices_57 : Finset (Fin 10) := literalFinset [0, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_73 : Finset (Fin 10) := literalFinset [0, 3, 6] (by decide +kernel)
noncomputable def vertices_265 : Finset (Fin 10) := literalFinset [0, 3, 8] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_138 : Finset (Fin 10) := literalFinset [1, 3, 7] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_652 : Finset (Fin 10) := literalFinset [2, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_548 : Finset (Fin 10) := literalFinset [2, 5, 9] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_104 : Finset (Fin 10) := literalFinset [3, 5, 6] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_200 : Finset (Fin 10) := literalFinset [3, 6, 7] (by decide +kernel)
noncomputable def vertices_392 : Finset (Fin 10) := literalFinset [3, 7, 8] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_784 : Finset (Fin 10) := literalFinset [4, 8, 9] (by decide +kernel)
noncomputable def vertices_224 : Finset (Fin 10) := literalFinset [5, 6, 7] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_267, vertices_341, vertices_121, vertices_457, vertices_654, vertices_394, vertices_962, vertices_684, vertices_820, vertices_232, vertices_752, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_265, vertices_81, vertices_321, vertices_14, vertices_518, vertices_138, vertices_266, vertices_386, vertices_642, vertices_770, vertices_44, vertices_652, vertices_52, vertices_276, vertices_548, vertices_772, vertices_104, vertices_168, vertices_200, vertices_392, vertices_112, vertices_560, vertices_336, vertices_592, vertices_784, vertices_224, vertices_672, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_267), (false, vertices_341), (false, vertices_121), (false, vertices_457), (true, vertices_138), (true, vertices_386), (true, vertices_642), (true, vertices_652), (true, vertices_548), (true, vertices_168), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_224), (true, vertices_672), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 15, 18, 22, 23, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 19 else
  if p.val = (false, vertices_775) then 14 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_341) then 16 else
  if p.val = (false, vertices_121) then 20 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_652) then 17 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_652), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 22 => Sum.inl 3
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
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_386, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
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
  frame := ![3, 4, 5, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_752, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_752, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![2, 0, 1, 3]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_654, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_654, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_394, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 2, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_138, (by decide +kernel)⟩ ⟨vertices_394, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_962, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_386, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_684, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 2, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_684, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_820, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![1, 3, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_820, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_232, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![2, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_104, (by decide +kernel)⟩ ⟨vertices_232, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_752, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![3, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_752, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1180

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_one_six_1181.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1181

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_775 : Finset (Fin 10) := literalFinset [0, 1, 2, 8, 9] (by decide +kernel)
noncomputable def vertices_651 : Finset (Fin 10) := literalFinset [0, 1, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_789 : Finset (Fin 10) := literalFinset [0, 2, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_233 : Finset (Fin 10) := literalFinset [0, 3, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_689 : Finset (Fin 10) := literalFinset [0, 4, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_270 : Finset (Fin 10) := literalFinset [1, 2, 3, 8] (by decide +kernel)
noncomputable def vertices_394 : Finset (Fin 10) := literalFinset [1, 3, 7, 8] (by decide +kernel)
noncomputable def vertices_962 : Finset (Fin 10) := literalFinset [1, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_124 : Finset (Fin 10) := literalFinset [2, 3, 4, 5, 6] (by decide +kernel)
noncomputable def vertices_460 : Finset (Fin 10) := literalFinset [2, 3, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_340 : Finset (Fin 10) := literalFinset [2, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_880 : Finset (Fin 10) := literalFinset [4, 5, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_736 : Finset (Fin 10) := literalFinset [5, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_515 : Finset (Fin 10) := literalFinset [0, 1, 9] (by decide +kernel)
noncomputable def vertices_21 : Finset (Fin 10) := literalFinset [0, 2, 4] (by decide +kernel)
noncomputable def vertices_773 : Finset (Fin 10) := literalFinset [0, 2, 8, 9] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_529 : Finset (Fin 10) := literalFinset [0, 4, 9] (by decide +kernel)
noncomputable def vertices_161 : Finset (Fin 10) := literalFinset [0, 5, 7] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_262 : Finset (Fin 10) := literalFinset [1, 2, 8] (by decide +kernel)
noncomputable def vertices_138 : Finset (Fin 10) := literalFinset [1, 3, 7] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_60 : Finset (Fin 10) := literalFinset [2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_76 : Finset (Fin 10) := literalFinset [2, 3, 6] (by decide +kernel)
noncomputable def vertices_268 : Finset (Fin 10) := literalFinset [2, 3, 8] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_324 : Finset (Fin 10) := literalFinset [2, 6, 8] (by decide +kernel)
noncomputable def vertices_104 : Finset (Fin 10) := literalFinset [3, 5, 6] (by decide +kernel)
noncomputable def vertices_200 : Finset (Fin 10) := literalFinset [3, 6, 7] (by decide +kernel)
noncomputable def vertices_392 : Finset (Fin 10) := literalFinset [3, 7, 8] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_784 : Finset (Fin 10) := literalFinset [4, 8, 9] (by decide +kernel)
noncomputable def vertices_224 : Finset (Fin 10) := literalFinset [5, 6, 7] (by decide +kernel)
noncomputable def vertices_608 : Finset (Fin 10) := literalFinset [5, 6, 9] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_651, vertices_789, vertices_233, vertices_689, vertices_270, vertices_394, vertices_962, vertices_124, vertices_460, vertices_340, vertices_880, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_773, vertices_41, vertices_137, vertices_49, vertices_529, vertices_161, vertices_641, vertices_14, vertices_262, vertices_138, vertices_266, vertices_386, vertices_642, vertices_770, vertices_60, vertices_76, vertices_268, vertices_84, vertices_276, vertices_324, vertices_104, vertices_200, vertices_392, vertices_112, vertices_560, vertices_336, vertices_784, vertices_224, vertices_608, vertices_672, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_651), (false, vertices_789), (false, vertices_233), (false, vertices_689), (true, vertices_266), (true, vertices_386), (true, vertices_76), (true, vertices_268), (true, vertices_84), (true, vertices_324), (true, vertices_392), (true, vertices_112), (true, vertices_336), (true, vertices_608), (true, vertices_448), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 15, 19, 21, 23, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_651) then 14 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_233) then 20 else
  if p.val = (false, vertices_689) then 22 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_386) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
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
  frame := ![0, 5, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_962, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_386, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 5, 6]
  vertex := 7
  face := Sum.inl ⟨vertices_460, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_76, (by decide +kernel)⟩ ⟨vertices_460, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 3
  frame := ![1, 2, 3]
  vertex := 4
  face := Sum.inr ⟨vertices_60, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![3, 4, 5, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_880, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_880, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 6, 1, 3]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_270, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .fundamental ![0, 1, 2, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_270, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_394, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 2, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_138, (by decide +kernel)⟩ ⟨vertices_394, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_962, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_386, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_124, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_124, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_460, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![1, 2, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_76, (by decide +kernel)⟩ ⟨vertices_460, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_340, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![1, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_340, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_880, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![3, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_880, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_736, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![4, 5, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_224, (by decide +kernel)⟩ ⟨vertices_736, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1181

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_one_six_1196.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1196

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_263 : Finset (Fin 10) := literalFinset [0, 1, 2, 8] (by decide +kernel)
noncomputable def vertices_651 : Finset (Fin 10) := literalFinset [0, 1, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_771 : Finset (Fin 10) := literalFinset [0, 1, 8, 9] (by decide +kernel)
noncomputable def vertices_789 : Finset (Fin 10) := literalFinset [0, 2, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_233 : Finset (Fin 10) := literalFinset [0, 3, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_689 : Finset (Fin 10) := literalFinset [0, 4, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_398 : Finset (Fin 10) := literalFinset [1, 2, 3, 7, 8] (by decide +kernel)
noncomputable def vertices_962 : Finset (Fin 10) := literalFinset [1, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_124 : Finset (Fin 10) := literalFinset [2, 3, 4, 5, 6] (by decide +kernel)
noncomputable def vertices_460 : Finset (Fin 10) := literalFinset [2, 3, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_340 : Finset (Fin 10) := literalFinset [2, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_880 : Finset (Fin 10) := literalFinset [4, 5, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_736 : Finset (Fin 10) := literalFinset [5, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_259 : Finset (Fin 10) := literalFinset [0, 1, 8] (by decide +kernel)
noncomputable def vertices_515 : Finset (Fin 10) := literalFinset [0, 1, 9] (by decide +kernel)
noncomputable def vertices_21 : Finset (Fin 10) := literalFinset [0, 2, 4] (by decide +kernel)
noncomputable def vertices_261 : Finset (Fin 10) := literalFinset [0, 2, 8] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_529 : Finset (Fin 10) := literalFinset [0, 4, 9] (by decide +kernel)
noncomputable def vertices_161 : Finset (Fin 10) := literalFinset [0, 5, 7] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_262 : Finset (Fin 10) := literalFinset [1, 2, 8] (by decide +kernel)
noncomputable def vertices_138 : Finset (Fin 10) := literalFinset [1, 3, 7] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_60 : Finset (Fin 10) := literalFinset [2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_76 : Finset (Fin 10) := literalFinset [2, 3, 6] (by decide +kernel)
noncomputable def vertices_396 : Finset (Fin 10) := literalFinset [2, 3, 7, 8] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_324 : Finset (Fin 10) := literalFinset [2, 6, 8] (by decide +kernel)
noncomputable def vertices_104 : Finset (Fin 10) := literalFinset [3, 5, 6] (by decide +kernel)
noncomputable def vertices_200 : Finset (Fin 10) := literalFinset [3, 6, 7] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_784 : Finset (Fin 10) := literalFinset [4, 8, 9] (by decide +kernel)
noncomputable def vertices_224 : Finset (Fin 10) := literalFinset [5, 6, 7] (by decide +kernel)
noncomputable def vertices_608 : Finset (Fin 10) := literalFinset [5, 6, 9] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_263, vertices_651, vertices_771, vertices_789, vertices_233, vertices_689, vertices_398, vertices_962, vertices_124, vertices_460, vertices_340, vertices_880, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_515, vertices_21, vertices_261, vertices_41, vertices_137, vertices_49, vertices_529, vertices_161, vertices_641, vertices_769, vertices_14, vertices_262, vertices_138, vertices_386, vertices_642, vertices_770, vertices_60, vertices_76, vertices_396, vertices_84, vertices_276, vertices_324, vertices_104, vertices_200, vertices_112, vertices_560, vertices_336, vertices_784, vertices_224, vertices_608, vertices_672, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_263), (false, vertices_651), (false, vertices_771), (false, vertices_789), (false, vertices_233), (false, vertices_689), (true, vertices_386), (true, vertices_76), (true, vertices_396), (true, vertices_84), (true, vertices_324), (true, vertices_112), (true, vertices_336), (true, vertices_608), (true, vertices_448), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![12, 14, 18, 20, 22, 23, 24, 25, 26]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_263) then 0 else
  if p.val = (false, vertices_651) then 13 else
  if p.val = (false, vertices_771) then 1 else
  if p.val = (false, vertices_789) then 16 else
  if p.val = (false, vertices_233) then 19 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_396) then 17 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_263), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
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
  frame := ![0, 5, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_962, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_386, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 3
  frame := ![1, 2, 6]
  vertex := 7
  face := Sum.inr ⟨vertices_396, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_396, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 3
  frame := ![1, 2, 3]
  vertex := 4
  face := Sum.inr ⟨vertices_60, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![3, 4, 5, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_880, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_880, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 6, 1, 3]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_398, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_398, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_962, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_386, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_124, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![1, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_124, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_460, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 2, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_76, (by decide +kernel)⟩ ⟨vertices_460, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_340, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![1, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_340, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_880, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![3, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_880, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_736, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![4, 5, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_224, (by decide +kernel)⟩ ⟨vertices_736, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1196

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_one_six_1197.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1197

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_391 : Finset (Fin 10) := literalFinset [0, 1, 2, 7, 8] (by decide +kernel)
noncomputable def vertices_651 : Finset (Fin 10) := literalFinset [0, 1, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_117 : Finset (Fin 10) := literalFinset [0, 2, 4, 5, 6] (by decide +kernel)
noncomputable def vertices_453 : Finset (Fin 10) := literalFinset [0, 2, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_233 : Finset (Fin 10) := literalFinset [0, 3, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_270 : Finset (Fin 10) := literalFinset [1, 2, 3, 8] (by decide +kernel)
noncomputable def vertices_778 : Finset (Fin 10) := literalFinset [1, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_962 : Finset (Fin 10) := literalFinset [1, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_284 : Finset (Fin 10) := literalFinset [2, 3, 4, 8] (by decide +kernel)
noncomputable def vertices_852 : Finset (Fin 10) := literalFinset [2, 4, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_824 : Finset (Fin 10) := literalFinset [3, 4, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_680 : Finset (Fin 10) := literalFinset [3, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_752 : Finset (Fin 10) := literalFinset [4, 5, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_131 : Finset (Fin 10) := literalFinset [0, 1, 7] (by decide +kernel)
noncomputable def vertices_53 : Finset (Fin 10) := literalFinset [0, 2, 4, 5] (by decide +kernel)
noncomputable def vertices_69 : Finset (Fin 10) := literalFinset [0, 2, 6] (by decide +kernel)
noncomputable def vertices_389 : Finset (Fin 10) := literalFinset [0, 2, 7, 8] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_97 : Finset (Fin 10) := literalFinset [0, 5, 6] (by decide +kernel)
noncomputable def vertices_193 : Finset (Fin 10) := literalFinset [0, 6, 7] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_262 : Finset (Fin 10) := literalFinset [1, 2, 8] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_522 : Finset (Fin 10) := literalFinset [1, 3, 9] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_28 : Finset (Fin 10) := literalFinset [2, 3, 4] (by decide +kernel)
noncomputable def vertices_268 : Finset (Fin 10) := literalFinset [2, 3, 8] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_324 : Finset (Fin 10) := literalFinset [2, 6, 8] (by decide +kernel)
noncomputable def vertices_56 : Finset (Fin 10) := literalFinset [3, 4, 5] (by decide +kernel)
noncomputable def vertices_280 : Finset (Fin 10) := literalFinset [3, 4, 8] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_552 : Finset (Fin 10) := literalFinset [3, 5, 9] (by decide +kernel)
noncomputable def vertices_648 : Finset (Fin 10) := literalFinset [3, 7, 9] (by decide +kernel)
noncomputable def vertices_776 : Finset (Fin 10) := literalFinset [3, 8, 9] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_784 : Finset (Fin 10) := literalFinset [4, 8, 9] (by decide +kernel)
noncomputable def vertices_224 : Finset (Fin 10) := literalFinset [5, 6, 7] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_651, vertices_117, vertices_453, vertices_233, vertices_270, vertices_778, vertices_962, vertices_284, vertices_852, vertices_824, vertices_680, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_53, vertices_69, vertices_389, vertices_41, vertices_137, vertices_97, vertices_193, vertices_14, vertices_262, vertices_266, vertices_522, vertices_386, vertices_642, vertices_770, vertices_28, vertices_268, vertices_84, vertices_276, vertices_324, vertices_56, vertices_280, vertices_168, vertices_552, vertices_648, vertices_776, vertices_112, vertices_560, vertices_592, vertices_784, vertices_224, vertices_672, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_651), (false, vertices_117), (false, vertices_453), (false, vertices_233), (true, vertices_266), (true, vertices_770), (true, vertices_268), (true, vertices_276), (true, vertices_280), (true, vertices_552), (true, vertices_776), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_672), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 20, 15, 17, 23, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_391) then 21 else
  if p.val = (false, vertices_651) then 14 else
  if p.val = (false, vertices_117) then 19 else
  if p.val = (false, vertices_453) then 22 else
  if p.val = (false, vertices_233) then 16 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_770) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
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
  frame := ![0, 5, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_962, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_386, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
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

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![2, 3, 4, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_824, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_824, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![3, 4, 5, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_752, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_752, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 1, 2, 3]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_270, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .fundamental ![0, 1, 2, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_270, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_778, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 2, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_266, (by decide +kernel)⟩ ⟨vertices_778, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_962, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_386, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_284, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![1, 2, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_28, (by decide +kernel)⟩ ⟨vertices_284, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_852, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![1, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_852, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_824, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![2, 3, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_824, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_680, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![2, 4, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_168, (by decide +kernel)⟩ ⟨vertices_680, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_752, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .oneRow ![3, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_752, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1197

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_one_six_1198.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1198

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_519 : Finset (Fin 10) := literalFinset [0, 1, 2, 9] (by decide +kernel)
noncomputable def vertices_651 : Finset (Fin 10) := literalFinset [0, 1, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_789 : Finset (Fin 10) := literalFinset [0, 2, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_233 : Finset (Fin 10) := literalFinset [0, 3, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_689 : Finset (Fin 10) := literalFinset [0, 4, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_398 : Finset (Fin 10) := literalFinset [1, 2, 3, 7, 8] (by decide +kernel)
noncomputable def vertices_774 : Finset (Fin 10) := literalFinset [1, 2, 8, 9] (by decide +kernel)
noncomputable def vertices_962 : Finset (Fin 10) := literalFinset [1, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_124 : Finset (Fin 10) := literalFinset [2, 3, 4, 5, 6] (by decide +kernel)
noncomputable def vertices_460 : Finset (Fin 10) := literalFinset [2, 3, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_340 : Finset (Fin 10) := literalFinset [2, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_880 : Finset (Fin 10) := literalFinset [4, 5, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_736 : Finset (Fin 10) := literalFinset [5, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_515 : Finset (Fin 10) := literalFinset [0, 1, 9] (by decide +kernel)
noncomputable def vertices_21 : Finset (Fin 10) := literalFinset [0, 2, 4] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_529 : Finset (Fin 10) := literalFinset [0, 4, 9] (by decide +kernel)
noncomputable def vertices_161 : Finset (Fin 10) := literalFinset [0, 5, 7] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_262 : Finset (Fin 10) := literalFinset [1, 2, 8] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_138 : Finset (Fin 10) := literalFinset [1, 3, 7] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_60 : Finset (Fin 10) := literalFinset [2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_76 : Finset (Fin 10) := literalFinset [2, 3, 6] (by decide +kernel)
noncomputable def vertices_396 : Finset (Fin 10) := literalFinset [2, 3, 7, 8] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_324 : Finset (Fin 10) := literalFinset [2, 6, 8] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_104 : Finset (Fin 10) := literalFinset [3, 5, 6] (by decide +kernel)
noncomputable def vertices_200 : Finset (Fin 10) := literalFinset [3, 6, 7] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_784 : Finset (Fin 10) := literalFinset [4, 8, 9] (by decide +kernel)
noncomputable def vertices_224 : Finset (Fin 10) := literalFinset [5, 6, 7] (by decide +kernel)
noncomputable def vertices_608 : Finset (Fin 10) := literalFinset [5, 6, 9] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_519, vertices_651, vertices_789, vertices_233, vertices_689, vertices_398, vertices_774, vertices_962, vertices_124, vertices_460, vertices_340, vertices_880, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_517, vertices_41, vertices_137, vertices_49, vertices_529, vertices_161, vertices_641, vertices_14, vertices_262, vertices_518, vertices_138, vertices_386, vertices_642, vertices_770, vertices_60, vertices_76, vertices_396, vertices_84, vertices_276, vertices_324, vertices_772, vertices_104, vertices_200, vertices_112, vertices_560, vertices_336, vertices_784, vertices_224, vertices_608, vertices_672, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_519), (false, vertices_651), (false, vertices_789), (false, vertices_233), (false, vertices_689), (true, vertices_262), (true, vertices_386), (true, vertices_770), (true, vertices_76), (true, vertices_396), (true, vertices_84), (true, vertices_324), (true, vertices_112), (true, vertices_336), (true, vertices_608), (true, vertices_448), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 15, 19, 21, 23, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_651) then 14 else
  if p.val = (false, vertices_789) then 17 else
  if p.val = (false, vertices_233) then 20 else
  if p.val = (false, vertices_689) then 22 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_396) then 18 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_324) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_519), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
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
  frame := ![0, 5, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_962, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_386, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 3
  frame := ![1, 2, 6]
  vertex := 7
  face := Sum.inr ⟨vertices_396, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_396, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 3
  frame := ![1, 2, 3]
  vertex := 4
  face := Sum.inr ⟨vertices_60, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![3, 4, 5, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_880, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_880, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 6, 1, 3]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_398, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_398, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_774, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 1, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_262, (by decide +kernel)⟩ ⟨vertices_774, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_962, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_386, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_124, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_124, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_460, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![1, 2, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_76, (by decide +kernel)⟩ ⟨vertices_460, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_340, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![1, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_340, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_880, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![3, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_880, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_736, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![4, 5, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_224, (by decide +kernel)⟩ ⟨vertices_736, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1198

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_one_six_1199.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1199

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_775 : Finset (Fin 10) := literalFinset [0, 1, 2, 8, 9] (by decide +kernel)
noncomputable def vertices_651 : Finset (Fin 10) := literalFinset [0, 1, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_277 : Finset (Fin 10) := literalFinset [0, 2, 4, 8] (by decide +kernel)
noncomputable def vertices_233 : Finset (Fin 10) := literalFinset [0, 3, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_689 : Finset (Fin 10) := literalFinset [0, 4, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_785 : Finset (Fin 10) := literalFinset [0, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_398 : Finset (Fin 10) := literalFinset [1, 2, 3, 7, 8] (by decide +kernel)
noncomputable def vertices_962 : Finset (Fin 10) := literalFinset [1, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_124 : Finset (Fin 10) := literalFinset [2, 3, 4, 5, 6] (by decide +kernel)
noncomputable def vertices_460 : Finset (Fin 10) := literalFinset [2, 3, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_340 : Finset (Fin 10) := literalFinset [2, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_880 : Finset (Fin 10) := literalFinset [4, 5, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_736 : Finset (Fin 10) := literalFinset [5, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_515 : Finset (Fin 10) := literalFinset [0, 1, 9] (by decide +kernel)
noncomputable def vertices_21 : Finset (Fin 10) := literalFinset [0, 2, 4] (by decide +kernel)
noncomputable def vertices_261 : Finset (Fin 10) := literalFinset [0, 2, 8] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_273 : Finset (Fin 10) := literalFinset [0, 4, 8] (by decide +kernel)
noncomputable def vertices_529 : Finset (Fin 10) := literalFinset [0, 4, 9] (by decide +kernel)
noncomputable def vertices_161 : Finset (Fin 10) := literalFinset [0, 5, 7] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_262 : Finset (Fin 10) := literalFinset [1, 2, 8] (by decide +kernel)
noncomputable def vertices_138 : Finset (Fin 10) := literalFinset [1, 3, 7] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_60 : Finset (Fin 10) := literalFinset [2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_76 : Finset (Fin 10) := literalFinset [2, 3, 6] (by decide +kernel)
noncomputable def vertices_396 : Finset (Fin 10) := literalFinset [2, 3, 7, 8] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_324 : Finset (Fin 10) := literalFinset [2, 6, 8] (by decide +kernel)
noncomputable def vertices_104 : Finset (Fin 10) := literalFinset [3, 5, 6] (by decide +kernel)
noncomputable def vertices_200 : Finset (Fin 10) := literalFinset [3, 6, 7] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_784 : Finset (Fin 10) := literalFinset [4, 8, 9] (by decide +kernel)
noncomputable def vertices_224 : Finset (Fin 10) := literalFinset [5, 6, 7] (by decide +kernel)
noncomputable def vertices_608 : Finset (Fin 10) := literalFinset [5, 6, 9] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_651, vertices_277, vertices_233, vertices_689, vertices_785, vertices_398, vertices_962, vertices_124, vertices_460, vertices_340, vertices_880, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_261, vertices_41, vertices_137, vertices_49, vertices_273, vertices_529, vertices_161, vertices_641, vertices_769, vertices_14, vertices_262, vertices_138, vertices_386, vertices_642, vertices_770, vertices_60, vertices_76, vertices_396, vertices_84, vertices_276, vertices_324, vertices_104, vertices_200, vertices_112, vertices_560, vertices_336, vertices_784, vertices_224, vertices_608, vertices_672, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_651), (false, vertices_277), (false, vertices_233), (false, vertices_689), (false, vertices_785), (true, vertices_386), (true, vertices_76), (true, vertices_396), (true, vertices_84), (true, vertices_324), (true, vertices_112), (true, vertices_336), (true, vertices_608), (true, vertices_448), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![12, 15, 18, 20, 22, 23, 24, 25, 26]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_775) then 13 else
  if p.val = (false, vertices_651) then 14 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_233) then 19 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (false, vertices_785) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_396) then 17 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_785), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
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
  frame := ![0, 5, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_962, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_386, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 3
  frame := ![1, 2, 6]
  vertex := 7
  face := Sum.inr ⟨vertices_396, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_396, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 3
  frame := ![1, 2, 3]
  vertex := 4
  face := Sum.inr ⟨vertices_60, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![3, 4, 5, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_880, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_880, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 6, 1, 3]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_398, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_398, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_962, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_386, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_124, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![1, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_124, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_460, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 2, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_76, (by decide +kernel)⟩ ⟨vertices_460, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_340, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![1, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_340, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_880, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![3, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_880, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_736, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![4, 5, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_224, (by decide +kernel)⟩ ⟨vertices_736, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1199

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_one_six_1200.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1200

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_775 : Finset (Fin 10) := literalFinset [0, 1, 2, 8, 9] (by decide +kernel)
noncomputable def vertices_651 : Finset (Fin 10) := literalFinset [0, 1, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_277 : Finset (Fin 10) := literalFinset [0, 2, 4, 8] (by decide +kernel)
noncomputable def vertices_233 : Finset (Fin 10) := literalFinset [0, 3, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_817 : Finset (Fin 10) := literalFinset [0, 4, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_673 : Finset (Fin 10) := literalFinset [0, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_398 : Finset (Fin 10) := literalFinset [1, 2, 3, 7, 8] (by decide +kernel)
noncomputable def vertices_962 : Finset (Fin 10) := literalFinset [1, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_124 : Finset (Fin 10) := literalFinset [2, 3, 4, 5, 6] (by decide +kernel)
noncomputable def vertices_460 : Finset (Fin 10) := literalFinset [2, 3, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_340 : Finset (Fin 10) := literalFinset [2, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_752 : Finset (Fin 10) := literalFinset [4, 5, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_848 : Finset (Fin 10) := literalFinset [4, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_515 : Finset (Fin 10) := literalFinset [0, 1, 9] (by decide +kernel)
noncomputable def vertices_21 : Finset (Fin 10) := literalFinset [0, 2, 4] (by decide +kernel)
noncomputable def vertices_261 : Finset (Fin 10) := literalFinset [0, 2, 8] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_273 : Finset (Fin 10) := literalFinset [0, 4, 8] (by decide +kernel)
noncomputable def vertices_161 : Finset (Fin 10) := literalFinset [0, 5, 7] (by decide +kernel)
noncomputable def vertices_545 : Finset (Fin 10) := literalFinset [0, 5, 9] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_262 : Finset (Fin 10) := literalFinset [1, 2, 8] (by decide +kernel)
noncomputable def vertices_138 : Finset (Fin 10) := literalFinset [1, 3, 7] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_60 : Finset (Fin 10) := literalFinset [2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_76 : Finset (Fin 10) := literalFinset [2, 3, 6] (by decide +kernel)
noncomputable def vertices_396 : Finset (Fin 10) := literalFinset [2, 3, 7, 8] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_324 : Finset (Fin 10) := literalFinset [2, 6, 8] (by decide +kernel)
noncomputable def vertices_104 : Finset (Fin 10) := literalFinset [3, 5, 6] (by decide +kernel)
noncomputable def vertices_200 : Finset (Fin 10) := literalFinset [3, 6, 7] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_784 : Finset (Fin 10) := literalFinset [4, 8, 9] (by decide +kernel)
noncomputable def vertices_224 : Finset (Fin 10) := literalFinset [5, 6, 7] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_651, vertices_277, vertices_233, vertices_817, vertices_673, vertices_398, vertices_962, vertices_124, vertices_460, vertices_340, vertices_752, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_21, vertices_261, vertices_41, vertices_137, vertices_49, vertices_273, vertices_161, vertices_545, vertices_641, vertices_769, vertices_14, vertices_262, vertices_138, vertices_386, vertices_642, vertices_770, vertices_60, vertices_76, vertices_396, vertices_84, vertices_276, vertices_324, vertices_104, vertices_200, vertices_112, vertices_560, vertices_336, vertices_592, vertices_784, vertices_224, vertices_672, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_651), (false, vertices_277), (false, vertices_233), (false, vertices_817), (false, vertices_673), (true, vertices_386), (true, vertices_76), (true, vertices_396), (true, vertices_84), (true, vertices_324), (true, vertices_112), (true, vertices_336), (true, vertices_592), (true, vertices_448), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![12, 15, 18, 20, 22, 23, 24, 25, 26]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_775) then 13 else
  if p.val = (false, vertices_651) then 14 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_233) then 19 else
  if p.val = (false, vertices_817) then 21 else
  if p.val = (false, vertices_673) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_396) then 17 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_673), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
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
  frame := ![0, 5, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_962, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_386, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 3
  frame := ![1, 2, 6]
  vertex := 7
  face := Sum.inr ⟨vertices_396, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_396, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 3
  frame := ![1, 2, 3]
  vertex := 4
  face := Sum.inr ⟨vertices_60, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![3, 4, 5, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_752, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_752, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 7, 1, 3]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_398, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_398, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_962, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_386, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_124, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![1, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_124, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_460, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 2, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_76, (by decide +kernel)⟩ ⟨vertices_460, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_340, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![1, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_340, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_752, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![3, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_752, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_848, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![3, 5, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_336, (by decide +kernel)⟩ ⟨vertices_848, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1200

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_one_six_1201.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1201

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_775 : Finset (Fin 10) := literalFinset [0, 1, 2, 8, 9] (by decide +kernel)
noncomputable def vertices_395 : Finset (Fin 10) := literalFinset [0, 1, 3, 7, 8] (by decide +kernel)
noncomputable def vertices_341 : Finset (Fin 10) := literalFinset [0, 2, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_121 : Finset (Fin 10) := literalFinset [0, 3, 4, 5, 6] (by decide +kernel)
noncomputable def vertices_457 : Finset (Fin 10) := literalFinset [0, 3, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_654 : Finset (Fin 10) := literalFinset [1, 2, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_962 : Finset (Fin 10) := literalFinset [1, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_556 : Finset (Fin 10) := literalFinset [2, 3, 5, 9] (by decide +kernel)
noncomputable def vertices_820 : Finset (Fin 10) := literalFinset [2, 4, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_232 : Finset (Fin 10) := literalFinset [3, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_680 : Finset (Fin 10) := literalFinset [3, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_752 : Finset (Fin 10) := literalFinset [4, 5, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_848 : Finset (Fin 10) := literalFinset [4, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_259 : Finset (Fin 10) := literalFinset [0, 1, 8] (by decide +kernel)
noncomputable def vertices_21 : Finset (Fin 10) := literalFinset [0, 2, 4] (by decide +kernel)
noncomputable def vertices_261 : Finset (Fin 10) := literalFinset [0, 2, 8] (by decide +kernel)
noncomputable def vertices_57 : Finset (Fin 10) := literalFinset [0, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_73 : Finset (Fin 10) := literalFinset [0, 3, 6] (by decide +kernel)
noncomputable def vertices_393 : Finset (Fin 10) := literalFinset [0, 3, 7, 8] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_138 : Finset (Fin 10) := literalFinset [1, 3, 7] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_548 : Finset (Fin 10) := literalFinset [2, 5, 9] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_104 : Finset (Fin 10) := literalFinset [3, 5, 6] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_552 : Finset (Fin 10) := literalFinset [3, 5, 9] (by decide +kernel)
noncomputable def vertices_200 : Finset (Fin 10) := literalFinset [3, 6, 7] (by decide +kernel)
noncomputable def vertices_648 : Finset (Fin 10) := literalFinset [3, 7, 9] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_784 : Finset (Fin 10) := literalFinset [4, 8, 9] (by decide +kernel)
noncomputable def vertices_224 : Finset (Fin 10) := literalFinset [5, 6, 7] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_395, vertices_341, vertices_121, vertices_457, vertices_654, vertices_962, vertices_556, vertices_820, vertices_232, vertices_680, vertices_752, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_393, vertices_81, vertices_321, vertices_14, vertices_518, vertices_138, vertices_386, vertices_642, vertices_770, vertices_44, vertices_524, vertices_52, vertices_276, vertices_548, vertices_772, vertices_104, vertices_168, vertices_552, vertices_200, vertices_648, vertices_112, vertices_560, vertices_336, vertices_592, vertices_784, vertices_224, vertices_672, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_395), (false, vertices_341), (false, vertices_121), (false, vertices_457), (true, vertices_642), (true, vertices_524), (true, vertices_548), (true, vertices_168), (true, vertices_552), (true, vertices_648), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_224), (true, vertices_672), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 15, 20, 17, 23, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_775) then 14 else
  if p.val = (false, vertices_395) then 21 else
  if p.val = (false, vertices_341) then 16 else
  if p.val = (false, vertices_121) then 19 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (true, vertices_642) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_168) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
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
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_386, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
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
  frame := ![3, 4, 5, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_752, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_752, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![2, 0, 1, 3]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_654, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_654, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_962, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_386, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_556, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![1, 2, 4, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_556, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_820, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 3, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_820, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_232, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![2, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_104, (by decide +kernel)⟩ ⟨vertices_232, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_680, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![2, 4, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_168, (by decide +kernel)⟩ ⟨vertices_680, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_752, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![3, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_752, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1201

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_one_six_1213.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1213

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_647 : Finset (Fin 10) := literalFinset [0, 1, 2, 7, 9] (by decide +kernel)
noncomputable def vertices_587 : Finset (Fin 10) := literalFinset [0, 1, 3, 6, 9] (by decide +kernel)
noncomputable def vertices_181 : Finset (Fin 10) := literalFinset [0, 2, 4, 5, 7] (by decide +kernel)
noncomputable def vertices_233 : Finset (Fin 10) := literalFinset [0, 3, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_961 : Finset (Fin 10) := literalFinset [0, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_94 : Finset (Fin 10) := literalFinset [1, 2, 3, 4, 6] (by decide +kernel)
noncomputable def vertices_838 : Finset (Fin 10) := literalFinset [1, 2, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_340 : Finset (Fin 10) := literalFinset [2, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_916 : Finset (Fin 10) := literalFinset [2, 4, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_120 : Finset (Fin 10) := literalFinset [3, 4, 5, 6] (by decide +kernel)
noncomputable def vertices_496 : Finset (Fin 10) := literalFinset [4, 5, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_515 : Finset (Fin 10) := literalFinset [0, 1, 9] (by decide +kernel)
noncomputable def vertices_53 : Finset (Fin 10) := literalFinset [0, 2, 4, 5] (by decide +kernel)
noncomputable def vertices_133 : Finset (Fin 10) := literalFinset [0, 2, 7] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_73 : Finset (Fin 10) := literalFinset [0, 3, 6] (by decide +kernel)
noncomputable def vertices_161 : Finset (Fin 10) := literalFinset [0, 5, 7] (by decide +kernel)
noncomputable def vertices_193 : Finset (Fin 10) := literalFinset [0, 6, 7] (by decide +kernel)
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
noncomputable def vertices_104 : Finset (Fin 10) := literalFinset [3, 5, 6] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_224 : Finset (Fin 10) := literalFinset [5, 6, 7] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_587, vertices_181, vertices_233, vertices_961, vertices_94, vertices_838, vertices_340, vertices_916, vertices_120, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_515, vertices_53, vertices_133, vertices_41, vertices_73, vertices_161, vertices_193, vertices_577, vertices_641, vertices_30, vertices_70, vertices_518, vertices_74, vertices_578, vertices_84, vertices_148, vertices_276, vertices_324, vertices_644, vertices_772, vertices_56, vertices_88, vertices_104, vertices_112, vertices_176, vertices_336, vertices_400, vertices_224, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_587), (false, vertices_181), (false, vertices_233), (false, vertices_961), (true, vertices_70), (true, vertices_84), (true, vertices_276), (true, vertices_324), (true, vertices_772), (true, vertices_88), (true, vertices_112), (true, vertices_336), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![9, 12, 15, 17, 18, 19, 21, 22, 23]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_647) then 10 else
  if p.val = (false, vertices_587) then 11 else
  if p.val = (false, vertices_181) then 14 else
  if p.val = (false, vertices_233) then 16 else
  if p.val = (false, vertices_961) then 20 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_324) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_88) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_400) then 8 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 17 => Sum.inl 3
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
  frame := ![0, 1, 2]
  vertex := 3
  face := Sum.inr ⟨vertices_30, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_30, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
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
  frame := ![3, 4, 5, 6]
  vertex := 7
  face := Sum.inl ⟨vertices_496, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_496, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![2, 0, 1, 3]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_94, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_30, (by decide +kernel)⟩ ⟨vertices_94, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_838, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_70, (by decide +kernel)⟩ ⟨vertices_838, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_340, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![1, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_340, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_916, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 3, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_148, (by decide +kernel)⟩ ⟨vertices_916, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_120, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![2, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_120, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_496, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![3, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_496, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1213

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_one_six_1231.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1231

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_199 : Finset (Fin 10) := literalFinset [0, 1, 2, 6, 7] (by decide +kernel)
noncomputable def vertices_523 : Finset (Fin 10) := literalFinset [0, 1, 3, 9] (by decide +kernel)
noncomputable def vertices_835 : Finset (Fin 10) := literalFinset [0, 1, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_181 : Finset (Fin 10) := literalFinset [0, 2, 4, 5, 7] (by decide +kernel)
noncomputable def vertices_809 : Finset (Fin 10) := literalFinset [0, 3, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_481 : Finset (Fin 10) := literalFinset [0, 5, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_94 : Finset (Fin 10) := literalFinset [1, 2, 3, 4, 6] (by decide +kernel)
noncomputable def vertices_586 : Finset (Fin 10) := literalFinset [1, 3, 6, 9] (by decide +kernel)
noncomputable def vertices_468 : Finset (Fin 10) := literalFinset [2, 4, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_440 : Finset (Fin 10) := literalFinset [3, 4, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_856 : Finset (Fin 10) := literalFinset [3, 4, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_67 : Finset (Fin 10) := literalFinset [0, 1, 6] (by decide +kernel)
noncomputable def vertices_515 : Finset (Fin 10) := literalFinset [0, 1, 9] (by decide +kernel)
noncomputable def vertices_53 : Finset (Fin 10) := literalFinset [0, 2, 4, 5] (by decide +kernel)
noncomputable def vertices_133 : Finset (Fin 10) := literalFinset [0, 2, 7] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_521 : Finset (Fin 10) := literalFinset [0, 3, 9] (by decide +kernel)
noncomputable def vertices_161 : Finset (Fin 10) := literalFinset [0, 5, 7] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_193 : Finset (Fin 10) := literalFinset [0, 6, 7] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_30 : Finset (Fin 10) := literalFinset [1, 2, 3, 4] (by decide +kernel)
noncomputable def vertices_70 : Finset (Fin 10) := literalFinset [1, 2, 6] (by decide +kernel)
noncomputable def vertices_74 : Finset (Fin 10) := literalFinset [1, 3, 6] (by decide +kernel)
noncomputable def vertices_522 : Finset (Fin 10) := literalFinset [1, 3, 9] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_148 : Finset (Fin 10) := literalFinset [2, 4, 7] (by decide +kernel)
noncomputable def vertices_196 : Finset (Fin 10) := literalFinset [2, 6, 7] (by decide +kernel)
noncomputable def vertices_56 : Finset (Fin 10) := literalFinset [3, 4, 5] (by decide +kernel)
noncomputable def vertices_88 : Finset (Fin 10) := literalFinset [3, 4, 6] (by decide +kernel)
noncomputable def vertices_280 : Finset (Fin 10) := literalFinset [3, 4, 8] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_584 : Finset (Fin 10) := literalFinset [3, 6, 9] (by decide +kernel)
noncomputable def vertices_776 : Finset (Fin 10) := literalFinset [3, 8, 9] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_523, vertices_835, vertices_181, vertices_809, vertices_481, vertices_94, vertices_586, vertices_468, vertices_440, vertices_856] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_515, vertices_53, vertices_133, vertices_41, vertices_521, vertices_161, vertices_289, vertices_193, vertices_321, vertices_769, vertices_30, vertices_70, vertices_74, vertices_522, vertices_578, vertices_84, vertices_148, vertices_196, vertices_56, vertices_88, vertices_280, vertices_296, vertices_584, vertices_776, vertices_176, vertices_336, vertices_400, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_523), (false, vertices_835), (false, vertices_181), (false, vertices_809), (false, vertices_481), (true, vertices_74), (true, vertices_84), (true, vertices_88), (true, vertices_280), (true, vertices_584), (true, vertices_336), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![8, 11, 14, 16, 17, 19, 20, 21, 22]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_199) then 9 else
  if p.val = (false, vertices_523) then 0 else
  if p.val = (false, vertices_835) then 10 else
  if p.val = (false, vertices_181) then 13 else
  if p.val = (false, vertices_809) then 15 else
  if p.val = (false, vertices_481) then 18 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_88) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_336) then 6 else
  if p.val = (true, vertices_400) then 7 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_523), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inl 4
  | 18 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
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
  frame := ![0, 1, 2]
  vertex := 3
  face := Sum.inr ⟨vertices_30, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_30, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 3, 5, 6]
  vertex := 7
  face := Sum.inl ⟨vertices_468, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_468, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
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
  frame := ![2, 3, 5, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_856, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_88, (by decide +kernel)⟩ ⟨vertices_856, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 1, 4, 2]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_94, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_30, (by decide +kernel)⟩ ⟨vertices_94, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_586, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 2, 5, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_74, (by decide +kernel)⟩ ⟨vertices_586, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_468, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![1, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_468, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_440, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![2, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_440, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_856, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![2, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_88, (by decide +kernel)⟩ ⟨vertices_856, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1231

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_one_six_1232.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1232

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_63 : Finset (Fin 10) := literalFinset [0, 1, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_647 : Finset (Fin 10) := literalFinset [0, 1, 2, 7, 9] (by decide +kernel)
noncomputable def vertices_91 : Finset (Fin 10) := literalFinset [0, 1, 3, 4, 6] (by decide +kernel)
noncomputable def vertices_195 : Finset (Fin 10) := literalFinset [0, 1, 6, 7] (by decide +kernel)
noncomputable def vertices_805 : Finset (Fin 10) := literalFinset [0, 2, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_369 : Finset (Fin 10) := literalFinset [0, 4, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_961 : Finset (Fin 10) := literalFinset [0, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_206 : Finset (Fin 10) := literalFinset [1, 2, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_188 : Finset (Fin 10) := literalFinset [2, 3, 4, 5, 7] (by decide +kernel)
noncomputable def vertices_676 : Finset (Fin 10) := literalFinset [2, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_472 : Finset (Fin 10) := literalFinset [3, 4, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_944 : Finset (Fin 10) := literalFinset [4, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_7 : Finset (Fin 10) := literalFinset [0, 1, 2] (by decide +kernel)
noncomputable def vertices_27 : Finset (Fin 10) := literalFinset [0, 1, 3, 4] (by decide +kernel)
noncomputable def vertices_67 : Finset (Fin 10) := literalFinset [0, 1, 6] (by decide +kernel)
noncomputable def vertices_131 : Finset (Fin 10) := literalFinset [0, 1, 7] (by decide +kernel)
noncomputable def vertices_37 : Finset (Fin 10) := literalFinset [0, 2, 5] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_193 : Finset (Fin 10) := literalFinset [0, 6, 7] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_134 : Finset (Fin 10) := literalFinset [1, 2, 7] (by decide +kernel)
noncomputable def vertices_74 : Finset (Fin 10) := literalFinset [1, 3, 6] (by decide +kernel)
noncomputable def vertices_194 : Finset (Fin 10) := literalFinset [1, 6, 7] (by decide +kernel)
noncomputable def vertices_60 : Finset (Fin 10) := literalFinset [2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_140 : Finset (Fin 10) := literalFinset [2, 3, 7] (by decide +kernel)
noncomputable def vertices_164 : Finset (Fin 10) := literalFinset [2, 5, 7] (by decide +kernel)
noncomputable def vertices_548 : Finset (Fin 10) := literalFinset [2, 5, 9] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_88 : Finset (Fin 10) := literalFinset [3, 4, 6] (by decide +kernel)
noncomputable def vertices_152 : Finset (Fin 10) := literalFinset [3, 4, 7] (by decide +kernel)
noncomputable def vertices_200 : Finset (Fin 10) := literalFinset [3, 6, 7] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_195, vertices_805, vertices_369, vertices_961, vertices_206, vertices_188, vertices_676, vertices_472, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_517, vertices_49, vertices_81, vertices_289, vertices_193, vertices_321, vertices_641, vertices_769, vertices_14, vertices_134, vertices_74, vertices_194, vertices_60, vertices_140, vertices_164, vertices_548, vertices_644, vertices_88, vertices_152, vertices_200, vertices_176, vertices_304, vertices_336, vertices_400, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_195), (false, vertices_805), (false, vertices_369), (false, vertices_961), (true, vertices_140), (true, vertices_164), (true, vertices_152), (true, vertices_200), (true, vertices_176), (true, vertices_400), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![8, 11, 14, 15, 17, 18, 20, 21, 22]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_647) then 9 else
  if p.val = (false, vertices_91) then 10 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_805) then 13 else
  if p.val = (false, vertices_369) then 16 else
  if p.val = (false, vertices_961) then 19 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_152) then 3 else
  if p.val = (true, vertices_200) then 4 else
  if p.val = (true, vertices_176) then 5 else
  if p.val = (true, vertices_400) then 6 else
  if p.val = (true, vertices_672) then 7 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 17 => Sum.inl 4
  | 18 => Sum.inl 5
  | 19 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
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
  frame := ![0, 1, 2, 5]
  vertex := 6
  face := Sum.inl ⟨vertices_206, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_206, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 3
  frame := ![1, 2, 3]
  vertex := 4
  face := Sum.inr ⟨vertices_60, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
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

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_206, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_206, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_188, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![1, 2, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_60, (by decide +kernel)⟩ ⟨vertices_188, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_676, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![1, 4, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_164, (by decide +kernel)⟩ ⟨vertices_676, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_472, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![2, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_88, (by decide +kernel)⟩ ⟨vertices_472, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_944, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![3, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_176, (by decide +kernel)⟩ ⟨vertices_944, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1232

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_1410 : Certifies 1410 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1161.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1411 : Certifies 1411 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1162.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1412 : Certifies 1412 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1163.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1413 : Certifies 1413 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1164.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1414 : Certifies 1414 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1165.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1415 : Certifies 1415 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1166.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1416 : Certifies 1416 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1167.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1417 : Certifies 1417 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1168.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1418 : Certifies 1418 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1169.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1419 : Certifies 1419 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1170.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1420 : Certifies 1420 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1171.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1421 : Certifies 1421 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1172.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1422 : Certifies 1422 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1173.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1423 : Certifies 1423 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1174.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1424 : Certifies 1424 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1175.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1425 : Certifies 1425 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1176.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1426 : Certifies 1426 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1177.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1427 : Certifies 1427 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1178.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1428 : Certifies 1428 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1179.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1429 : Certifies 1429 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1180.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1430 : Certifies 1430 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1181.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1431 : Certifies 1431 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1196.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1432 : Certifies 1432 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1197.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1433 : Certifies 1433 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1198.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1434 : Certifies 1434 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1199.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1435 : Certifies 1435 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1200.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1436 : Certifies 1436 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1201.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1437 : Certifies 1437 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1213.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1438 : Certifies 1438 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1231.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1439 : Certifies 1439 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1232.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B047 (j : Fin 30) :
    Certifies (1410 + j.val) := by
  fin_cases j
  · exact projection_1410
  · exact projection_1411
  · exact projection_1412
  · exact projection_1413
  · exact projection_1414
  · exact projection_1415
  · exact projection_1416
  · exact projection_1417
  · exact projection_1418
  · exact projection_1419
  · exact projection_1420
  · exact projection_1421
  · exact projection_1422
  · exact projection_1423
  · exact projection_1424
  · exact projection_1425
  · exact projection_1426
  · exact projection_1427
  · exact projection_1428
  · exact projection_1429
  · exact projection_1430
  · exact projection_1431
  · exact projection_1432
  · exact projection_1433
  · exact projection_1434
  · exact projection_1435
  · exact projection_1436
  · exact projection_1437
  · exact projection_1438
  · exact projection_1439

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
