module
public import TerminalGeometry
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Papers.FiniteProjectionChecks

section
set_option debug.skipKernelTC false

section BundlePart0
/- Source: ProjectionCertificates/R_m14e10q0_0009.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0009

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_295 : Finset (Fin 10) := literalFinset [0, 1, 2, 5, 8] (by decide +kernel)
noncomputable def vertices_555 : Finset (Fin 10) := literalFinset [0, 1, 3, 5, 9] (by decide +kernel)
noncomputable def vertices_331 : Finset (Fin 10) := literalFinset [0, 1, 3, 6, 8] (by decide +kernel)
noncomputable def vertices_213 : Finset (Fin 10) := literalFinset [0, 2, 4, 6, 7] (by decide +kernel)
noncomputable def vertices_677 : Finset (Fin 10) := literalFinset [0, 2, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_325 : Finset (Fin 10) := literalFinset [0, 2, 6, 8] (by decide +kernel)
noncomputable def vertices_713 : Finset (Fin 10) := literalFinset [0, 3, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_794 : Finset (Fin 10) := literalFinset [1, 3, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_802 : Finset (Fin 10) := literalFinset [1, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_348 : Finset (Fin 10) := literalFinset [2, 3, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_436 : Finset (Fin 10) := literalFinset [2, 4, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_600 : Finset (Fin 10) := literalFinset [3, 4, 6, 9] (by decide +kernel)
noncomputable def vertices_752 : Finset (Fin 10) := literalFinset [4, 5, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_816 : Finset (Fin 10) := literalFinset [4, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_35 : Finset (Fin 10) := literalFinset [0, 1, 5] (by decide +kernel)
noncomputable def vertices_259 : Finset (Fin 10) := literalFinset [0, 1, 8] (by decide +kernel)
noncomputable def vertices_37 : Finset (Fin 10) := literalFinset [0, 2, 5] (by decide +kernel)
noncomputable def vertices_69 : Finset (Fin 10) := literalFinset [0, 2, 6] (by decide +kernel)
noncomputable def vertices_133 : Finset (Fin 10) := literalFinset [0, 2, 7] (by decide +kernel)
noncomputable def vertices_261 : Finset (Fin 10) := literalFinset [0, 2, 8] (by decide +kernel)
noncomputable def vertices_73 : Finset (Fin 10) := literalFinset [0, 3, 6] (by decide +kernel)
noncomputable def vertices_521 : Finset (Fin 10) := literalFinset [0, 3, 9] (by decide +kernel)
noncomputable def vertices_545 : Finset (Fin 10) := literalFinset [0, 5, 9] (by decide +kernel)
noncomputable def vertices_193 : Finset (Fin 10) := literalFinset [0, 6, 7] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_522 : Finset (Fin 10) := literalFinset [1, 3, 9] (by decide +kernel)
noncomputable def vertices_290 : Finset (Fin 10) := literalFinset [1, 5, 8] (by decide +kernel)
noncomputable def vertices_546 : Finset (Fin 10) := literalFinset [1, 5, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_148 : Finset (Fin 10) := literalFinset [2, 4, 7] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_164 : Finset (Fin 10) := literalFinset [2, 5, 7] (by decide +kernel)
noncomputable def vertices_292 : Finset (Fin 10) := literalFinset [2, 5, 8] (by decide +kernel)
noncomputable def vertices_324 : Finset (Fin 10) := literalFinset [2, 6, 8] (by decide +kernel)
noncomputable def vertices_88 : Finset (Fin 10) := literalFinset [3, 4, 6] (by decide +kernel)
noncomputable def vertices_280 : Finset (Fin 10) := literalFinset [3, 4, 8] (by decide +kernel)
noncomputable def vertices_536 : Finset (Fin 10) := literalFinset [3, 4, 9] (by decide +kernel)
noncomputable def vertices_328 : Finset (Fin 10) := literalFinset [3, 6, 8] (by decide +kernel)
noncomputable def vertices_584 : Finset (Fin 10) := literalFinset [3, 6, 9] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_208 : Finset (Fin 10) := literalFinset [4, 6, 7] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_784 : Finset (Fin 10) := literalFinset [4, 8, 9] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_555, vertices_331, vertices_213, vertices_677, vertices_325, vertices_713, vertices_794, vertices_802, vertices_348, vertices_436, vertices_600, vertices_752, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_259, vertices_37, vertices_69, vertices_133, vertices_261, vertices_73, vertices_521, vertices_545, vertices_193, vertices_321, vertices_641, vertices_266, vertices_522, vertices_290, vertices_546, vertices_770, vertices_84, vertices_148, vertices_276, vertices_164, vertices_292, vertices_324, vertices_88, vertices_280, vertices_536, vertices_328, vertices_584, vertices_176, vertices_304, vertices_560, vertices_208, vertices_592, vertices_784, vertices_672, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_555), (false, vertices_331), (false, vertices_213), (false, vertices_677), (false, vertices_325), (false, vertices_713), (true, vertices_770), (true, vertices_276), (true, vertices_88), (true, vertices_280), (true, vertices_536), (true, vertices_176), (true, vertices_304), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![12, 16, 19, 21, 22, 23, 24, 25, 26]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 13 else
  if p.val = (false, vertices_555) then 14 else
  if p.val = (false, vertices_331) then 15 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_325) then 0 else
  if p.val = (false, vertices_713) then 20 else
  if p.val = (true, vertices_770) then 1 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_88) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_325), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 21 => Sum.inl 3
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
  frame := ![0, 2, 3, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_794, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_266, (by decide +kernel)⟩ ⟨vertices_794, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 3, 5]
  vertex := 7
  face := Sum.inl ⟨vertices_348, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_348, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 3, 4, 6]
  vertex := 7
  face := Sum.inl ⟨vertices_436, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_148, (by decide +kernel)⟩ ⟨vertices_436, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
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
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_176, (by decide +kernel)⟩ ⟨vertices_752, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 2, 1, 3]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_794, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 2, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_266, (by decide +kernel)⟩ ⟨vertices_794, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_802, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 4, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_290, (by decide +kernel)⟩ ⟨vertices_802, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_348, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![1, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_348, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_436, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_148, (by decide +kernel)⟩ ⟨vertices_436, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_600, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![2, 3, 5, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_88, (by decide +kernel)⟩ ⟨vertices_600, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_752, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![3, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_176, (by decide +kernel)⟩ ⟨vertices_752, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_816, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![3, 4, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_304, (by decide +kernel)⟩ ⟨vertices_816, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0009

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m14e10q0_0011.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0011

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_307 : Finset (Fin 10) := literalFinset [0, 1, 4, 5, 8] (by decide +kernel)
noncomputable def vertices_659 : Finset (Fin 10) := literalFinset [0, 1, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_611 : Finset (Fin 10) := literalFinset [0, 1, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_709 : Finset (Fin 10) := literalFinset [0, 2, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_409 : Finset (Fin 10) := literalFinset [0, 3, 4, 7, 8] (by decide +kernel)
noncomputable def vertices_481 : Finset (Fin 10) := literalFinset [0, 5, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_558 : Finset (Fin 10) := literalFinset [1, 2, 3, 5, 9] (by decide +kernel)
noncomputable def vertices_282 : Finset (Fin 10) := literalFinset [1, 3, 4, 8] (by decide +kernel)
noncomputable def vertices_538 : Finset (Fin 10) := literalFinset [1, 3, 4, 9] (by decide +kernel)
noncomputable def vertices_298 : Finset (Fin 10) := literalFinset [1, 3, 5, 8] (by decide +kernel)
noncomputable def vertices_668 : Finset (Fin 10) := literalFinset [2, 3, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_300 : Finset (Fin 10) := literalFinset [2, 3, 5, 8] (by decide +kernel)
noncomputable def vertices_460 : Finset (Fin 10) := literalFinset [2, 3, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_868 : Finset (Fin 10) := literalFinset [2, 5, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_19 : Finset (Fin 10) := literalFinset [0, 1, 4] (by decide +kernel)
noncomputable def vertices_35 : Finset (Fin 10) := literalFinset [0, 1, 5] (by decide +kernel)
noncomputable def vertices_515 : Finset (Fin 10) := literalFinset [0, 1, 9] (by decide +kernel)
noncomputable def vertices_145 : Finset (Fin 10) := literalFinset [0, 4, 7] (by decide +kernel)
noncomputable def vertices_273 : Finset (Fin 10) := literalFinset [0, 4, 8] (by decide +kernel)
noncomputable def vertices_97 : Finset (Fin 10) := literalFinset [0, 5, 6] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_193 : Finset (Fin 10) := literalFinset [0, 6, 7] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_385 : Finset (Fin 10) := literalFinset [0, 7, 8] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_26 : Finset (Fin 10) := literalFinset [1, 3, 4] (by decide +kernel)
noncomputable def vertices_42 : Finset (Fin 10) := literalFinset [1, 3, 5] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_522 : Finset (Fin 10) := literalFinset [1, 3, 9] (by decide +kernel)
noncomputable def vertices_274 : Finset (Fin 10) := literalFinset [1, 4, 8] (by decide +kernel)
noncomputable def vertices_530 : Finset (Fin 10) := literalFinset [1, 4, 9] (by decide +kernel)
noncomputable def vertices_290 : Finset (Fin 10) := literalFinset [1, 5, 8] (by decide +kernel)
noncomputable def vertices_546 : Finset (Fin 10) := literalFinset [1, 5, 9] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_140 : Finset (Fin 10) := literalFinset [2, 3, 7] (by decide +kernel)
noncomputable def vertices_268 : Finset (Fin 10) := literalFinset [2, 3, 8] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_292 : Finset (Fin 10) := literalFinset [2, 5, 8] (by decide +kernel)
noncomputable def vertices_548 : Finset (Fin 10) := literalFinset [2, 5, 9] (by decide +kernel)
noncomputable def vertices_196 : Finset (Fin 10) := literalFinset [2, 6, 7] (by decide +kernel)
noncomputable def vertices_324 : Finset (Fin 10) := literalFinset [2, 6, 8] (by decide +kernel)
noncomputable def vertices_580 : Finset (Fin 10) := literalFinset [2, 6, 9] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_152 : Finset (Fin 10) := literalFinset [3, 4, 7] (by decide +kernel)
noncomputable def vertices_280 : Finset (Fin 10) := literalFinset [3, 4, 8] (by decide +kernel)
noncomputable def vertices_536 : Finset (Fin 10) := literalFinset [3, 4, 9] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_392 : Finset (Fin 10) := literalFinset [3, 7, 8] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_608 : Finset (Fin 10) := literalFinset [5, 6, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_659, vertices_611, vertices_709, vertices_409, vertices_481, vertices_558, vertices_282, vertices_538, vertices_298, vertices_668, vertices_300, vertices_460, vertices_868] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_515, vertices_145, vertices_273, vertices_97, vertices_289, vertices_193, vertices_577, vertices_385, vertices_641, vertices_26, vertices_42, vertices_266, vertices_522, vertices_274, vertices_530, vertices_290, vertices_546, vertices_44, vertices_140, vertices_268, vertices_524, vertices_292, vertices_548, vertices_196, vertices_324, vertices_580, vertices_644, vertices_152, vertices_280, vertices_536, vertices_296, vertices_392, vertices_656, vertices_352, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_659), (false, vertices_611), (false, vertices_709), (false, vertices_409), (false, vertices_481), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_44), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_292), (true, vertices_548), (true, vertices_324), (true, vertices_536), (true, vertices_296)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 17, 19, 21, 22, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 14 else
  if p.val = (false, vertices_659) then 15 else
  if p.val = (false, vertices_611) then 16 else
  if p.val = (false, vertices_709) then 18 else
  if p.val = (false, vertices_409) then 20 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_296) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
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
  frame := ![0, 1, 2, 4]
  vertex := 8
  face := Sum.inl ⟨vertices_558, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_42, (by decide +kernel)⟩ ⟨vertices_558, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 3, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_668, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_140, (by decide +kernel)⟩ ⟨vertices_668, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 5, 6]
  vertex := 7
  face := Sum.inl ⟨vertices_460, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_140, (by decide +kernel)⟩ ⟨vertices_460, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 4, 5, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_868, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_292, (by decide +kernel)⟩ ⟨vertices_868, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 3, 2, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_558, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_42, (by decide +kernel)⟩ ⟨vertices_558, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_282, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 2, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_26, (by decide +kernel)⟩ ⟨vertices_282, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_538, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 2, 3, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_26, (by decide +kernel)⟩ ⟨vertices_538, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_298, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 2, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_42, (by decide +kernel)⟩ ⟨vertices_298, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_668, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![1, 2, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_140, (by decide +kernel)⟩ ⟨vertices_668, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_300, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![1, 2, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_300, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_460, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![1, 2, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_140, (by decide +kernel)⟩ ⟨vertices_460, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_868, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .oneRow ![1, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_292, (by decide +kernel)⟩ ⟨vertices_868, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0011

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m14e10q0_0012.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0012

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_675 : Finset (Fin 10) := literalFinset [0, 1, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_93 : Finset (Fin 10) := literalFinset [0, 2, 3, 4, 6] (by decide +kernel)
noncomputable def vertices_653 : Finset (Fin 10) := literalFinset [0, 2, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_613 : Finset (Fin 10) := literalFinset [0, 2, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_185 : Finset (Fin 10) := literalFinset [0, 3, 4, 5, 7] (by decide +kernel)
noncomputable def vertices_369 : Finset (Fin 10) := literalFinset [0, 4, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_782 : Finset (Fin 10) := literalFinset [1, 2, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_410 : Finset (Fin 10) := literalFinset [1, 3, 4, 7, 8] (by decide +kernel)
noncomputable def vertices_650 : Finset (Fin 10) := literalFinset [1, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_866 : Finset (Fin 10) := literalFinset [1, 5, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_418 : Finset (Fin 10) := literalFinset [1, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_284 : Finset (Fin 10) := literalFinset [2, 3, 4, 8] (by decide +kernel)
noncomputable def vertices_852 : Finset (Fin 10) := literalFinset [2, 4, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_432 : Finset (Fin 10) := literalFinset [4, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_13 : Finset (Fin 10) := literalFinset [0, 2, 3] (by decide +kernel)
noncomputable def vertices_69 : Finset (Fin 10) := literalFinset [0, 2, 6] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_25 : Finset (Fin 10) := literalFinset [0, 3, 4] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_97 : Finset (Fin 10) := literalFinset [0, 5, 6] (by decide +kernel)
noncomputable def vertices_161 : Finset (Fin 10) := literalFinset [0, 5, 7] (by decide +kernel)
noncomputable def vertices_545 : Finset (Fin 10) := literalFinset [0, 5, 9] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_138 : Finset (Fin 10) := literalFinset [1, 3, 7] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_522 : Finset (Fin 10) := literalFinset [1, 3, 9] (by decide +kernel)
noncomputable def vertices_162 : Finset (Fin 10) := literalFinset [1, 5, 7] (by decide +kernel)
noncomputable def vertices_290 : Finset (Fin 10) := literalFinset [1, 5, 8] (by decide +kernel)
noncomputable def vertices_546 : Finset (Fin 10) := literalFinset [1, 5, 9] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_28 : Finset (Fin 10) := literalFinset [2, 3, 4] (by decide +kernel)
noncomputable def vertices_268 : Finset (Fin 10) := literalFinset [2, 3, 8] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_580 : Finset (Fin 10) := literalFinset [2, 6, 9] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_152 : Finset (Fin 10) := literalFinset [3, 4, 7] (by decide +kernel)
noncomputable def vertices_280 : Finset (Fin 10) := literalFinset [3, 4, 8] (by decide +kernel)
noncomputable def vertices_648 : Finset (Fin 10) := literalFinset [3, 7, 9] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_608 : Finset (Fin 10) := literalFinset [5, 6, 9] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_93, vertices_653, vertices_613, vertices_185, vertices_369, vertices_782, vertices_410, vertices_650, vertices_866, vertices_418, vertices_284, vertices_852, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_517, vertices_25, vertices_137, vertices_49, vertices_81, vertices_97, vertices_161, vertices_545, vertices_641, vertices_138, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_28, vertices_268, vertices_524, vertices_84, vertices_276, vertices_580, vertices_772, vertices_152, vertices_280, vertices_648, vertices_176, vertices_304, vertices_336, vertices_400, vertices_352, vertices_608, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_93), (false, vertices_653), (false, vertices_613), (false, vertices_185), (false, vertices_369), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_290), (true, vertices_386), (true, vertices_770), (true, vertices_268), (true, vertices_276), (true, vertices_772), (true, vertices_280), (true, vertices_400), (true, vertices_416), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 15, 19, 21, 23, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 14 else
  if p.val = (false, vertices_93) then 16 else
  if p.val = (false, vertices_653) then 17 else
  if p.val = (false, vertices_613) then 18 else
  if p.val = (false, vertices_185) then 20 else
  if p.val = (false, vertices_369) then 22 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_416) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
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
  frame := ![0, 2, 3, 6]
  vertex := 7
  face := Sum.inl ⟨vertices_410, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_138, (by decide +kernel)⟩ ⟨vertices_410, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
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
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_266, (by decide +kernel)⟩ ⟨vertices_782, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 4, 5, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_866, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_290, (by decide +kernel)⟩ ⟨vertices_866, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
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
noncomputable def pivot : Fin 4 → Fin 9 := ![6, 2, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_782, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_266, (by decide +kernel)⟩ ⟨vertices_782, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_410, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 2, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_138, (by decide +kernel)⟩ ⟨vertices_410, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_650, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 2, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_138, (by decide +kernel)⟩ ⟨vertices_650, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_866, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![0, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_290, (by decide +kernel)⟩ ⟨vertices_866, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_418, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![0, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_162, (by decide +kernel)⟩ ⟨vertices_418, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_284, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![1, 2, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_28, (by decide +kernel)⟩ ⟨vertices_284, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_852, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![1, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_852, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_432, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![3, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_176, (by decide +kernel)⟩ ⟨vertices_432, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0012

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m14e10q0_0013.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0013

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_563 : Finset (Fin 10) := literalFinset [0, 1, 4, 5, 9] (by decide +kernel)
noncomputable def vertices_403 : Finset (Fin 10) := literalFinset [0, 1, 4, 7, 8] (by decide +kernel)
noncomputable def vertices_355 : Finset (Fin 10) := literalFinset [0, 1, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_453 : Finset (Fin 10) := literalFinset [0, 2, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_665 : Finset (Fin 10) := literalFinset [0, 3, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_737 : Finset (Fin 10) := literalFinset [0, 5, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_558 : Finset (Fin 10) := literalFinset [1, 2, 3, 5, 9] (by decide +kernel)
noncomputable def vertices_282 : Finset (Fin 10) := literalFinset [1, 3, 4, 8] (by decide +kernel)
noncomputable def vertices_538 : Finset (Fin 10) := literalFinset [1, 3, 4, 9] (by decide +kernel)
noncomputable def vertices_298 : Finset (Fin 10) := literalFinset [1, 3, 5, 8] (by decide +kernel)
noncomputable def vertices_412 : Finset (Fin 10) := literalFinset [2, 3, 4, 7, 8] (by decide +kernel)
noncomputable def vertices_300 : Finset (Fin 10) := literalFinset [2, 3, 5, 8] (by decide +kernel)
noncomputable def vertices_716 : Finset (Fin 10) := literalFinset [2, 3, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_868 : Finset (Fin 10) := literalFinset [2, 5, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_19 : Finset (Fin 10) := literalFinset [0, 1, 4] (by decide +kernel)
noncomputable def vertices_35 : Finset (Fin 10) := literalFinset [0, 1, 5] (by decide +kernel)
noncomputable def vertices_259 : Finset (Fin 10) := literalFinset [0, 1, 8] (by decide +kernel)
noncomputable def vertices_145 : Finset (Fin 10) := literalFinset [0, 4, 7] (by decide +kernel)
noncomputable def vertices_529 : Finset (Fin 10) := literalFinset [0, 4, 9] (by decide +kernel)
noncomputable def vertices_97 : Finset (Fin 10) := literalFinset [0, 5, 6] (by decide +kernel)
noncomputable def vertices_545 : Finset (Fin 10) := literalFinset [0, 5, 9] (by decide +kernel)
noncomputable def vertices_193 : Finset (Fin 10) := literalFinset [0, 6, 7] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_385 : Finset (Fin 10) := literalFinset [0, 7, 8] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_26 : Finset (Fin 10) := literalFinset [1, 3, 4] (by decide +kernel)
noncomputable def vertices_42 : Finset (Fin 10) := literalFinset [1, 3, 5] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_522 : Finset (Fin 10) := literalFinset [1, 3, 9] (by decide +kernel)
noncomputable def vertices_274 : Finset (Fin 10) := literalFinset [1, 4, 8] (by decide +kernel)
noncomputable def vertices_530 : Finset (Fin 10) := literalFinset [1, 4, 9] (by decide +kernel)
noncomputable def vertices_290 : Finset (Fin 10) := literalFinset [1, 5, 8] (by decide +kernel)
noncomputable def vertices_546 : Finset (Fin 10) := literalFinset [1, 5, 9] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_140 : Finset (Fin 10) := literalFinset [2, 3, 7] (by decide +kernel)
noncomputable def vertices_268 : Finset (Fin 10) := literalFinset [2, 3, 8] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_292 : Finset (Fin 10) := literalFinset [2, 5, 8] (by decide +kernel)
noncomputable def vertices_548 : Finset (Fin 10) := literalFinset [2, 5, 9] (by decide +kernel)
noncomputable def vertices_196 : Finset (Fin 10) := literalFinset [2, 6, 7] (by decide +kernel)
noncomputable def vertices_324 : Finset (Fin 10) := literalFinset [2, 6, 8] (by decide +kernel)
noncomputable def vertices_580 : Finset (Fin 10) := literalFinset [2, 6, 9] (by decide +kernel)
noncomputable def vertices_388 : Finset (Fin 10) := literalFinset [2, 7, 8] (by decide +kernel)
noncomputable def vertices_152 : Finset (Fin 10) := literalFinset [3, 4, 7] (by decide +kernel)
noncomputable def vertices_280 : Finset (Fin 10) := literalFinset [3, 4, 8] (by decide +kernel)
noncomputable def vertices_536 : Finset (Fin 10) := literalFinset [3, 4, 9] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_648 : Finset (Fin 10) := literalFinset [3, 7, 9] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_608 : Finset (Fin 10) := literalFinset [5, 6, 9] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_403, vertices_355, vertices_453, vertices_665, vertices_737, vertices_558, vertices_282, vertices_538, vertices_298, vertices_412, vertices_300, vertices_716, vertices_868] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_259, vertices_145, vertices_529, vertices_97, vertices_545, vertices_193, vertices_321, vertices_385, vertices_641, vertices_26, vertices_42, vertices_266, vertices_522, vertices_274, vertices_530, vertices_290, vertices_546, vertices_44, vertices_140, vertices_268, vertices_524, vertices_292, vertices_548, vertices_196, vertices_324, vertices_580, vertices_388, vertices_152, vertices_280, vertices_536, vertices_296, vertices_648, vertices_400, vertices_352, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_403), (false, vertices_355), (false, vertices_453), (false, vertices_665), (false, vertices_737), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_44), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_292), (true, vertices_548), (true, vertices_580), (true, vertices_280), (true, vertices_296)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 17, 19, 21, 22, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 14 else
  if p.val = (false, vertices_403) then 15 else
  if p.val = (false, vertices_355) then 16 else
  if p.val = (false, vertices_453) then 18 else
  if p.val = (false, vertices_665) then 20 else
  if p.val = (false, vertices_737) then 23 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_296) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
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
  frame := ![0, 1, 2, 4]
  vertex := 8
  face := Sum.inl ⟨vertices_558, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_42, (by decide +kernel)⟩ ⟨vertices_558, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 3, 6]
  vertex := 7
  face := Sum.inl ⟨vertices_412, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_140, (by decide +kernel)⟩ ⟨vertices_412, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
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

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 4, 5, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_868, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_292, (by decide +kernel)⟩ ⟨vertices_868, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 3, 2, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_558, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_42, (by decide +kernel)⟩ ⟨vertices_558, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_282, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 2, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_26, (by decide +kernel)⟩ ⟨vertices_282, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_538, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 2, 3, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_26, (by decide +kernel)⟩ ⟨vertices_538, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_298, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 2, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_42, (by decide +kernel)⟩ ⟨vertices_298, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_412, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![1, 2, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_140, (by decide +kernel)⟩ ⟨vertices_412, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_300, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![1, 2, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_300, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_716, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![1, 2, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_140, (by decide +kernel)⟩ ⟨vertices_716, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_868, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .oneRow ![1, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_292, (by decide +kernel)⟩ ⟨vertices_868, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0013

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m14e10q0_0023.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0023

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_55 : Finset (Fin 10) := literalFinset [0, 1, 2, 4, 5] (by decide +kernel)
noncomputable def vertices_91 : Finset (Fin 10) := literalFinset [0, 1, 3, 4, 6] (by decide +kernel)
noncomputable def vertices_803 : Finset (Fin 10) := literalFinset [0, 1, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_451 : Finset (Fin 10) := literalFinset [0, 1, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_157 : Finset (Fin 10) := literalFinset [0, 2, 3, 4, 7] (by decide +kernel)
noncomputable def vertices_421 : Finset (Fin 10) := literalFinset [0, 2, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_201 : Finset (Fin 10) := literalFinset [0, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_562 : Finset (Fin 10) := literalFinset [1, 4, 5, 9] (by decide +kernel)
noncomputable def vertices_850 : Finset (Fin 10) := literalFinset [1, 4, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_572 : Finset (Fin 10) := literalFinset [2, 3, 4, 5, 9] (by decide +kernel)
noncomputable def vertices_716 : Finset (Fin 10) := literalFinset [2, 3, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_676 : Finset (Fin 10) := literalFinset [2, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_600 : Finset (Fin 10) := literalFinset [3, 4, 6, 9] (by decide +kernel)
noncomputable def vertices_992 : Finset (Fin 10) := literalFinset [5, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_19 : Finset (Fin 10) := literalFinset [0, 1, 4] (by decide +kernel)
noncomputable def vertices_35 : Finset (Fin 10) := literalFinset [0, 1, 5] (by decide +kernel)
noncomputable def vertices_67 : Finset (Fin 10) := literalFinset [0, 1, 6] (by decide +kernel)
noncomputable def vertices_259 : Finset (Fin 10) := literalFinset [0, 1, 8] (by decide +kernel)
noncomputable def vertices_21 : Finset (Fin 10) := literalFinset [0, 2, 4] (by decide +kernel)
noncomputable def vertices_37 : Finset (Fin 10) := literalFinset [0, 2, 5] (by decide +kernel)
noncomputable def vertices_133 : Finset (Fin 10) := literalFinset [0, 2, 7] (by decide +kernel)
noncomputable def vertices_25 : Finset (Fin 10) := literalFinset [0, 3, 4] (by decide +kernel)
noncomputable def vertices_73 : Finset (Fin 10) := literalFinset [0, 3, 6] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_193 : Finset (Fin 10) := literalFinset [0, 6, 7] (by decide +kernel)
noncomputable def vertices_385 : Finset (Fin 10) := literalFinset [0, 7, 8] (by decide +kernel)
noncomputable def vertices_50 : Finset (Fin 10) := literalFinset [1, 4, 5] (by decide +kernel)
noncomputable def vertices_82 : Finset (Fin 10) := literalFinset [1, 4, 6] (by decide +kernel)
noncomputable def vertices_530 : Finset (Fin 10) := literalFinset [1, 4, 9] (by decide +kernel)
noncomputable def vertices_546 : Finset (Fin 10) := literalFinset [1, 5, 9] (by decide +kernel)
noncomputable def vertices_322 : Finset (Fin 10) := literalFinset [1, 6, 8] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_28 : Finset (Fin 10) := literalFinset [2, 3, 4] (by decide +kernel)
noncomputable def vertices_140 : Finset (Fin 10) := literalFinset [2, 3, 7] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_164 : Finset (Fin 10) := literalFinset [2, 5, 7] (by decide +kernel)
noncomputable def vertices_548 : Finset (Fin 10) := literalFinset [2, 5, 9] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_88 : Finset (Fin 10) := literalFinset [3, 4, 6] (by decide +kernel)
noncomputable def vertices_536 : Finset (Fin 10) := literalFinset [3, 4, 9] (by decide +kernel)
noncomputable def vertices_200 : Finset (Fin 10) := literalFinset [3, 6, 7] (by decide +kernel)
noncomputable def vertices_584 : Finset (Fin 10) := literalFinset [3, 6, 9] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_55, vertices_91, vertices_803, vertices_451, vertices_157, vertices_421, vertices_201, vertices_562, vertices_850, vertices_572, vertices_716, vertices_676, vertices_600, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_67, vertices_259, vertices_21, vertices_37, vertices_133, vertices_25, vertices_73, vertices_137, vertices_289, vertices_193, vertices_385, vertices_50, vertices_82, vertices_530, vertices_546, vertices_322, vertices_770, vertices_28, vertices_140, vertices_524, vertices_52, vertices_164, vertices_548, vertices_644, vertices_88, vertices_536, vertices_200, vertices_584, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_55), (false, vertices_91), (false, vertices_803), (false, vertices_451), (false, vertices_157), (false, vertices_421), (false, vertices_201), (true, vertices_530), (true, vertices_524), (true, vertices_548), (true, vertices_644), (true, vertices_536), (true, vertices_584), (true, vertices_560), (true, vertices_592), (true, vertices_672), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![16, 12, 20, 21, 22, 23, 24, 25, 26]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_55) then 13 else
  if p.val = (false, vertices_91) then 17 else
  if p.val = (false, vertices_803) then 18 else
  if p.val = (false, vertices_451) then 19 else
  if p.val = (false, vertices_157) then 14 else
  if p.val = (false, vertices_421) then 15 else
  if p.val = (false, vertices_201) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_201), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_55), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
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
  frameSize := 4
  frame := ![1, 2, 3, 4]
  vertex := 8
  face := Sum.inl ⟨vertices_572, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_28, (by decide +kernel)⟩ ⟨vertices_572, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
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

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![4, 5, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_992, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_416, (by decide +kernel)⟩ ⟨vertices_992, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 3, 1, 4]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_562, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .fundamental ![0, 3, 4, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_50, (by decide +kernel)⟩ ⟨vertices_562, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_850, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_82, (by decide +kernel)⟩ ⟨vertices_850, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_572, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![1, 2, 3, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_28, (by decide +kernel)⟩ ⟨vertices_572, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_716, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 2, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_140, (by decide +kernel)⟩ ⟨vertices_716, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_676, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![1, 4, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_164, (by decide +kernel)⟩ ⟨vertices_676, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_600, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![2, 3, 5, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_88, (by decide +kernel)⟩ ⟨vertices_600, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_992, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![4, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_416, (by decide +kernel)⟩ ⟨vertices_992, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0023

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m14e10q0_0024.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0024

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_55 : Finset (Fin 10) := literalFinset [0, 1, 2, 4, 5] (by decide +kernel)
noncomputable def vertices_91 : Finset (Fin 10) := literalFinset [0, 1, 3, 4, 6] (by decide +kernel)
noncomputable def vertices_803 : Finset (Fin 10) := literalFinset [0, 1, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_451 : Finset (Fin 10) := literalFinset [0, 1, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_157 : Finset (Fin 10) := literalFinset [0, 2, 3, 4, 7] (by decide +kernel)
noncomputable def vertices_421 : Finset (Fin 10) := literalFinset [0, 2, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_201 : Finset (Fin 10) := literalFinset [0, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_562 : Finset (Fin 10) := literalFinset [1, 4, 5, 9] (by decide +kernel)
noncomputable def vertices_850 : Finset (Fin 10) := literalFinset [1, 4, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_604 : Finset (Fin 10) := literalFinset [2, 3, 4, 6, 9] (by decide +kernel)
noncomputable def vertices_684 : Finset (Fin 10) := literalFinset [2, 3, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_564 : Finset (Fin 10) := literalFinset [2, 4, 5, 9] (by decide +kernel)
noncomputable def vertices_712 : Finset (Fin 10) := literalFinset [3, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_992 : Finset (Fin 10) := literalFinset [5, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_19 : Finset (Fin 10) := literalFinset [0, 1, 4] (by decide +kernel)
noncomputable def vertices_35 : Finset (Fin 10) := literalFinset [0, 1, 5] (by decide +kernel)
noncomputable def vertices_67 : Finset (Fin 10) := literalFinset [0, 1, 6] (by decide +kernel)
noncomputable def vertices_259 : Finset (Fin 10) := literalFinset [0, 1, 8] (by decide +kernel)
noncomputable def vertices_21 : Finset (Fin 10) := literalFinset [0, 2, 4] (by decide +kernel)
noncomputable def vertices_37 : Finset (Fin 10) := literalFinset [0, 2, 5] (by decide +kernel)
noncomputable def vertices_133 : Finset (Fin 10) := literalFinset [0, 2, 7] (by decide +kernel)
noncomputable def vertices_25 : Finset (Fin 10) := literalFinset [0, 3, 4] (by decide +kernel)
noncomputable def vertices_73 : Finset (Fin 10) := literalFinset [0, 3, 6] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_193 : Finset (Fin 10) := literalFinset [0, 6, 7] (by decide +kernel)
noncomputable def vertices_385 : Finset (Fin 10) := literalFinset [0, 7, 8] (by decide +kernel)
noncomputable def vertices_50 : Finset (Fin 10) := literalFinset [1, 4, 5] (by decide +kernel)
noncomputable def vertices_82 : Finset (Fin 10) := literalFinset [1, 4, 6] (by decide +kernel)
noncomputable def vertices_530 : Finset (Fin 10) := literalFinset [1, 4, 9] (by decide +kernel)
noncomputable def vertices_546 : Finset (Fin 10) := literalFinset [1, 5, 9] (by decide +kernel)
noncomputable def vertices_322 : Finset (Fin 10) := literalFinset [1, 6, 8] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_28 : Finset (Fin 10) := literalFinset [2, 3, 4] (by decide +kernel)
noncomputable def vertices_140 : Finset (Fin 10) := literalFinset [2, 3, 7] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_532 : Finset (Fin 10) := literalFinset [2, 4, 9] (by decide +kernel)
noncomputable def vertices_164 : Finset (Fin 10) := literalFinset [2, 5, 7] (by decide +kernel)
noncomputable def vertices_548 : Finset (Fin 10) := literalFinset [2, 5, 9] (by decide +kernel)
noncomputable def vertices_88 : Finset (Fin 10) := literalFinset [3, 4, 6] (by decide +kernel)
noncomputable def vertices_200 : Finset (Fin 10) := literalFinset [3, 6, 7] (by decide +kernel)
noncomputable def vertices_584 : Finset (Fin 10) := literalFinset [3, 6, 9] (by decide +kernel)
noncomputable def vertices_648 : Finset (Fin 10) := literalFinset [3, 7, 9] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_55, vertices_91, vertices_803, vertices_451, vertices_157, vertices_421, vertices_201, vertices_562, vertices_850, vertices_604, vertices_684, vertices_564, vertices_712, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_67, vertices_259, vertices_21, vertices_37, vertices_133, vertices_25, vertices_73, vertices_137, vertices_289, vertices_193, vertices_385, vertices_50, vertices_82, vertices_530, vertices_546, vertices_322, vertices_770, vertices_28, vertices_140, vertices_524, vertices_52, vertices_532, vertices_164, vertices_548, vertices_88, vertices_200, vertices_584, vertices_648, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_55), (false, vertices_91), (false, vertices_803), (false, vertices_451), (false, vertices_157), (false, vertices_421), (false, vertices_201), (true, vertices_530), (true, vertices_524), (true, vertices_532), (true, vertices_548), (true, vertices_584), (true, vertices_648), (true, vertices_560), (true, vertices_592), (true, vertices_672), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![16, 12, 20, 21, 22, 23, 24, 25, 26]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_55) then 13 else
  if p.val = (false, vertices_91) then 17 else
  if p.val = (false, vertices_803) then 18 else
  if p.val = (false, vertices_451) then 19 else
  if p.val = (false, vertices_157) then 14 else
  if p.val = (false, vertices_421) then 15 else
  if p.val = (false, vertices_201) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_201), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_55), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
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
  frameSize := 4
  frame := ![1, 2, 3, 5]
  vertex := 8
  face := Sum.inl ⟨vertices_604, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_28, (by decide +kernel)⟩ ⟨vertices_604, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 4, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_684, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_140, (by decide +kernel)⟩ ⟨vertices_684, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
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
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_416, (by decide +kernel)⟩ ⟨vertices_992, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 3, 1, 4]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_562, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .fundamental ![0, 3, 4, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_50, (by decide +kernel)⟩ ⟨vertices_562, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_850, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_82, (by decide +kernel)⟩ ⟨vertices_850, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_604, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![1, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_28, (by decide +kernel)⟩ ⟨vertices_604, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_684, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 2, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_140, (by decide +kernel)⟩ ⟨vertices_684, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_564, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![1, 3, 4, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_564, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_712, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![2, 5, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_200, (by decide +kernel)⟩ ⟨vertices_712, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_992, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![4, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_416, (by decide +kernel)⟩ ⟨vertices_992, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0024

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m14e10q0_0029.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0029

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_327 : Finset (Fin 10) := literalFinset [0, 1, 2, 6, 8] (by decide +kernel)
noncomputable def vertices_91 : Finset (Fin 10) := literalFinset [0, 1, 3, 4, 6] (by decide +kernel)
noncomputable def vertices_299 : Finset (Fin 10) := literalFinset [0, 1, 3, 5, 8] (by decide +kernel)
noncomputable def vertices_117 : Finset (Fin 10) := literalFinset [0, 2, 4, 5, 6] (by decide +kernel)
noncomputable def vertices_805 : Finset (Fin 10) := literalFinset [0, 2, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_185 : Finset (Fin 10) := literalFinset [0, 3, 4, 5, 7] (by decide +kernel)
noncomputable def vertices_202 : Finset (Fin 10) := literalFinset [1, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_394 : Finset (Fin 10) := literalFinset [1, 3, 7, 8] (by decide +kernel)
noncomputable def vertices_962 : Finset (Fin 10) := literalFinset [1, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_220 : Finset (Fin 10) := literalFinset [2, 3, 4, 6, 7] (by decide +kernel)
noncomputable def vertices_692 : Finset (Fin 10) := literalFinset [2, 4, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_708 : Finset (Fin 10) := literalFinset [2, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_836 : Finset (Fin 10) := literalFinset [2, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_936 : Finset (Fin 10) := literalFinset [3, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_67 : Finset (Fin 10) := literalFinset [0, 1, 6] (by decide +kernel)
noncomputable def vertices_259 : Finset (Fin 10) := literalFinset [0, 1, 8] (by decide +kernel)
noncomputable def vertices_37 : Finset (Fin 10) := literalFinset [0, 2, 5] (by decide +kernel)
noncomputable def vertices_69 : Finset (Fin 10) := literalFinset [0, 2, 6] (by decide +kernel)
noncomputable def vertices_261 : Finset (Fin 10) := literalFinset [0, 2, 8] (by decide +kernel)
noncomputable def vertices_25 : Finset (Fin 10) := literalFinset [0, 3, 4] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_74 : Finset (Fin 10) := literalFinset [1, 3, 6] (by decide +kernel)
noncomputable def vertices_138 : Finset (Fin 10) := literalFinset [1, 3, 7] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_194 : Finset (Fin 10) := literalFinset [1, 6, 7] (by decide +kernel)
noncomputable def vertices_322 : Finset (Fin 10) := literalFinset [1, 6, 8] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_148 : Finset (Fin 10) := literalFinset [2, 4, 7] (by decide +kernel)
noncomputable def vertices_548 : Finset (Fin 10) := literalFinset [2, 5, 9] (by decide +kernel)
noncomputable def vertices_196 : Finset (Fin 10) := literalFinset [2, 6, 7] (by decide +kernel)
noncomputable def vertices_324 : Finset (Fin 10) := literalFinset [2, 6, 8] (by decide +kernel)
noncomputable def vertices_580 : Finset (Fin 10) := literalFinset [2, 6, 9] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_88 : Finset (Fin 10) := literalFinset [3, 4, 6] (by decide +kernel)
noncomputable def vertices_152 : Finset (Fin 10) := literalFinset [3, 4, 7] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_200 : Finset (Fin 10) := literalFinset [3, 6, 7] (by decide +kernel)
noncomputable def vertices_392 : Finset (Fin 10) := literalFinset [3, 7, 8] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_91, vertices_299, vertices_117, vertices_805, vertices_185, vertices_202, vertices_394, vertices_962, vertices_220, vertices_692, vertices_708, vertices_836, vertices_936] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_67, vertices_259, vertices_37, vertices_69, vertices_261, vertices_25, vertices_41, vertices_49, vertices_81, vertices_289, vertices_74, vertices_138, vertices_266, vertices_194, vertices_322, vertices_386, vertices_52, vertices_84, vertices_148, vertices_548, vertices_196, vertices_324, vertices_580, vertices_644, vertices_772, vertices_88, vertices_152, vertices_168, vertices_296, vertices_200, vertices_392, vertices_176, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_91), (false, vertices_299), (false, vertices_117), (false, vertices_805), (false, vertices_185), (true, vertices_138), (true, vertices_194), (true, vertices_386), (true, vertices_148), (true, vertices_196), (true, vertices_580), (true, vertices_644), (true, vertices_200), (true, vertices_392), (true, vertices_672), (true, vertices_704), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 17, 20, 22, 23, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 14 else
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_299) then 16 else
  if p.val = (false, vertices_117) then 18 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_185) then 21 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_580) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_392) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
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
  vertex := 6
  face := Sum.inl ⟨vertices_220, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_220, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
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
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 5, 1, 2]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_202, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .fundamental ![0, 2, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_74, (by decide +kernel)⟩ ⟨vertices_202, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_394, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 2, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_138, (by decide +kernel)⟩ ⟨vertices_394, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_962, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_194, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_220, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_220, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_692, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![1, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_692, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_708, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![1, 5, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_196, (by decide +kernel)⟩ ⟨vertices_708, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_836, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![1, 5, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_324, (by decide +kernel)⟩ ⟨vertices_836, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_936, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .oneRow ![2, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_168, (by decide +kernel)⟩ ⟨vertices_936, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0029

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m14e10q0_0032.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0032

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_331 : Finset (Fin 10) := literalFinset [0, 1, 3, 6, 8] (by decide +kernel)
noncomputable def vertices_651 : Finset (Fin 10) := literalFinset [0, 1, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_595 : Finset (Fin 10) := literalFinset [0, 1, 4, 6, 9] (by decide +kernel)
noncomputable def vertices_181 : Finset (Fin 10) := literalFinset [0, 2, 4, 5, 7] (by decide +kernel)
noncomputable def vertices_425 : Finset (Fin 10) := literalFinset [0, 3, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_369 : Finset (Fin 10) := literalFinset [0, 4, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_657 : Finset (Fin 10) := literalFinset [0, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_782 : Finset (Fin 10) := literalFinset [1, 2, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_866 : Finset (Fin 10) := literalFinset [1, 5, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_668 : Finset (Fin 10) := literalFinset [2, 3, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_396 : Finset (Fin 10) := literalFinset [2, 3, 7, 8] (by decide +kernel)
noncomputable def vertices_628 : Finset (Fin 10) := literalFinset [2, 4, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_420 : Finset (Fin 10) := literalFinset [2, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_804 : Finset (Fin 10) := literalFinset [2, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_67 : Finset (Fin 10) := literalFinset [0, 1, 6] (by decide +kernel)
noncomputable def vertices_515 : Finset (Fin 10) := literalFinset [0, 1, 9] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_265 : Finset (Fin 10) := literalFinset [0, 3, 8] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_145 : Finset (Fin 10) := literalFinset [0, 4, 7] (by decide +kernel)
noncomputable def vertices_529 : Finset (Fin 10) := literalFinset [0, 4, 9] (by decide +kernel)
noncomputable def vertices_161 : Finset (Fin 10) := literalFinset [0, 5, 7] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_522 : Finset (Fin 10) := literalFinset [1, 3, 9] (by decide +kernel)
noncomputable def vertices_322 : Finset (Fin 10) := literalFinset [1, 6, 8] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_140 : Finset (Fin 10) := literalFinset [2, 3, 7] (by decide +kernel)
noncomputable def vertices_268 : Finset (Fin 10) := literalFinset [2, 3, 8] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_148 : Finset (Fin 10) := literalFinset [2, 4, 7] (by decide +kernel)
noncomputable def vertices_532 : Finset (Fin 10) := literalFinset [2, 4, 9] (by decide +kernel)
noncomputable def vertices_164 : Finset (Fin 10) := literalFinset [2, 5, 7] (by decide +kernel)
noncomputable def vertices_292 : Finset (Fin 10) := literalFinset [2, 5, 8] (by decide +kernel)
noncomputable def vertices_548 : Finset (Fin 10) := literalFinset [2, 5, 9] (by decide +kernel)
noncomputable def vertices_388 : Finset (Fin 10) := literalFinset [2, 7, 8] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_392 : Finset (Fin 10) := literalFinset [3, 7, 8] (by decide +kernel)
noncomputable def vertices_648 : Finset (Fin 10) := literalFinset [3, 7, 9] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_608 : Finset (Fin 10) := literalFinset [5, 6, 9] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_651, vertices_595, vertices_181, vertices_425, vertices_369, vertices_657, vertices_782, vertices_866, vertices_668, vertices_396, vertices_628, vertices_420, vertices_804] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_67, vertices_515, vertices_137, vertices_265, vertices_49, vertices_81, vertices_145, vertices_529, vertices_161, vertices_289, vertices_321, vertices_641, vertices_266, vertices_522, vertices_322, vertices_578, vertices_770, vertices_140, vertices_268, vertices_524, vertices_52, vertices_148, vertices_532, vertices_164, vertices_292, vertices_548, vertices_388, vertices_772, vertices_392, vertices_648, vertices_112, vertices_592, vertices_656, vertices_352, vertices_608, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_651), (false, vertices_595), (false, vertices_181), (false, vertices_425), (false, vertices_369), (false, vertices_657), (true, vertices_770), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_532), (true, vertices_292), (true, vertices_548), (true, vertices_388), (true, vertices_772), (true, vertices_608), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![12, 16, 18, 20, 22, 23, 24, 25, 26]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 13 else
  if p.val = (false, vertices_651) then 14 else
  if p.val = (false, vertices_595) then 15 else
  if p.val = (false, vertices_181) then 17 else
  if p.val = (false, vertices_425) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (false, vertices_657) then 0 else
  if p.val = (true, vertices_770) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_657), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
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
  frame := ![1, 2, 3, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_668, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_140, (by decide +kernel)⟩ ⟨vertices_668, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
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
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_266, (by decide +kernel)⟩ ⟨vertices_782, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 4, 5, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_866, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_322, (by decide +kernel)⟩ ⟨vertices_866, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
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

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![6, 2, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_782, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_266, (by decide +kernel)⟩ ⟨vertices_782, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_866, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_322, (by decide +kernel)⟩ ⟨vertices_866, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_668, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![1, 2, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_140, (by decide +kernel)⟩ ⟨vertices_668, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_396, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![1, 2, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_140, (by decide +kernel)⟩ ⟨vertices_396, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_628, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![1, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_628, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_420, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![1, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_164, (by decide +kernel)⟩ ⟨vertices_420, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_804, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![1, 4, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_292, (by decide +kernel)⟩ ⟨vertices_804, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0032

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m14e10q0_0033.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0033

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_103 : Finset (Fin 10) := literalFinset [0, 1, 2, 5, 6] (by decide +kernel)
noncomputable def vertices_395 : Finset (Fin 10) := literalFinset [0, 1, 3, 7, 8] (by decide +kernel)
noncomputable def vertices_307 : Finset (Fin 10) := literalFinset [0, 1, 4, 5, 8] (by decide +kernel)
noncomputable def vertices_707 : Finset (Fin 10) := literalFinset [0, 1, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_61 : Finset (Fin 10) := literalFinset [0, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_653 : Finset (Fin 10) := literalFinset [0, 2, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_581 : Finset (Fin 10) := literalFinset [0, 2, 6, 9] (by decide +kernel)
noncomputable def vertices_281 : Finset (Fin 10) := literalFinset [0, 3, 4, 8] (by decide +kernel)
noncomputable def vertices_482 : Finset (Fin 10) := literalFinset [1, 5, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_796 : Finset (Fin 10) := literalFinset [2, 3, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_628 : Finset (Fin 10) := literalFinset [2, 4, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_968 : Finset (Fin 10) := literalFinset [3, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_816 : Finset (Fin 10) := literalFinset [4, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_864 : Finset (Fin 10) := literalFinset [5, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_35 : Finset (Fin 10) := literalFinset [0, 1, 5] (by decide +kernel)
noncomputable def vertices_67 : Finset (Fin 10) := literalFinset [0, 1, 6] (by decide +kernel)
noncomputable def vertices_131 : Finset (Fin 10) := literalFinset [0, 1, 7] (by decide +kernel)
noncomputable def vertices_259 : Finset (Fin 10) := literalFinset [0, 1, 8] (by decide +kernel)
noncomputable def vertices_13 : Finset (Fin 10) := literalFinset [0, 2, 3] (by decide +kernel)
noncomputable def vertices_37 : Finset (Fin 10) := literalFinset [0, 2, 5] (by decide +kernel)
noncomputable def vertices_69 : Finset (Fin 10) := literalFinset [0, 2, 6] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_25 : Finset (Fin 10) := literalFinset [0, 3, 4] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_265 : Finset (Fin 10) := literalFinset [0, 3, 8] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_273 : Finset (Fin 10) := literalFinset [0, 4, 8] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_98 : Finset (Fin 10) := literalFinset [1, 5, 6] (by decide +kernel)
noncomputable def vertices_290 : Finset (Fin 10) := literalFinset [1, 5, 8] (by decide +kernel)
noncomputable def vertices_194 : Finset (Fin 10) := literalFinset [1, 6, 7] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_28 : Finset (Fin 10) := literalFinset [2, 3, 4] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_532 : Finset (Fin 10) := literalFinset [2, 4, 9] (by decide +kernel)
noncomputable def vertices_100 : Finset (Fin 10) := literalFinset [2, 5, 6] (by decide +kernel)
noncomputable def vertices_580 : Finset (Fin 10) := literalFinset [2, 6, 9] (by decide +kernel)
noncomputable def vertices_280 : Finset (Fin 10) := literalFinset [3, 4, 8] (by decide +kernel)
noncomputable def vertices_392 : Finset (Fin 10) := literalFinset [3, 7, 8] (by decide +kernel)
noncomputable def vertices_648 : Finset (Fin 10) := literalFinset [3, 7, 9] (by decide +kernel)
noncomputable def vertices_776 : Finset (Fin 10) := literalFinset [3, 8, 9] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_784 : Finset (Fin 10) := literalFinset [4, 8, 9] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_608 : Finset (Fin 10) := literalFinset [5, 6, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_103, vertices_395, vertices_307, vertices_707, vertices_61, vertices_653, vertices_581, vertices_281, vertices_482, vertices_796, vertices_628, vertices_968, vertices_816, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_131, vertices_259, vertices_13, vertices_37, vertices_69, vertices_517, vertices_25, vertices_137, vertices_265, vertices_49, vertices_273, vertices_577, vertices_641, vertices_98, vertices_290, vertices_194, vertices_386, vertices_28, vertices_524, vertices_52, vertices_532, vertices_100, vertices_580, vertices_280, vertices_392, vertices_648, vertices_776, vertices_304, vertices_560, vertices_784, vertices_352, vertices_608, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_103), (false, vertices_395), (false, vertices_307), (false, vertices_707), (false, vertices_61), (false, vertices_653), (false, vertices_581), (false, vertices_281), (true, vertices_532), (true, vertices_776), (true, vertices_560), (true, vertices_784), (true, vertices_352), (true, vertices_608), (true, vertices_800), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![15, 11, 19, 20, 21, 22, 23, 24, 25]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_103) then 12 else
  if p.val = (false, vertices_395) then 16 else
  if p.val = (false, vertices_307) then 17 else
  if p.val = (false, vertices_707) then 18 else
  if p.val = (false, vertices_61) then 13 else
  if p.val = (false, vertices_653) then 14 else
  if p.val = (false, vertices_581) then 0 else
  if p.val = (false, vertices_281) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_776) then 3 else
  if p.val = (true, vertices_560) then 4 else
  if p.val = (true, vertices_784) then 5 else
  if p.val = (true, vertices_352) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_581), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_103), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_61), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
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
  frameSize := 4
  frame := ![0, 4, 5, 6]
  vertex := 7
  face := Sum.inl ⟨vertices_482, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_98, (by decide +kernel)⟩ ⟨vertices_482, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
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

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 3, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_796, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_28, (by decide +kernel)⟩ ⟨vertices_796, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![2, 5, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_968, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_392, (by decide +kernel)⟩ ⟨vertices_968, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 4, 1, 2]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_482, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_98, (by decide +kernel)⟩ ⟨vertices_482, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_796, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![1, 2, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_28, (by decide +kernel)⟩ ⟨vertices_796, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_628, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![1, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_628, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_968, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![2, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_392, (by decide +kernel)⟩ ⟨vertices_968, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_816, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![3, 4, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_304, (by decide +kernel)⟩ ⟨vertices_816, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_864, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![4, 5, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_352, (by decide +kernel)⟩ ⟨vertices_864, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0033

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m14e10q0_0034.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0034

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_227 : Finset (Fin 10) := literalFinset [0, 1, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_285 : Finset (Fin 10) := literalFinset [0, 2, 3, 4, 8] (by decide +kernel)
noncomputable def vertices_557 : Finset (Fin 10) := literalFinset [0, 2, 3, 5, 9] (by decide +kernel)
noncomputable def vertices_533 : Finset (Fin 10) := literalFinset [0, 2, 4, 9] (by decide +kernel)
noncomputable def vertices_361 : Finset (Fin 10) := literalFinset [0, 3, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_689 : Finset (Fin 10) := literalFinset [0, 4, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_465 : Finset (Fin 10) := literalFinset [0, 4, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_782 : Finset (Fin 10) := literalFinset [1, 2, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_682 : Finset (Fin 10) := literalFinset [1, 3, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_298 : Finset (Fin 10) := literalFinset [1, 3, 5, 8] (by decide +kernel)
noncomputable def vertices_722 : Finset (Fin 10) := literalFinset [1, 4, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_354 : Finset (Fin 10) := literalFinset [1, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_834 : Finset (Fin 10) := literalFinset [1, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_852 : Finset (Fin 10) := literalFinset [2, 4, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_13 : Finset (Fin 10) := literalFinset [0, 2, 3] (by decide +kernel)
noncomputable def vertices_21 : Finset (Fin 10) := literalFinset [0, 2, 4] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_265 : Finset (Fin 10) := literalFinset [0, 3, 8] (by decide +kernel)
noncomputable def vertices_145 : Finset (Fin 10) := literalFinset [0, 4, 7] (by decide +kernel)
noncomputable def vertices_273 : Finset (Fin 10) := literalFinset [0, 4, 8] (by decide +kernel)
noncomputable def vertices_529 : Finset (Fin 10) := literalFinset [0, 4, 9] (by decide +kernel)
noncomputable def vertices_97 : Finset (Fin 10) := literalFinset [0, 5, 6] (by decide +kernel)
noncomputable def vertices_161 : Finset (Fin 10) := literalFinset [0, 5, 7] (by decide +kernel)
noncomputable def vertices_545 : Finset (Fin 10) := literalFinset [0, 5, 9] (by decide +kernel)
noncomputable def vertices_193 : Finset (Fin 10) := literalFinset [0, 6, 7] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_42 : Finset (Fin 10) := literalFinset [1, 3, 5] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_522 : Finset (Fin 10) := literalFinset [1, 3, 9] (by decide +kernel)
noncomputable def vertices_98 : Finset (Fin 10) := literalFinset [1, 5, 6] (by decide +kernel)
noncomputable def vertices_162 : Finset (Fin 10) := literalFinset [1, 5, 7] (by decide +kernel)
noncomputable def vertices_290 : Finset (Fin 10) := literalFinset [1, 5, 8] (by decide +kernel)
noncomputable def vertices_194 : Finset (Fin 10) := literalFinset [1, 6, 7] (by decide +kernel)
noncomputable def vertices_322 : Finset (Fin 10) := literalFinset [1, 6, 8] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_268 : Finset (Fin 10) := literalFinset [2, 3, 8] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_532 : Finset (Fin 10) := literalFinset [2, 4, 9] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_552 : Finset (Fin 10) := literalFinset [3, 5, 9] (by decide +kernel)
noncomputable def vertices_208 : Finset (Fin 10) := literalFinset [4, 6, 7] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_227, vertices_285, vertices_557, vertices_533, vertices_361, vertices_689, vertices_465, vertices_782, vertices_682, vertices_298, vertices_722, vertices_354, vertices_834, vertices_852] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_517, vertices_41, vertices_265, vertices_145, vertices_273, vertices_529, vertices_97, vertices_161, vertices_545, vertices_193, vertices_321, vertices_42, vertices_266, vertices_522, vertices_98, vertices_162, vertices_290, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_268, vertices_524, vertices_276, vertices_532, vertices_772, vertices_296, vertices_552, vertices_208, vertices_336, vertices_592, vertices_656, vertices_352, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_227), (false, vertices_285), (false, vertices_557), (false, vertices_533), (false, vertices_361), (false, vertices_689), (false, vertices_465), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_290), (true, vertices_322), (true, vertices_578), (true, vertices_642), (true, vertices_770), (true, vertices_772), (true, vertices_592), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![12, 14, 17, 19, 22, 23, 24, 25, 26]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_227) then 13 else
  if p.val = (false, vertices_285) then 15 else
  if p.val = (false, vertices_557) then 16 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_361) then 18 else
  if p.val = (false, vertices_689) then 20 else
  if p.val = (false, vertices_465) then 21 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
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
  frame := ![0, 2, 4, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_682, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_42, (by decide +kernel)⟩ ⟨vertices_682, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
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
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_266, (by decide +kernel)⟩ ⟨vertices_782, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 3, 5, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_722, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_194, (by decide +kernel)⟩ ⟨vertices_722, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
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
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_276, (by decide +kernel)⟩ ⟨vertices_852, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![4, 2, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_782, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_266, (by decide +kernel)⟩ ⟨vertices_782, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_682, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 2, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_42, (by decide +kernel)⟩ ⟨vertices_682, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_298, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 2, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_42, (by decide +kernel)⟩ ⟨vertices_298, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_722, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![0, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_194, (by decide +kernel)⟩ ⟨vertices_722, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_354, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![0, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_98, (by decide +kernel)⟩ ⟨vertices_354, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_834, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![0, 5, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_322, (by decide +kernel)⟩ ⟨vertices_834, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_852, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![1, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_276, (by decide +kernel)⟩ ⟨vertices_852, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0034

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m14e10q0_0035.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0035

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_103 : Finset (Fin 10) := literalFinset [0, 1, 2, 5, 6] (by decide +kernel)
noncomputable def vertices_299 : Finset (Fin 10) := literalFinset [0, 1, 3, 5, 8] (by decide +kernel)
noncomputable def vertices_595 : Finset (Fin 10) := literalFinset [0, 1, 4, 6, 9] (by decide +kernel)
noncomputable def vertices_275 : Finset (Fin 10) := literalFinset [0, 1, 4, 8] (by decide +kernel)
noncomputable def vertices_173 : Finset (Fin 10) := literalFinset [0, 2, 3, 5, 7] (by decide +kernel)
noncomputable def vertices_661 : Finset (Fin 10) := literalFinset [0, 2, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_581 : Finset (Fin 10) := literalFinset [0, 2, 6, 9] (by decide +kernel)
noncomputable def vertices_409 : Finset (Fin 10) := literalFinset [0, 3, 4, 7, 8] (by decide +kernel)
noncomputable def vertices_370 : Finset (Fin 10) := literalFinset [1, 4, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_620 : Finset (Fin 10) := literalFinset [2, 3, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_908 : Finset (Fin 10) := literalFinset [2, 3, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_808 : Finset (Fin 10) := literalFinset [3, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_976 : Finset (Fin 10) := literalFinset [4, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_864 : Finset (Fin 10) := literalFinset [5, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_19 : Finset (Fin 10) := literalFinset [0, 1, 4] (by decide +kernel)
noncomputable def vertices_35 : Finset (Fin 10) := literalFinset [0, 1, 5] (by decide +kernel)
noncomputable def vertices_67 : Finset (Fin 10) := literalFinset [0, 1, 6] (by decide +kernel)
noncomputable def vertices_259 : Finset (Fin 10) := literalFinset [0, 1, 8] (by decide +kernel)
noncomputable def vertices_37 : Finset (Fin 10) := literalFinset [0, 2, 5] (by decide +kernel)
noncomputable def vertices_69 : Finset (Fin 10) := literalFinset [0, 2, 6] (by decide +kernel)
noncomputable def vertices_133 : Finset (Fin 10) := literalFinset [0, 2, 7] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_265 : Finset (Fin 10) := literalFinset [0, 3, 8] (by decide +kernel)
noncomputable def vertices_145 : Finset (Fin 10) := literalFinset [0, 4, 7] (by decide +kernel)
noncomputable def vertices_273 : Finset (Fin 10) := literalFinset [0, 4, 8] (by decide +kernel)
noncomputable def vertices_529 : Finset (Fin 10) := literalFinset [0, 4, 9] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_82 : Finset (Fin 10) := literalFinset [1, 4, 6] (by decide +kernel)
noncomputable def vertices_274 : Finset (Fin 10) := literalFinset [1, 4, 8] (by decide +kernel)
noncomputable def vertices_98 : Finset (Fin 10) := literalFinset [1, 5, 6] (by decide +kernel)
noncomputable def vertices_290 : Finset (Fin 10) := literalFinset [1, 5, 8] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_140 : Finset (Fin 10) := literalFinset [2, 3, 7] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_100 : Finset (Fin 10) := literalFinset [2, 5, 6] (by decide +kernel)
noncomputable def vertices_580 : Finset (Fin 10) := literalFinset [2, 6, 9] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_552 : Finset (Fin 10) := literalFinset [3, 5, 9] (by decide +kernel)
noncomputable def vertices_392 : Finset (Fin 10) := literalFinset [3, 7, 8] (by decide +kernel)
noncomputable def vertices_776 : Finset (Fin 10) := literalFinset [3, 8, 9] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_608 : Finset (Fin 10) := literalFinset [5, 6, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_103, vertices_299, vertices_595, vertices_275, vertices_173, vertices_661, vertices_581, vertices_409, vertices_370, vertices_620, vertices_908, vertices_808, vertices_976, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_67, vertices_259, vertices_37, vertices_69, vertices_133, vertices_517, vertices_41, vertices_137, vertices_265, vertices_145, vertices_273, vertices_529, vertices_577, vertices_82, vertices_274, vertices_98, vertices_290, vertices_44, vertices_140, vertices_524, vertices_100, vertices_580, vertices_644, vertices_296, vertices_552, vertices_392, vertices_776, vertices_336, vertices_592, vertices_400, vertices_656, vertices_352, vertices_608, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_103), (false, vertices_299), (false, vertices_595), (false, vertices_275), (false, vertices_173), (false, vertices_661), (false, vertices_581), (false, vertices_409), (true, vertices_524), (true, vertices_552), (true, vertices_776), (true, vertices_336), (true, vertices_352), (true, vertices_608), (true, vertices_800), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![11, 15, 18, 20, 21, 22, 23, 24, 25]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_103) then 12 else
  if p.val = (false, vertices_299) then 13 else
  if p.val = (false, vertices_595) then 14 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_173) then 16 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_581) then 1 else
  if p.val = (false, vertices_409) then 19 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_776) then 4 else
  if p.val = (true, vertices_336) then 5 else
  if p.val = (true, vertices_352) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_832) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_581), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_103), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 20 => Sum.inl 3
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
  frameSize := 4
  frame := ![0, 3, 4, 5]
  vertex := 7
  face := Sum.inl ⟨vertices_370, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_82, (by decide +kernel)⟩ ⟨vertices_370, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
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
  frame := ![1, 2, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_908, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_140, (by decide +kernel)⟩ ⟨vertices_908, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
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
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_336, (by decide +kernel)⟩ ⟨vertices_976, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 4, 1, 3]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_370, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_82, (by decide +kernel)⟩ ⟨vertices_370, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_620, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![1, 2, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_620, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_908, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![1, 2, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_140, (by decide +kernel)⟩ ⟨vertices_908, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_808, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![2, 4, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_296, (by decide +kernel)⟩ ⟨vertices_808, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_976, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![3, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_336, (by decide +kernel)⟩ ⟨vertices_976, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_864, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![4, 5, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_352, (by decide +kernel)⟩ ⟨vertices_864, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0035

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m14e10q0_0036.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0036

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_587 : Finset (Fin 10) := literalFinset [0, 1, 3, 6, 9] (by decide +kernel)
noncomputable def vertices_541 : Finset (Fin 10) := literalFinset [0, 2, 3, 4, 9] (by decide +kernel)
noncomputable def vertices_405 : Finset (Fin 10) := literalFinset [0, 2, 4, 7, 8] (by decide +kernel)
noncomputable def vertices_677 : Finset (Fin 10) := literalFinset [0, 2, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_345 : Finset (Fin 10) := literalFinset [0, 3, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_961 : Finset (Fin 10) := literalFinset [0, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_310 : Finset (Fin 10) := literalFinset [1, 2, 4, 5, 8] (by decide +kernel)
noncomputable def vertices_570 : Finset (Fin 10) := literalFinset [1, 3, 4, 5, 9] (by decide +kernel)
noncomputable def vertices_282 : Finset (Fin 10) := literalFinset [1, 3, 4, 8] (by decide +kernel)
noncomputable def vertices_330 : Finset (Fin 10) := literalFinset [1, 3, 6, 8] (by decide +kernel)
noncomputable def vertices_738 : Finset (Fin 10) := literalFinset [1, 5, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_354 : Finset (Fin 10) := literalFinset [1, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_564 : Finset (Fin 10) := literalFinset [2, 4, 5, 9] (by decide +kernel)
noncomputable def vertices_484 : Finset (Fin 10) := literalFinset [2, 5, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_21 : Finset (Fin 10) := literalFinset [0, 2, 4] (by decide +kernel)
noncomputable def vertices_133 : Finset (Fin 10) := literalFinset [0, 2, 7] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_25 : Finset (Fin 10) := literalFinset [0, 3, 4] (by decide +kernel)
noncomputable def vertices_73 : Finset (Fin 10) := literalFinset [0, 3, 6] (by decide +kernel)
noncomputable def vertices_521 : Finset (Fin 10) := literalFinset [0, 3, 9] (by decide +kernel)
noncomputable def vertices_273 : Finset (Fin 10) := literalFinset [0, 4, 8] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_385 : Finset (Fin 10) := literalFinset [0, 7, 8] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_26 : Finset (Fin 10) := literalFinset [1, 3, 4] (by decide +kernel)
noncomputable def vertices_74 : Finset (Fin 10) := literalFinset [1, 3, 6] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_522 : Finset (Fin 10) := literalFinset [1, 3, 9] (by decide +kernel)
noncomputable def vertices_50 : Finset (Fin 10) := literalFinset [1, 4, 5] (by decide +kernel)
noncomputable def vertices_274 : Finset (Fin 10) := literalFinset [1, 4, 8] (by decide +kernel)
noncomputable def vertices_98 : Finset (Fin 10) := literalFinset [1, 5, 6] (by decide +kernel)
noncomputable def vertices_290 : Finset (Fin 10) := literalFinset [1, 5, 8] (by decide +kernel)
noncomputable def vertices_546 : Finset (Fin 10) := literalFinset [1, 5, 9] (by decide +kernel)
noncomputable def vertices_322 : Finset (Fin 10) := literalFinset [1, 6, 8] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_532 : Finset (Fin 10) := literalFinset [2, 4, 9] (by decide +kernel)
noncomputable def vertices_164 : Finset (Fin 10) := literalFinset [2, 5, 7] (by decide +kernel)
noncomputable def vertices_292 : Finset (Fin 10) := literalFinset [2, 5, 8] (by decide +kernel)
noncomputable def vertices_548 : Finset (Fin 10) := literalFinset [2, 5, 9] (by decide +kernel)
noncomputable def vertices_388 : Finset (Fin 10) := literalFinset [2, 7, 8] (by decide +kernel)
noncomputable def vertices_280 : Finset (Fin 10) := literalFinset [3, 4, 8] (by decide +kernel)
noncomputable def vertices_536 : Finset (Fin 10) := literalFinset [3, 4, 9] (by decide +kernel)
noncomputable def vertices_328 : Finset (Fin 10) := literalFinset [3, 6, 8] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_224 : Finset (Fin 10) := literalFinset [5, 6, 7] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_541, vertices_405, vertices_677, vertices_345, vertices_961, vertices_310, vertices_570, vertices_282, vertices_330, vertices_738, vertices_354, vertices_564, vertices_484] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_517, vertices_25, vertices_73, vertices_521, vertices_273, vertices_321, vertices_577, vertices_385, vertices_641, vertices_26, vertices_74, vertices_266, vertices_522, vertices_50, vertices_274, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_52, vertices_276, vertices_532, vertices_164, vertices_292, vertices_548, vertices_388, vertices_280, vertices_536, vertices_328, vertices_560, vertices_224, vertices_352, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_541), (false, vertices_405), (false, vertices_677), (false, vertices_345), (false, vertices_961), (true, vertices_26), (true, vertices_266), (true, vertices_50), (true, vertices_274), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_322), (true, vertices_52), (true, vertices_292), (true, vertices_560), (true, vertices_224), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 15, 19, 21, 22, 23, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 14 else
  if p.val = (false, vertices_541) then 16 else
  if p.val = (false, vertices_405) then 17 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_345) then 20 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_352) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
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
  frame := ![0, 2, 3, 4]
  vertex := 8
  face := Sum.inl ⟨vertices_570, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_26, (by decide +kernel)⟩ ⟨vertices_570, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 3, 4]
  vertex := 7
  face := Sum.inl ⟨vertices_310, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_50, (by decide +kernel)⟩ ⟨vertices_310, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 4, 5, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_738, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_98, (by decide +kernel)⟩ ⟨vertices_738, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 4, 5, 6]
  vertex := 7
  face := Sum.inl ⟨vertices_484, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_164, (by decide +kernel)⟩ ⟨vertices_484, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![2, 3, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_310, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 3, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_50, (by decide +kernel)⟩ ⟨vertices_310, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_570, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 2, 3, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_26, (by decide +kernel)⟩ ⟨vertices_570, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_282, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 2, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_26, (by decide +kernel)⟩ ⟨vertices_282, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_330, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 2, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_74, (by decide +kernel)⟩ ⟨vertices_330, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_738, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![0, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_98, (by decide +kernel)⟩ ⟨vertices_738, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_354, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![0, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_98, (by decide +kernel)⟩ ⟨vertices_354, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_564, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![1, 3, 4, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_564, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_484, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .oneRow ![1, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_164, (by decide +kernel)⟩ ⟨vertices_484, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0036

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m14e10q0_0037.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0037

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_295 : Finset (Fin 10) := literalFinset [0, 1, 2, 5, 8] (by decide +kernel)
noncomputable def vertices_555 : Finset (Fin 10) := literalFinset [0, 1, 3, 5, 9] (by decide +kernel)
noncomputable def vertices_331 : Finset (Fin 10) := literalFinset [0, 1, 3, 6, 8] (by decide +kernel)
noncomputable def vertices_229 : Finset (Fin 10) := literalFinset [0, 2, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_325 : Finset (Fin 10) := literalFinset [0, 2, 6, 8] (by decide +kernel)
noncomputable def vertices_713 : Finset (Fin 10) := literalFinset [0, 3, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_689 : Finset (Fin 10) := literalFinset [0, 4, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_794 : Finset (Fin 10) := literalFinset [1, 3, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_802 : Finset (Fin 10) := literalFinset [1, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_348 : Finset (Fin 10) := literalFinset [2, 3, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_436 : Finset (Fin 10) := literalFinset [2, 4, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_724 : Finset (Fin 10) := literalFinset [2, 4, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_600 : Finset (Fin 10) := literalFinset [3, 4, 6, 9] (by decide +kernel)
noncomputable def vertices_816 : Finset (Fin 10) := literalFinset [4, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_35 : Finset (Fin 10) := literalFinset [0, 1, 5] (by decide +kernel)
noncomputable def vertices_259 : Finset (Fin 10) := literalFinset [0, 1, 8] (by decide +kernel)
noncomputable def vertices_37 : Finset (Fin 10) := literalFinset [0, 2, 5] (by decide +kernel)
noncomputable def vertices_69 : Finset (Fin 10) := literalFinset [0, 2, 6] (by decide +kernel)
noncomputable def vertices_261 : Finset (Fin 10) := literalFinset [0, 2, 8] (by decide +kernel)
noncomputable def vertices_73 : Finset (Fin 10) := literalFinset [0, 3, 6] (by decide +kernel)
noncomputable def vertices_521 : Finset (Fin 10) := literalFinset [0, 3, 9] (by decide +kernel)
noncomputable def vertices_161 : Finset (Fin 10) := literalFinset [0, 5, 7] (by decide +kernel)
noncomputable def vertices_545 : Finset (Fin 10) := literalFinset [0, 5, 9] (by decide +kernel)
noncomputable def vertices_193 : Finset (Fin 10) := literalFinset [0, 6, 7] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_522 : Finset (Fin 10) := literalFinset [1, 3, 9] (by decide +kernel)
noncomputable def vertices_290 : Finset (Fin 10) := literalFinset [1, 5, 8] (by decide +kernel)
noncomputable def vertices_546 : Finset (Fin 10) := literalFinset [1, 5, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_148 : Finset (Fin 10) := literalFinset [2, 4, 7] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_164 : Finset (Fin 10) := literalFinset [2, 5, 7] (by decide +kernel)
noncomputable def vertices_292 : Finset (Fin 10) := literalFinset [2, 5, 8] (by decide +kernel)
noncomputable def vertices_196 : Finset (Fin 10) := literalFinset [2, 6, 7] (by decide +kernel)
noncomputable def vertices_324 : Finset (Fin 10) := literalFinset [2, 6, 8] (by decide +kernel)
noncomputable def vertices_88 : Finset (Fin 10) := literalFinset [3, 4, 6] (by decide +kernel)
noncomputable def vertices_280 : Finset (Fin 10) := literalFinset [3, 4, 8] (by decide +kernel)
noncomputable def vertices_536 : Finset (Fin 10) := literalFinset [3, 4, 9] (by decide +kernel)
noncomputable def vertices_328 : Finset (Fin 10) := literalFinset [3, 6, 8] (by decide +kernel)
noncomputable def vertices_584 : Finset (Fin 10) := literalFinset [3, 6, 9] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_784 : Finset (Fin 10) := literalFinset [4, 8, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_555, vertices_331, vertices_229, vertices_325, vertices_713, vertices_689, vertices_794, vertices_802, vertices_348, vertices_436, vertices_724, vertices_600, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_259, vertices_37, vertices_69, vertices_261, vertices_73, vertices_521, vertices_161, vertices_545, vertices_193, vertices_321, vertices_641, vertices_266, vertices_522, vertices_290, vertices_546, vertices_770, vertices_84, vertices_148, vertices_276, vertices_164, vertices_292, vertices_196, vertices_324, vertices_88, vertices_280, vertices_536, vertices_328, vertices_584, vertices_176, vertices_304, vertices_560, vertices_592, vertices_656, vertices_784, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_555), (false, vertices_331), (false, vertices_229), (false, vertices_325), (false, vertices_713), (false, vertices_689), (true, vertices_770), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_88), (true, vertices_280), (true, vertices_536), (true, vertices_304), (true, vertices_592), (true, vertices_784), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![12, 16, 18, 20, 22, 23, 24, 25, 26]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 13 else
  if p.val = (false, vertices_555) then 14 else
  if p.val = (false, vertices_331) then 15 else
  if p.val = (false, vertices_229) then 17 else
  if p.val = (false, vertices_325) then 0 else
  if p.val = (false, vertices_713) then 19 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (true, vertices_770) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_276) then 4 else
  if p.val = (true, vertices_88) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_325), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
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
  frame := ![0, 2, 3, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_794, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_266, (by decide +kernel)⟩ ⟨vertices_794, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 3, 5]
  vertex := 7
  face := Sum.inl ⟨vertices_348, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_348, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 3, 4, 6]
  vertex := 7
  face := Sum.inl ⟨vertices_436, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_148, (by decide +kernel)⟩ ⟨vertices_436, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
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
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 2, 4, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_794, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 2, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_266, (by decide +kernel)⟩ ⟨vertices_794, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_802, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 4, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_290, (by decide +kernel)⟩ ⟨vertices_802, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_348, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![1, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_348, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_436, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_148, (by decide +kernel)⟩ ⟨vertices_436, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_724, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![1, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_724, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_600, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![2, 3, 5, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_88, (by decide +kernel)⟩ ⟨vertices_600, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_816, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![3, 4, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_304, (by decide +kernel)⟩ ⟨vertices_816, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0037

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m14e10q0_0040.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0040

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_327 : Finset (Fin 10) := literalFinset [0, 1, 2, 6, 8] (by decide +kernel)
noncomputable def vertices_91 : Finset (Fin 10) := literalFinset [0, 1, 3, 4, 6] (by decide +kernel)
noncomputable def vertices_299 : Finset (Fin 10) := literalFinset [0, 1, 3, 5, 8] (by decide +kernel)
noncomputable def vertices_61 : Finset (Fin 10) := literalFinset [0, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_213 : Finset (Fin 10) := literalFinset [0, 2, 4, 6, 7] (by decide +kernel)
noncomputable def vertices_805 : Finset (Fin 10) := literalFinset [0, 2, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_202 : Finset (Fin 10) := literalFinset [1, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_394 : Finset (Fin 10) := literalFinset [1, 3, 7, 8] (by decide +kernel)
noncomputable def vertices_962 : Finset (Fin 10) := literalFinset [1, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_692 : Finset (Fin 10) := literalFinset [2, 4, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_708 : Finset (Fin 10) := literalFinset [2, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_836 : Finset (Fin 10) := literalFinset [2, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_248 : Finset (Fin 10) := literalFinset [3, 4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_936 : Finset (Fin 10) := literalFinset [3, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_11 : Finset (Fin 10) := literalFinset [0, 1, 3] (by decide +kernel)
noncomputable def vertices_67 : Finset (Fin 10) := literalFinset [0, 1, 6] (by decide +kernel)
noncomputable def vertices_259 : Finset (Fin 10) := literalFinset [0, 1, 8] (by decide +kernel)
noncomputable def vertices_21 : Finset (Fin 10) := literalFinset [0, 2, 4] (by decide +kernel)
noncomputable def vertices_37 : Finset (Fin 10) := literalFinset [0, 2, 5] (by decide +kernel)
noncomputable def vertices_69 : Finset (Fin 10) := literalFinset [0, 2, 6] (by decide +kernel)
noncomputable def vertices_261 : Finset (Fin 10) := literalFinset [0, 2, 8] (by decide +kernel)
noncomputable def vertices_25 : Finset (Fin 10) := literalFinset [0, 3, 4] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_74 : Finset (Fin 10) := literalFinset [1, 3, 6] (by decide +kernel)
noncomputable def vertices_138 : Finset (Fin 10) := literalFinset [1, 3, 7] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_194 : Finset (Fin 10) := literalFinset [1, 6, 7] (by decide +kernel)
noncomputable def vertices_322 : Finset (Fin 10) := literalFinset [1, 6, 8] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_148 : Finset (Fin 10) := literalFinset [2, 4, 7] (by decide +kernel)
noncomputable def vertices_548 : Finset (Fin 10) := literalFinset [2, 5, 9] (by decide +kernel)
noncomputable def vertices_196 : Finset (Fin 10) := literalFinset [2, 6, 7] (by decide +kernel)
noncomputable def vertices_324 : Finset (Fin 10) := literalFinset [2, 6, 8] (by decide +kernel)
noncomputable def vertices_580 : Finset (Fin 10) := literalFinset [2, 6, 9] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_56 : Finset (Fin 10) := literalFinset [3, 4, 5] (by decide +kernel)
noncomputable def vertices_88 : Finset (Fin 10) := literalFinset [3, 4, 6] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_200 : Finset (Fin 10) := literalFinset [3, 6, 7] (by decide +kernel)
noncomputable def vertices_392 : Finset (Fin 10) := literalFinset [3, 7, 8] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_208 : Finset (Fin 10) := literalFinset [4, 6, 7] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_91, vertices_299, vertices_61, vertices_213, vertices_805, vertices_202, vertices_394, vertices_962, vertices_692, vertices_708, vertices_836, vertices_248, vertices_936] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_67, vertices_259, vertices_21, vertices_37, vertices_69, vertices_261, vertices_25, vertices_41, vertices_81, vertices_289, vertices_74, vertices_138, vertices_266, vertices_194, vertices_322, vertices_386, vertices_52, vertices_148, vertices_548, vertices_196, vertices_324, vertices_580, vertices_644, vertices_772, vertices_56, vertices_88, vertices_168, vertices_296, vertices_200, vertices_392, vertices_176, vertices_208, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_91), (false, vertices_299), (false, vertices_61), (false, vertices_213), (false, vertices_805), (true, vertices_138), (true, vertices_194), (true, vertices_386), (true, vertices_580), (true, vertices_644), (true, vertices_168), (true, vertices_200), (true, vertices_392), (true, vertices_176), (true, vertices_672), (true, vertices_704), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 17, 21, 22, 23, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 14 else
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_299) then 16 else
  if p.val = (false, vertices_61) then 18 else
  if p.val = (false, vertices_213) then 19 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_580) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_200) then 6 else
  if p.val = (true, vertices_392) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_61), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 21 => Sum.inl 2
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
  frame := ![2, 3, 4, 5]
  vertex := 6
  face := Sum.inl ⟨vertices_248, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_248, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
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
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 1, 3, 2]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_202, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .fundamental ![0, 2, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_74, (by decide +kernel)⟩ ⟨vertices_202, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_394, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 2, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_138, (by decide +kernel)⟩ ⟨vertices_394, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_962, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_194, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_692, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_692, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_708, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![1, 5, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_196, (by decide +kernel)⟩ ⟨vertices_708, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_836, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![1, 5, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_324, (by decide +kernel)⟩ ⟨vertices_836, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_248, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![2, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_248, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_936, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .oneRow ![2, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_168, (by decide +kernel)⟩ ⟨vertices_936, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0040

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m14e10q0_0041.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0041

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_403 : Finset (Fin 10) := literalFinset [0, 1, 4, 7, 8] (by decide +kernel)
noncomputable def vertices_803 : Finset (Fin 10) := literalFinset [0, 1, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_707 : Finset (Fin 10) := literalFinset [0, 1, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_309 : Finset (Fin 10) := literalFinset [0, 2, 4, 5, 8] (by decide +kernel)
noncomputable def vertices_217 : Finset (Fin 10) := literalFinset [0, 3, 4, 6, 7] (by decide +kernel)
noncomputable def vertices_625 : Finset (Fin 10) := literalFinset [0, 4, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_782 : Finset (Fin 10) := literalFinset [1, 2, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_394 : Finset (Fin 10) := literalFinset [1, 3, 7, 8] (by decide +kernel)
noncomputable def vertices_650 : Finset (Fin 10) := literalFinset [1, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_124 : Finset (Fin 10) := literalFinset [2, 3, 4, 5, 6] (by decide +kernel)
noncomputable def vertices_284 : Finset (Fin 10) := literalFinset [2, 3, 4, 8] (by decide +kernel)
noncomputable def vertices_716 : Finset (Fin 10) := literalFinset [2, 3, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_868 : Finset (Fin 10) := literalFinset [2, 5, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_408 : Finset (Fin 10) := literalFinset [3, 4, 7, 8] (by decide +kernel)
noncomputable def vertices_131 : Finset (Fin 10) := literalFinset [0, 1, 7] (by decide +kernel)
noncomputable def vertices_259 : Finset (Fin 10) := literalFinset [0, 1, 8] (by decide +kernel)
noncomputable def vertices_515 : Finset (Fin 10) := literalFinset [0, 1, 9] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_145 : Finset (Fin 10) := literalFinset [0, 4, 7] (by decide +kernel)
noncomputable def vertices_273 : Finset (Fin 10) := literalFinset [0, 4, 8] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_545 : Finset (Fin 10) := literalFinset [0, 5, 9] (by decide +kernel)
noncomputable def vertices_193 : Finset (Fin 10) := literalFinset [0, 6, 7] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_138 : Finset (Fin 10) := literalFinset [1, 3, 7] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_522 : Finset (Fin 10) := literalFinset [1, 3, 9] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_28 : Finset (Fin 10) := literalFinset [2, 3, 4] (by decide +kernel)
noncomputable def vertices_76 : Finset (Fin 10) := literalFinset [2, 3, 6] (by decide +kernel)
noncomputable def vertices_268 : Finset (Fin 10) := literalFinset [2, 3, 8] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_100 : Finset (Fin 10) := literalFinset [2, 5, 6] (by decide +kernel)
noncomputable def vertices_292 : Finset (Fin 10) := literalFinset [2, 5, 8] (by decide +kernel)
noncomputable def vertices_580 : Finset (Fin 10) := literalFinset [2, 6, 9] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_88 : Finset (Fin 10) := literalFinset [3, 4, 6] (by decide +kernel)
noncomputable def vertices_152 : Finset (Fin 10) := literalFinset [3, 4, 7] (by decide +kernel)
noncomputable def vertices_280 : Finset (Fin 10) := literalFinset [3, 4, 8] (by decide +kernel)
noncomputable def vertices_200 : Finset (Fin 10) := literalFinset [3, 6, 7] (by decide +kernel)
noncomputable def vertices_392 : Finset (Fin 10) := literalFinset [3, 7, 8] (by decide +kernel)
noncomputable def vertices_648 : Finset (Fin 10) := literalFinset [3, 7, 9] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_608 : Finset (Fin 10) := literalFinset [5, 6, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_803, vertices_707, vertices_309, vertices_217, vertices_625, vertices_782, vertices_394, vertices_650, vertices_124, vertices_284, vertices_716, vertices_868, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_49, vertices_81, vertices_145, vertices_273, vertices_289, vertices_545, vertices_193, vertices_577, vertices_138, vertices_266, vertices_522, vertices_386, vertices_642, vertices_770, vertices_28, vertices_76, vertices_268, vertices_524, vertices_52, vertices_276, vertices_100, vertices_292, vertices_580, vertices_772, vertices_88, vertices_152, vertices_280, vertices_200, vertices_392, vertices_648, vertices_112, vertices_400, vertices_608, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_803), (false, vertices_707), (false, vertices_309), (false, vertices_217), (false, vertices_625), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_28), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_100), (true, vertices_580), (true, vertices_772), (true, vertices_280), (true, vertices_392), (true, vertices_648)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 17, 19, 21, 23, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 14 else
  if p.val = (false, vertices_803) then 15 else
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_309) then 18 else
  if p.val = (false, vertices_217) then 20 else
  if p.val = (false, vertices_625) then 22 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_28) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_648) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
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
  frame := ![0, 1, 2, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_782, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_266, (by decide +kernel)⟩ ⟨vertices_782, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 3, 4]
  vertex := 5
  face := Sum.inl ⟨vertices_124, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_28, (by decide +kernel)⟩ ⟨vertices_124, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
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

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 4, 5, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_868, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_100, (by decide +kernel)⟩ ⟨vertices_868, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 3, 2, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_782, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_266, (by decide +kernel)⟩ ⟨vertices_782, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_394, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 2, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_138, (by decide +kernel)⟩ ⟨vertices_394, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_650, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 2, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_138, (by decide +kernel)⟩ ⟨vertices_650, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_124, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 2, 3, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_28, (by decide +kernel)⟩ ⟨vertices_124, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_284, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![1, 2, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_28, (by decide +kernel)⟩ ⟨vertices_284, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_716, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![1, 2, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_76, (by decide +kernel)⟩ ⟨vertices_716, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_868, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![1, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_100, (by decide +kernel)⟩ ⟨vertices_868, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_408, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![2, 3, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_152, (by decide +kernel)⟩ ⟨vertices_408, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0041

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m14e10q0_0042.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0042

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_587 : Finset (Fin 10) := literalFinset [0, 1, 3, 6, 9] (by decide +kernel)
noncomputable def vertices_541 : Finset (Fin 10) := literalFinset [0, 2, 3, 4, 9] (by decide +kernel)
noncomputable def vertices_405 : Finset (Fin 10) := literalFinset [0, 2, 4, 7, 8] (by decide +kernel)
noncomputable def vertices_677 : Finset (Fin 10) := literalFinset [0, 2, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_345 : Finset (Fin 10) := literalFinset [0, 3, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_961 : Finset (Fin 10) := literalFinset [0, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_566 : Finset (Fin 10) := literalFinset [1, 2, 4, 5, 9] (by decide +kernel)
noncomputable def vertices_314 : Finset (Fin 10) := literalFinset [1, 3, 4, 5, 8] (by decide +kernel)
noncomputable def vertices_538 : Finset (Fin 10) := literalFinset [1, 3, 4, 9] (by decide +kernel)
noncomputable def vertices_330 : Finset (Fin 10) := literalFinset [1, 3, 6, 8] (by decide +kernel)
noncomputable def vertices_738 : Finset (Fin 10) := literalFinset [1, 5, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_354 : Finset (Fin 10) := literalFinset [1, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_308 : Finset (Fin 10) := literalFinset [2, 4, 5, 8] (by decide +kernel)
noncomputable def vertices_484 : Finset (Fin 10) := literalFinset [2, 5, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_21 : Finset (Fin 10) := literalFinset [0, 2, 4] (by decide +kernel)
noncomputable def vertices_133 : Finset (Fin 10) := literalFinset [0, 2, 7] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_25 : Finset (Fin 10) := literalFinset [0, 3, 4] (by decide +kernel)
noncomputable def vertices_73 : Finset (Fin 10) := literalFinset [0, 3, 6] (by decide +kernel)
noncomputable def vertices_521 : Finset (Fin 10) := literalFinset [0, 3, 9] (by decide +kernel)
noncomputable def vertices_273 : Finset (Fin 10) := literalFinset [0, 4, 8] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_385 : Finset (Fin 10) := literalFinset [0, 7, 8] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_26 : Finset (Fin 10) := literalFinset [1, 3, 4] (by decide +kernel)
noncomputable def vertices_74 : Finset (Fin 10) := literalFinset [1, 3, 6] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_522 : Finset (Fin 10) := literalFinset [1, 3, 9] (by decide +kernel)
noncomputable def vertices_50 : Finset (Fin 10) := literalFinset [1, 4, 5] (by decide +kernel)
noncomputable def vertices_530 : Finset (Fin 10) := literalFinset [1, 4, 9] (by decide +kernel)
noncomputable def vertices_98 : Finset (Fin 10) := literalFinset [1, 5, 6] (by decide +kernel)
noncomputable def vertices_290 : Finset (Fin 10) := literalFinset [1, 5, 8] (by decide +kernel)
noncomputable def vertices_546 : Finset (Fin 10) := literalFinset [1, 5, 9] (by decide +kernel)
noncomputable def vertices_322 : Finset (Fin 10) := literalFinset [1, 6, 8] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_532 : Finset (Fin 10) := literalFinset [2, 4, 9] (by decide +kernel)
noncomputable def vertices_164 : Finset (Fin 10) := literalFinset [2, 5, 7] (by decide +kernel)
noncomputable def vertices_292 : Finset (Fin 10) := literalFinset [2, 5, 8] (by decide +kernel)
noncomputable def vertices_548 : Finset (Fin 10) := literalFinset [2, 5, 9] (by decide +kernel)
noncomputable def vertices_388 : Finset (Fin 10) := literalFinset [2, 7, 8] (by decide +kernel)
noncomputable def vertices_280 : Finset (Fin 10) := literalFinset [3, 4, 8] (by decide +kernel)
noncomputable def vertices_536 : Finset (Fin 10) := literalFinset [3, 4, 9] (by decide +kernel)
noncomputable def vertices_328 : Finset (Fin 10) := literalFinset [3, 6, 8] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_224 : Finset (Fin 10) := literalFinset [5, 6, 7] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_541, vertices_405, vertices_677, vertices_345, vertices_961, vertices_566, vertices_314, vertices_538, vertices_330, vertices_738, vertices_354, vertices_308, vertices_484] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_517, vertices_25, vertices_73, vertices_521, vertices_273, vertices_321, vertices_577, vertices_385, vertices_641, vertices_26, vertices_74, vertices_266, vertices_522, vertices_50, vertices_530, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_52, vertices_276, vertices_532, vertices_164, vertices_292, vertices_548, vertices_388, vertices_280, vertices_536, vertices_328, vertices_304, vertices_224, vertices_352, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_541), (false, vertices_405), (false, vertices_677), (false, vertices_345), (false, vertices_961), (true, vertices_26), (true, vertices_266), (true, vertices_50), (true, vertices_530), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_322), (true, vertices_52), (true, vertices_292), (true, vertices_304), (true, vertices_224), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 15, 19, 21, 22, 23, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 14 else
  if p.val = (false, vertices_541) then 16 else
  if p.val = (false, vertices_405) then 17 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_345) then 20 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_352) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
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
  frame := ![0, 2, 3, 4]
  vertex := 7
  face := Sum.inl ⟨vertices_314, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_26, (by decide +kernel)⟩ ⟨vertices_314, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 3, 4]
  vertex := 8
  face := Sum.inl ⟨vertices_566, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_50, (by decide +kernel)⟩ ⟨vertices_566, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 4, 5, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_738, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_98, (by decide +kernel)⟩ ⟨vertices_738, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 4, 5, 6]
  vertex := 7
  face := Sum.inl ⟨vertices_484, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_164, (by decide +kernel)⟩ ⟨vertices_484, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![2, 3, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_566, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 3, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_50, (by decide +kernel)⟩ ⟨vertices_566, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_314, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 2, 3, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_26, (by decide +kernel)⟩ ⟨vertices_314, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_538, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 2, 3, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_26, (by decide +kernel)⟩ ⟨vertices_538, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_330, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 2, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_74, (by decide +kernel)⟩ ⟨vertices_330, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_738, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![0, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_98, (by decide +kernel)⟩ ⟨vertices_738, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_354, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![0, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_98, (by decide +kernel)⟩ ⟨vertices_354, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_308, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![1, 3, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_308, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_484, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .oneRow ![1, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_164, (by decide +kernel)⟩ ⟨vertices_484, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0042

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m14e10q0_0045.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0045

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_155 : Finset (Fin 10) := literalFinset [0, 1, 3, 4, 7] (by decide +kernel)
noncomputable def vertices_51 : Finset (Fin 10) := literalFinset [0, 1, 4, 5] (by decide +kernel)
noncomputable def vertices_419 : Finset (Fin 10) := literalFinset [0, 1, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_61 : Finset (Fin 10) := literalFinset [0, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_205 : Finset (Fin 10) := literalFinset [0, 2, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_357 : Finset (Fin 10) := literalFinset [0, 2, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_961 : Finset (Fin 10) := literalFinset [0, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_566 : Finset (Fin 10) := literalFinset [1, 2, 4, 5, 9] (by decide +kernel)
noncomputable def vertices_914 : Finset (Fin 10) := literalFinset [1, 4, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_866 : Finset (Fin 10) := literalFinset [1, 5, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_604 : Finset (Fin 10) := literalFinset [2, 3, 4, 6, 9] (by decide +kernel)
noncomputable def vertices_612 : Finset (Fin 10) := literalFinset [2, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_664 : Finset (Fin 10) := literalFinset [3, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_712 : Finset (Fin 10) := literalFinset [3, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_19 : Finset (Fin 10) := literalFinset [0, 1, 4] (by decide +kernel)
noncomputable def vertices_35 : Finset (Fin 10) := literalFinset [0, 1, 5] (by decide +kernel)
noncomputable def vertices_131 : Finset (Fin 10) := literalFinset [0, 1, 7] (by decide +kernel)
noncomputable def vertices_13 : Finset (Fin 10) := literalFinset [0, 2, 3] (by decide +kernel)
noncomputable def vertices_37 : Finset (Fin 10) := literalFinset [0, 2, 5] (by decide +kernel)
noncomputable def vertices_69 : Finset (Fin 10) := literalFinset [0, 2, 6] (by decide +kernel)
noncomputable def vertices_25 : Finset (Fin 10) := literalFinset [0, 3, 4] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_193 : Finset (Fin 10) := literalFinset [0, 6, 7] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_385 : Finset (Fin 10) := literalFinset [0, 7, 8] (by decide +kernel)
noncomputable def vertices_50 : Finset (Fin 10) := literalFinset [1, 4, 5] (by decide +kernel)
noncomputable def vertices_146 : Finset (Fin 10) := literalFinset [1, 4, 7] (by decide +kernel)
noncomputable def vertices_530 : Finset (Fin 10) := literalFinset [1, 4, 9] (by decide +kernel)
noncomputable def vertices_290 : Finset (Fin 10) := literalFinset [1, 5, 8] (by decide +kernel)
noncomputable def vertices_546 : Finset (Fin 10) := literalFinset [1, 5, 9] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_28 : Finset (Fin 10) := literalFinset [2, 3, 4] (by decide +kernel)
noncomputable def vertices_76 : Finset (Fin 10) := literalFinset [2, 3, 6] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_532 : Finset (Fin 10) := literalFinset [2, 4, 9] (by decide +kernel)
noncomputable def vertices_100 : Finset (Fin 10) := literalFinset [2, 5, 6] (by decide +kernel)
noncomputable def vertices_548 : Finset (Fin 10) := literalFinset [2, 5, 9] (by decide +kernel)
noncomputable def vertices_580 : Finset (Fin 10) := literalFinset [2, 6, 9] (by decide +kernel)
noncomputable def vertices_152 : Finset (Fin 10) := literalFinset [3, 4, 7] (by decide +kernel)
noncomputable def vertices_536 : Finset (Fin 10) := literalFinset [3, 4, 9] (by decide +kernel)
noncomputable def vertices_200 : Finset (Fin 10) := literalFinset [3, 6, 7] (by decide +kernel)
noncomputable def vertices_584 : Finset (Fin 10) := literalFinset [3, 6, 9] (by decide +kernel)
noncomputable def vertices_648 : Finset (Fin 10) := literalFinset [3, 7, 9] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_608 : Finset (Fin 10) := literalFinset [5, 6, 9] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_155, vertices_51, vertices_419, vertices_61, vertices_205, vertices_357, vertices_961, vertices_566, vertices_914, vertices_866, vertices_604, vertices_612, vertices_664, vertices_712] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_131, vertices_13, vertices_37, vertices_69, vertices_25, vertices_137, vertices_49, vertices_289, vertices_193, vertices_321, vertices_385, vertices_50, vertices_146, vertices_530, vertices_290, vertices_546, vertices_386, vertices_770, vertices_28, vertices_76, vertices_52, vertices_532, vertices_100, vertices_548, vertices_580, vertices_152, vertices_536, vertices_200, vertices_584, vertices_648, vertices_656, vertices_352, vertices_608, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_155), (false, vertices_51), (false, vertices_419), (false, vertices_61), (false, vertices_205), (false, vertices_357), (false, vertices_961), (true, vertices_530), (true, vertices_546), (true, vertices_770), (true, vertices_532), (true, vertices_548), (true, vertices_580), (true, vertices_536), (true, vertices_584), (true, vertices_648), (true, vertices_656), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![12, 15, 19, 20, 21, 22, 24, 25, 26]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_155) then 13 else
  if p.val = (false, vertices_51) then 0 else
  if p.val = (false, vertices_419) then 14 else
  if p.val = (false, vertices_61) then 16 else
  if p.val = (false, vertices_205) then 17 else
  if p.val = (false, vertices_357) then 18 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_580) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_584) then 8 else
  if p.val = (true, vertices_648) then 9 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_608) then 11 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_51), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_155), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_61), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 19 => Sum.inl 2
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
  frameSize := 4
  frame := ![0, 3, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_914, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_146, (by decide +kernel)⟩ ⟨vertices_914, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 4, 5, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_866, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_290, (by decide +kernel)⟩ ⟨vertices_866, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 3, 4]
  vertex := 8
  face := Sum.inl ⟨vertices_566, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_50, (by decide +kernel)⟩ ⟨vertices_566, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 3, 5]
  vertex := 8
  face := Sum.inl ⟨vertices_604, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_28, (by decide +kernel)⟩ ⟨vertices_604, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![6, 7, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_566, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 3, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_50, (by decide +kernel)⟩ ⟨vertices_566, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_914, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 3, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_146, (by decide +kernel)⟩ ⟨vertices_914, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_866, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_290, (by decide +kernel)⟩ ⟨vertices_866, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_604, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_28, (by decide +kernel)⟩ ⟨vertices_604, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_612, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![1, 4, 5, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_100, (by decide +kernel)⟩ ⟨vertices_612, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_664, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![2, 3, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_152, (by decide +kernel)⟩ ⟨vertices_664, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_712, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![2, 5, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_200, (by decide +kernel)⟩ ⟨vertices_712, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0045

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m14e10q0_0046.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0046

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_775 : Finset (Fin 10) := literalFinset [0, 1, 2, 8, 9] (by decide +kernel)
noncomputable def vertices_653 : Finset (Fin 10) := literalFinset [0, 2, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_421 : Finset (Fin 10) := literalFinset [0, 2, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_601 : Finset (Fin 10) := literalFinset [0, 3, 4, 6, 9] (by decide +kernel)
noncomputable def vertices_233 : Finset (Fin 10) := literalFinset [0, 3, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_865 : Finset (Fin 10) := literalFinset [0, 5, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_662 : Finset (Fin 10) := literalFinset [1, 2, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_390 : Finset (Fin 10) := literalFinset [1, 2, 7, 8] (by decide +kernel)
noncomputable def vertices_186 : Finset (Fin 10) := literalFinset [1, 3, 4, 5, 7] (by decide +kernel)
noncomputable def vertices_306 : Finset (Fin 10) := literalFinset [1, 4, 5, 8] (by decide +kernel)
noncomputable def vertices_850 : Finset (Fin 10) := literalFinset [1, 4, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_418 : Finset (Fin 10) := literalFinset [1, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_376 : Finset (Fin 10) := literalFinset [3, 4, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_664 : Finset (Fin 10) := literalFinset [3, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_133 : Finset (Fin 10) := literalFinset [0, 2, 7] (by decide +kernel)
noncomputable def vertices_261 : Finset (Fin 10) := literalFinset [0, 2, 8] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_73 : Finset (Fin 10) := literalFinset [0, 3, 6] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_521 : Finset (Fin 10) := literalFinset [0, 3, 9] (by decide +kernel)
noncomputable def vertices_97 : Finset (Fin 10) := literalFinset [0, 5, 6] (by decide +kernel)
noncomputable def vertices_161 : Finset (Fin 10) := literalFinset [0, 5, 7] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_134 : Finset (Fin 10) := literalFinset [1, 2, 7] (by decide +kernel)
noncomputable def vertices_262 : Finset (Fin 10) := literalFinset [1, 2, 8] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_50 : Finset (Fin 10) := literalFinset [1, 4, 5] (by decide +kernel)
noncomputable def vertices_146 : Finset (Fin 10) := literalFinset [1, 4, 7] (by decide +kernel)
noncomputable def vertices_274 : Finset (Fin 10) := literalFinset [1, 4, 8] (by decide +kernel)
noncomputable def vertices_530 : Finset (Fin 10) := literalFinset [1, 4, 9] (by decide +kernel)
noncomputable def vertices_162 : Finset (Fin 10) := literalFinset [1, 5, 7] (by decide +kernel)
noncomputable def vertices_290 : Finset (Fin 10) := literalFinset [1, 5, 8] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_388 : Finset (Fin 10) := literalFinset [2, 7, 8] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_56 : Finset (Fin 10) := literalFinset [3, 4, 5] (by decide +kernel)
noncomputable def vertices_88 : Finset (Fin 10) := literalFinset [3, 4, 6] (by decide +kernel)
noncomputable def vertices_152 : Finset (Fin 10) := literalFinset [3, 4, 7] (by decide +kernel)
noncomputable def vertices_536 : Finset (Fin 10) := literalFinset [3, 4, 9] (by decide +kernel)
noncomputable def vertices_104 : Finset (Fin 10) := literalFinset [3, 5, 6] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_648 : Finset (Fin 10) := literalFinset [3, 7, 9] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_653, vertices_421, vertices_601, vertices_233, vertices_865, vertices_662, vertices_390, vertices_186, vertices_306, vertices_850, vertices_418, vertices_376, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_521, vertices_97, vertices_161, vertices_289, vertices_577, vertices_769, vertices_134, vertices_262, vertices_518, vertices_50, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_386, vertices_770, vertices_388, vertices_644, vertices_56, vertices_88, vertices_152, vertices_536, vertices_104, vertices_168, vertices_648, vertices_304, vertices_336, vertices_592, vertices_656, vertices_352, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_653), (false, vertices_421), (false, vertices_601), (false, vertices_233), (false, vertices_865), (true, vertices_134), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_290), (true, vertices_386), (true, vertices_56), (true, vertices_152), (true, vertices_304), (true, vertices_336), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 15, 18, 21, 22, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 14 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_421) then 17 else
  if p.val = (false, vertices_601) then 19 else
  if p.val = (false, vertices_233) then 20 else
  if p.val = (false, vertices_865) then 23 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_656) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
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
  frame := ![0, 1, 3, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_662, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_134, (by decide +kernel)⟩ ⟨vertices_662, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 4]
  vertex := 6
  face := Sum.inl ⟨vertices_186, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_50, (by decide +kernel)⟩ ⟨vertices_186, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 3, 5, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_850, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_274, (by decide +kernel)⟩ ⟨vertices_850, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
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

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![1, 6, 0, 2]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_662, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_134, (by decide +kernel)⟩ ⟨vertices_662, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_390, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 1, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_134, (by decide +kernel)⟩ ⟨vertices_390, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_186, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 2, 3, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_50, (by decide +kernel)⟩ ⟨vertices_186, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_306, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 3, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_50, (by decide +kernel)⟩ ⟨vertices_306, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_850, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![0, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_274, (by decide +kernel)⟩ ⟨vertices_850, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_418, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![0, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_162, (by decide +kernel)⟩ ⟨vertices_418, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_376, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![2, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_376, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_664, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![2, 3, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_152, (by decide +kernel)⟩ ⟨vertices_664, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0046

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m14e10q0_0051.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0051

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_551 : Finset (Fin 10) := literalFinset [0, 1, 2, 5, 9] (by decide +kernel)
noncomputable def vertices_539 : Finset (Fin 10) := literalFinset [0, 1, 3, 4, 9] (by decide +kernel)
noncomputable def vertices_211 : Finset (Fin 10) := literalFinset [0, 1, 4, 6, 7] (by decide +kernel)
noncomputable def vertices_163 : Finset (Fin 10) := literalFinset [0, 1, 5, 7] (by decide +kernel)
noncomputable def vertices_93 : Finset (Fin 10) := literalFinset [0, 2, 3, 4, 6] (by decide +kernel)
noncomputable def vertices_781 : Finset (Fin 10) := literalFinset [0, 2, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_229 : Finset (Fin 10) := literalFinset [0, 2, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_690 : Finset (Fin 10) := literalFinset [1, 4, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_364 : Finset (Fin 10) := literalFinset [2, 3, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_804 : Finset (Fin 10) := literalFinset [2, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_344 : Finset (Fin 10) := literalFinset [3, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_920 : Finset (Fin 10) := literalFinset [3, 4, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_464 : Finset (Fin 10) := literalFinset [4, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_992 : Finset (Fin 10) := literalFinset [5, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_19 : Finset (Fin 10) := literalFinset [0, 1, 4] (by decide +kernel)
noncomputable def vertices_35 : Finset (Fin 10) := literalFinset [0, 1, 5] (by decide +kernel)
noncomputable def vertices_131 : Finset (Fin 10) := literalFinset [0, 1, 7] (by decide +kernel)
noncomputable def vertices_515 : Finset (Fin 10) := literalFinset [0, 1, 9] (by decide +kernel)
noncomputable def vertices_13 : Finset (Fin 10) := literalFinset [0, 2, 3] (by decide +kernel)
noncomputable def vertices_37 : Finset (Fin 10) := literalFinset [0, 2, 5] (by decide +kernel)
noncomputable def vertices_69 : Finset (Fin 10) := literalFinset [0, 2, 6] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_25 : Finset (Fin 10) := literalFinset [0, 3, 4] (by decide +kernel)
noncomputable def vertices_521 : Finset (Fin 10) := literalFinset [0, 3, 9] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_161 : Finset (Fin 10) := literalFinset [0, 5, 7] (by decide +kernel)
noncomputable def vertices_193 : Finset (Fin 10) := literalFinset [0, 6, 7] (by decide +kernel)
noncomputable def vertices_146 : Finset (Fin 10) := literalFinset [1, 4, 7] (by decide +kernel)
noncomputable def vertices_530 : Finset (Fin 10) := literalFinset [1, 4, 9] (by decide +kernel)
noncomputable def vertices_162 : Finset (Fin 10) := literalFinset [1, 5, 7] (by decide +kernel)
noncomputable def vertices_546 : Finset (Fin 10) := literalFinset [1, 5, 9] (by decide +kernel)
noncomputable def vertices_76 : Finset (Fin 10) := literalFinset [2, 3, 6] (by decide +kernel)
noncomputable def vertices_268 : Finset (Fin 10) := literalFinset [2, 3, 8] (by decide +kernel)
noncomputable def vertices_100 : Finset (Fin 10) := literalFinset [2, 5, 6] (by decide +kernel)
noncomputable def vertices_292 : Finset (Fin 10) := literalFinset [2, 5, 8] (by decide +kernel)
noncomputable def vertices_548 : Finset (Fin 10) := literalFinset [2, 5, 9] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_88 : Finset (Fin 10) := literalFinset [3, 4, 6] (by decide +kernel)
noncomputable def vertices_280 : Finset (Fin 10) := literalFinset [3, 4, 8] (by decide +kernel)
noncomputable def vertices_536 : Finset (Fin 10) := literalFinset [3, 4, 9] (by decide +kernel)
noncomputable def vertices_328 : Finset (Fin 10) := literalFinset [3, 6, 8] (by decide +kernel)
noncomputable def vertices_776 : Finset (Fin 10) := literalFinset [3, 8, 9] (by decide +kernel)
noncomputable def vertices_208 : Finset (Fin 10) := literalFinset [4, 6, 7] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_224 : Finset (Fin 10) := literalFinset [5, 6, 7] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_551, vertices_539, vertices_211, vertices_163, vertices_93, vertices_781, vertices_229, vertices_690, vertices_364, vertices_804, vertices_344, vertices_920, vertices_464, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_131, vertices_515, vertices_13, vertices_37, vertices_69, vertices_517, vertices_25, vertices_521, vertices_81, vertices_161, vertices_193, vertices_146, vertices_530, vertices_162, vertices_546, vertices_76, vertices_268, vertices_100, vertices_292, vertices_548, vertices_772, vertices_88, vertices_280, vertices_536, vertices_328, vertices_776, vertices_208, vertices_336, vertices_400, vertices_656, vertices_224, vertices_352, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_551), (false, vertices_539), (false, vertices_211), (false, vertices_163), (false, vertices_93), (false, vertices_781), (false, vertices_229), (true, vertices_292), (true, vertices_280), (true, vertices_328), (true, vertices_336), (true, vertices_400), (true, vertices_656), (true, vertices_352), (true, vertices_672), (true, vertices_800), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![12, 16, 20, 21, 22, 23, 24, 25, 26]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_551) then 13 else
  if p.val = (false, vertices_539) then 14 else
  if p.val = (false, vertices_211) then 15 else
  if p.val = (false, vertices_163) then 0 else
  if p.val = (false, vertices_93) then 17 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_229) then 19 else
  if p.val = (true, vertices_292) then 1 else
  if p.val = (true, vertices_280) then 2 else
  if p.val = (true, vertices_328) then 3 else
  if p.val = (true, vertices_336) then 4 else
  if p.val = (true, vertices_400) then 5 else
  if p.val = (true, vertices_656) then 6 else
  if p.val = (true, vertices_352) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_163), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
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
  frame := ![0, 3, 4, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_690, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_146, (by decide +kernel)⟩ ⟨vertices_690, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
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
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_76, (by decide +kernel)⟩ ⟨vertices_364, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![2, 3, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_920, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_280, (by decide +kernel)⟩ ⟨vertices_920, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
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

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_690, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_146, (by decide +kernel)⟩ ⟨vertices_690, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_364, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![1, 2, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_76, (by decide +kernel)⟩ ⟨vertices_364, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_804, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![1, 4, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_292, (by decide +kernel)⟩ ⟨vertices_804, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_344, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![2, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_88, (by decide +kernel)⟩ ⟨vertices_344, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_920, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![2, 3, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_280, (by decide +kernel)⟩ ⟨vertices_920, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_464, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![3, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_208, (by decide +kernel)⟩ ⟨vertices_464, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0051

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m14e10q0_0052.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0052

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_779 : Finset (Fin 10) := literalFinset [0, 1, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_589 : Finset (Fin 10) := literalFinset [0, 2, 3, 6, 9] (by decide +kernel)
noncomputable def vertices_117 : Finset (Fin 10) := literalFinset [0, 2, 4, 5, 6] (by decide +kernel)
noncomputable def vertices_805 : Finset (Fin 10) := literalFinset [0, 2, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_345 : Finset (Fin 10) := literalFinset [0, 3, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_433 : Finset (Fin 10) := literalFinset [0, 4, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_678 : Finset (Fin 10) := literalFinset [1, 2, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_426 : Finset (Fin 10) := literalFinset [1, 3, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_714 : Finset (Fin 10) := literalFinset [1, 3, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_802 : Finset (Fin 10) := literalFinset [1, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_180 : Finset (Fin 10) := literalFinset [2, 4, 5, 7] (by decide +kernel)
noncomputable def vertices_724 : Finset (Fin 10) := literalFinset [2, 4, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_456 : Finset (Fin 10) := literalFinset [3, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_464 : Finset (Fin 10) := literalFinset [4, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_37 : Finset (Fin 10) := literalFinset [0, 2, 5] (by decide +kernel)
noncomputable def vertices_69 : Finset (Fin 10) := literalFinset [0, 2, 6] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_73 : Finset (Fin 10) := literalFinset [0, 3, 6] (by decide +kernel)
noncomputable def vertices_265 : Finset (Fin 10) := literalFinset [0, 3, 8] (by decide +kernel)
noncomputable def vertices_521 : Finset (Fin 10) := literalFinset [0, 3, 9] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_273 : Finset (Fin 10) := literalFinset [0, 4, 8] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_138 : Finset (Fin 10) := literalFinset [1, 3, 7] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_522 : Finset (Fin 10) := literalFinset [1, 3, 9] (by decide +kernel)
noncomputable def vertices_162 : Finset (Fin 10) := literalFinset [1, 5, 7] (by decide +kernel)
noncomputable def vertices_290 : Finset (Fin 10) := literalFinset [1, 5, 8] (by decide +kernel)
noncomputable def vertices_546 : Finset (Fin 10) := literalFinset [1, 5, 9] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_148 : Finset (Fin 10) := literalFinset [2, 4, 7] (by decide +kernel)
noncomputable def vertices_164 : Finset (Fin 10) := literalFinset [2, 5, 7] (by decide +kernel)
noncomputable def vertices_548 : Finset (Fin 10) := literalFinset [2, 5, 9] (by decide +kernel)
noncomputable def vertices_580 : Finset (Fin 10) := literalFinset [2, 6, 9] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_200 : Finset (Fin 10) := literalFinset [3, 6, 7] (by decide +kernel)
noncomputable def vertices_328 : Finset (Fin 10) := literalFinset [3, 6, 8] (by decide +kernel)
noncomputable def vertices_584 : Finset (Fin 10) := literalFinset [3, 6, 9] (by decide +kernel)
noncomputable def vertices_392 : Finset (Fin 10) := literalFinset [3, 7, 8] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_208 : Finset (Fin 10) := literalFinset [4, 6, 7] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_589, vertices_117, vertices_805, vertices_345, vertices_433, vertices_678, vertices_426, vertices_714, vertices_802, vertices_180, vertices_724, vertices_456, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_517, vertices_73, vertices_265, vertices_521, vertices_49, vertices_81, vertices_273, vertices_289, vertices_769, vertices_138, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_52, vertices_84, vertices_148, vertices_164, vertices_548, vertices_580, vertices_644, vertices_200, vertices_328, vertices_584, vertices_392, vertices_176, vertices_208, vertices_336, vertices_400, vertices_416, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_589), (false, vertices_117), (false, vertices_805), (false, vertices_345), (false, vertices_433), (true, vertices_138), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_642), (true, vertices_148), (true, vertices_164), (true, vertices_644), (true, vertices_200), (true, vertices_392), (true, vertices_208), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 15, 19, 21, 23, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_589) then 16 else
  if p.val = (false, vertices_117) then 17 else
  if p.val = (false, vertices_805) then 18 else
  if p.val = (false, vertices_345) then 20 else
  if p.val = (false, vertices_433) then 22 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_448) then 11 else
  if p.val = (true, vertices_704) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
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
  frame := ![0, 2, 4, 6]
  vertex := 7
  face := Sum.inl ⟨vertices_426, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_138, (by decide +kernel)⟩ ⟨vertices_426, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 4, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_678, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_162, (by decide +kernel)⟩ ⟨vertices_678, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 5, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_714, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_138, (by decide +kernel)⟩ ⟨vertices_714, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
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
noncomputable def pivot : Fin 4 → Fin 9 := ![7, 4, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_678, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_162, (by decide +kernel)⟩ ⟨vertices_678, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_426, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 2, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_138, (by decide +kernel)⟩ ⟨vertices_426, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_714, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 2, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_138, (by decide +kernel)⟩ ⟨vertices_714, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_802, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 4, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_290, (by decide +kernel)⟩ ⟨vertices_802, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_180, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![1, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_180, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_724, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![1, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_724, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_456, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![2, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_200, (by decide +kernel)⟩ ⟨vertices_456, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_464, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![3, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_208, (by decide +kernel)⟩ ⟨vertices_464, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0052

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m14e10q0_0054.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0054

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_391 : Finset (Fin 10) := literalFinset [0, 1, 2, 7, 8] (by decide +kernel)
noncomputable def vertices_779 : Finset (Fin 10) := literalFinset [0, 1, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_595 : Finset (Fin 10) := literalFinset [0, 1, 4, 6, 9] (by decide +kernel)
noncomputable def vertices_147 : Finset (Fin 10) := literalFinset [0, 1, 4, 7] (by decide +kernel)
noncomputable def vertices_301 : Finset (Fin 10) := literalFinset [0, 2, 3, 5, 8] (by decide +kernel)
noncomputable def vertices_589 : Finset (Fin 10) := literalFinset [0, 2, 3, 6, 9] (by decide +kernel)
noncomputable def vertices_213 : Finset (Fin 10) := literalFinset [0, 2, 4, 6, 7] (by decide +kernel)
noncomputable def vertices_690 : Finset (Fin 10) := literalFinset [1, 4, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_898 : Finset (Fin 10) := literalFinset [1, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_108 : Finset (Fin 10) := literalFinset [2, 3, 5, 6] (by decide +kernel)
noncomputable def vertices_484 : Finset (Fin 10) := literalFinset [2, 5, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_632 : Finset (Fin 10) := literalFinset [3, 4, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_936 : Finset (Fin 10) := literalFinset [3, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_240 : Finset (Fin 10) := literalFinset [4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_19 : Finset (Fin 10) := literalFinset [0, 1, 4] (by decide +kernel)
noncomputable def vertices_131 : Finset (Fin 10) := literalFinset [0, 1, 7] (by decide +kernel)
noncomputable def vertices_259 : Finset (Fin 10) := literalFinset [0, 1, 8] (by decide +kernel)
noncomputable def vertices_515 : Finset (Fin 10) := literalFinset [0, 1, 9] (by decide +kernel)
noncomputable def vertices_13 : Finset (Fin 10) := literalFinset [0, 2, 3] (by decide +kernel)
noncomputable def vertices_69 : Finset (Fin 10) := literalFinset [0, 2, 6] (by decide +kernel)
noncomputable def vertices_133 : Finset (Fin 10) := literalFinset [0, 2, 7] (by decide +kernel)
noncomputable def vertices_261 : Finset (Fin 10) := literalFinset [0, 2, 8] (by decide +kernel)
noncomputable def vertices_265 : Finset (Fin 10) := literalFinset [0, 3, 8] (by decide +kernel)
noncomputable def vertices_521 : Finset (Fin 10) := literalFinset [0, 3, 9] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_145 : Finset (Fin 10) := literalFinset [0, 4, 7] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_146 : Finset (Fin 10) := literalFinset [1, 4, 7] (by decide +kernel)
noncomputable def vertices_530 : Finset (Fin 10) := literalFinset [1, 4, 9] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_76 : Finset (Fin 10) := literalFinset [2, 3, 6] (by decide +kernel)
noncomputable def vertices_100 : Finset (Fin 10) := literalFinset [2, 5, 6] (by decide +kernel)
noncomputable def vertices_292 : Finset (Fin 10) := literalFinset [2, 5, 8] (by decide +kernel)
noncomputable def vertices_196 : Finset (Fin 10) := literalFinset [2, 6, 7] (by decide +kernel)
noncomputable def vertices_388 : Finset (Fin 10) := literalFinset [2, 7, 8] (by decide +kernel)
noncomputable def vertices_104 : Finset (Fin 10) := literalFinset [3, 5, 6] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_552 : Finset (Fin 10) := literalFinset [3, 5, 9] (by decide +kernel)
noncomputable def vertices_584 : Finset (Fin 10) := literalFinset [3, 6, 9] (by decide +kernel)
noncomputable def vertices_776 : Finset (Fin 10) := literalFinset [3, 8, 9] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_208 : Finset (Fin 10) := literalFinset [4, 6, 7] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_224 : Finset (Fin 10) := literalFinset [5, 6, 7] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_779, vertices_595, vertices_147, vertices_301, vertices_589, vertices_213, vertices_690, vertices_898, vertices_108, vertices_484, vertices_632, vertices_936, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_13, vertices_69, vertices_133, vertices_261, vertices_265, vertices_521, vertices_81, vertices_145, vertices_577, vertices_146, vertices_530, vertices_386, vertices_642, vertices_770, vertices_44, vertices_76, vertices_100, vertices_292, vertices_196, vertices_388, vertices_104, vertices_296, vertices_552, vertices_584, vertices_776, vertices_112, vertices_176, vertices_560, vertices_208, vertices_592, vertices_224, vertices_416, vertices_672, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_779), (false, vertices_595), (false, vertices_147), (false, vertices_301), (false, vertices_589), (false, vertices_213), (true, vertices_642), (true, vertices_100), (true, vertices_104), (true, vertices_552), (true, vertices_112), (true, vertices_176), (true, vertices_560), (true, vertices_224), (true, vertices_416), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![12, 16, 20, 21, 22, 23, 24, 25, 26]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 13 else
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_595) then 15 else
  if p.val = (false, vertices_147) then 0 else
  if p.val = (false, vertices_301) then 17 else
  if p.val = (false, vertices_589) then 18 else
  if p.val = (false, vertices_213) then 19 else
  if p.val = (true, vertices_642) then 1 else
  if p.val = (true, vertices_100) then 2 else
  if p.val = (true, vertices_104) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_112) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_147), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
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
  frame := ![0, 3, 4, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_690, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_146, (by decide +kernel)⟩ ⟨vertices_690, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 4, 5, 6]
  vertex := 7
  face := Sum.inl ⟨vertices_484, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_100, (by decide +kernel)⟩ ⟨vertices_484, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
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
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_104, (by decide +kernel)⟩ ⟨vertices_632, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
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
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_296, (by decide +kernel)⟩ ⟨vertices_936, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 1, 3, 2]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_690, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_146, (by decide +kernel)⟩ ⟨vertices_690, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_898, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 6, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_386, (by decide +kernel)⟩ ⟨vertices_898, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_108, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![1, 2, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_108, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_484, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_100, (by decide +kernel)⟩ ⟨vertices_484, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_632, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![2, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_104, (by decide +kernel)⟩ ⟨vertices_632, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_936, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![2, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_296, (by decide +kernel)⟩ ⟨vertices_936, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0054

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m14e10q0_0057.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0057

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_775 : Finset (Fin 10) := literalFinset [0, 1, 2, 8, 9] (by decide +kernel)
noncomputable def vertices_539 : Finset (Fin 10) := literalFinset [0, 1, 3, 4, 9] (by decide +kernel)
noncomputable def vertices_179 : Finset (Fin 10) := literalFinset [0, 1, 4, 5, 7] (by decide +kernel)
noncomputable def vertices_387 : Finset (Fin 10) := literalFinset [0, 1, 7, 8] (by decide +kernel)
noncomputable def vertices_61 : Finset (Fin 10) := literalFinset [0, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_589 : Finset (Fin 10) := literalFinset [0, 2, 3, 6, 9] (by decide +kernel)
noncomputable def vertices_421 : Finset (Fin 10) := literalFinset [0, 2, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_658 : Finset (Fin 10) := literalFinset [1, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_962 : Finset (Fin 10) := literalFinset [1, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_108 : Finset (Fin 10) := literalFinset [2, 3, 5, 6] (by decide +kernel)
noncomputable def vertices_868 : Finset (Fin 10) := literalFinset [2, 5, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_120 : Finset (Fin 10) := literalFinset [3, 4, 5, 6] (by decide +kernel)
noncomputable def vertices_728 : Finset (Fin 10) := literalFinset [3, 4, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_496 : Finset (Fin 10) := literalFinset [4, 5, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_19 : Finset (Fin 10) := literalFinset [0, 1, 4] (by decide +kernel)
noncomputable def vertices_131 : Finset (Fin 10) := literalFinset [0, 1, 7] (by decide +kernel)
noncomputable def vertices_259 : Finset (Fin 10) := literalFinset [0, 1, 8] (by decide +kernel)
noncomputable def vertices_515 : Finset (Fin 10) := literalFinset [0, 1, 9] (by decide +kernel)
noncomputable def vertices_13 : Finset (Fin 10) := literalFinset [0, 2, 3] (by decide +kernel)
noncomputable def vertices_37 : Finset (Fin 10) := literalFinset [0, 2, 5] (by decide +kernel)
noncomputable def vertices_261 : Finset (Fin 10) := literalFinset [0, 2, 8] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_25 : Finset (Fin 10) := literalFinset [0, 3, 4] (by decide +kernel)
noncomputable def vertices_521 : Finset (Fin 10) := literalFinset [0, 3, 9] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_161 : Finset (Fin 10) := literalFinset [0, 5, 7] (by decide +kernel)
noncomputable def vertices_385 : Finset (Fin 10) := literalFinset [0, 7, 8] (by decide +kernel)
noncomputable def vertices_146 : Finset (Fin 10) := literalFinset [1, 4, 7] (by decide +kernel)
noncomputable def vertices_530 : Finset (Fin 10) := literalFinset [1, 4, 9] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_76 : Finset (Fin 10) := literalFinset [2, 3, 6] (by decide +kernel)
noncomputable def vertices_100 : Finset (Fin 10) := literalFinset [2, 5, 6] (by decide +kernel)
noncomputable def vertices_292 : Finset (Fin 10) := literalFinset [2, 5, 8] (by decide +kernel)
noncomputable def vertices_580 : Finset (Fin 10) := literalFinset [2, 6, 9] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_56 : Finset (Fin 10) := literalFinset [3, 4, 5] (by decide +kernel)
noncomputable def vertices_88 : Finset (Fin 10) := literalFinset [3, 4, 6] (by decide +kernel)
noncomputable def vertices_536 : Finset (Fin 10) := literalFinset [3, 4, 9] (by decide +kernel)
noncomputable def vertices_104 : Finset (Fin 10) := literalFinset [3, 5, 6] (by decide +kernel)
noncomputable def vertices_584 : Finset (Fin 10) := literalFinset [3, 6, 9] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_208 : Finset (Fin 10) := literalFinset [4, 6, 7] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_539, vertices_179, vertices_387, vertices_61, vertices_589, vertices_421, vertices_658, vertices_962, vertices_108, vertices_868, vertices_120, vertices_728, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_13, vertices_37, vertices_261, vertices_517, vertices_25, vertices_521, vertices_49, vertices_161, vertices_385, vertices_146, vertices_530, vertices_386, vertices_642, vertices_770, vertices_44, vertices_76, vertices_100, vertices_292, vertices_580, vertices_772, vertices_56, vertices_88, vertices_536, vertices_104, vertices_584, vertices_112, vertices_176, vertices_208, vertices_656, vertices_352, vertices_416, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_539), (false, vertices_179), (false, vertices_387), (false, vertices_61), (false, vertices_589), (false, vertices_421), (true, vertices_642), (true, vertices_100), (true, vertices_88), (true, vertices_104), (true, vertices_112), (true, vertices_208), (true, vertices_656), (true, vertices_352), (true, vertices_448), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![12, 16, 20, 21, 22, 23, 24, 25, 26]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 13 else
  if p.val = (false, vertices_539) then 14 else
  if p.val = (false, vertices_179) then 15 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_61) then 17 else
  if p.val = (false, vertices_589) then 18 else
  if p.val = (false, vertices_421) then 19 else
  if p.val = (true, vertices_642) then 1 else
  if p.val = (true, vertices_100) then 2 else
  if p.val = (true, vertices_88) then 3 else
  if p.val = (true, vertices_104) then 4 else
  if p.val = (true, vertices_112) then 5 else
  if p.val = (true, vertices_208) then 6 else
  if p.val = (true, vertices_656) then 7 else
  if p.val = (true, vertices_352) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_61), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
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
  frameSize := 4
  frame := ![1, 4, 5, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_868, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_100, (by decide +kernel)⟩ ⟨vertices_868, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![2, 3, 5, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_728, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_88, (by decide +kernel)⟩ ⟨vertices_728, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
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

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_658, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .fundamental ![0, 3, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_146, (by decide +kernel)⟩ ⟨vertices_658, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_962, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_386, (by decide +kernel)⟩ ⟨vertices_962, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_108, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![1, 2, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_108, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_868, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_100, (by decide +kernel)⟩ ⟨vertices_868, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_120, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![2, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_120, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_728, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![2, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_88, (by decide +kernel)⟩ ⟨vertices_728, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_496, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![3, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_496, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0057

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m14e10q0_0058.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0058

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_787 : Finset (Fin 10) := literalFinset [0, 1, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_173 : Finset (Fin 10) := literalFinset [0, 2, 3, 5, 7] (by decide +kernel)
noncomputable def vertices_661 : Finset (Fin 10) := literalFinset [0, 2, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_613 : Finset (Fin 10) := literalFinset [0, 2, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_409 : Finset (Fin 10) := literalFinset [0, 3, 4, 7, 8] (by decide +kernel)
noncomputable def vertices_809 : Finset (Fin 10) := literalFinset [0, 3, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_710 : Finset (Fin 10) := literalFinset [1, 2, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_218 : Finset (Fin 10) := literalFinset [1, 3, 4, 6, 7] (by decide +kernel)
noncomputable def vertices_338 : Finset (Fin 10) := literalFinset [1, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_658 : Finset (Fin 10) := literalFinset [1, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_866 : Finset (Fin 10) := literalFinset [1, 5, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_228 : Finset (Fin 10) := literalFinset [2, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_376 : Finset (Fin 10) := literalFinset [3, 4, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_232 : Finset (Fin 10) := literalFinset [3, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_37 : Finset (Fin 10) := literalFinset [0, 2, 5] (by decide +kernel)
noncomputable def vertices_133 : Finset (Fin 10) := literalFinset [0, 2, 7] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_265 : Finset (Fin 10) := literalFinset [0, 3, 8] (by decide +kernel)
noncomputable def vertices_145 : Finset (Fin 10) := literalFinset [0, 4, 7] (by decide +kernel)
noncomputable def vertices_273 : Finset (Fin 10) := literalFinset [0, 4, 8] (by decide +kernel)
noncomputable def vertices_529 : Finset (Fin 10) := literalFinset [0, 4, 9] (by decide +kernel)
noncomputable def vertices_545 : Finset (Fin 10) := literalFinset [0, 5, 9] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_82 : Finset (Fin 10) := literalFinset [1, 4, 6] (by decide +kernel)
noncomputable def vertices_146 : Finset (Fin 10) := literalFinset [1, 4, 7] (by decide +kernel)
noncomputable def vertices_274 : Finset (Fin 10) := literalFinset [1, 4, 8] (by decide +kernel)
noncomputable def vertices_530 : Finset (Fin 10) := literalFinset [1, 4, 9] (by decide +kernel)
noncomputable def vertices_194 : Finset (Fin 10) := literalFinset [1, 6, 7] (by decide +kernel)
noncomputable def vertices_322 : Finset (Fin 10) := literalFinset [1, 6, 8] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_100 : Finset (Fin 10) := literalFinset [2, 5, 6] (by decide +kernel)
noncomputable def vertices_164 : Finset (Fin 10) := literalFinset [2, 5, 7] (by decide +kernel)
noncomputable def vertices_196 : Finset (Fin 10) := literalFinset [2, 6, 7] (by decide +kernel)
noncomputable def vertices_580 : Finset (Fin 10) := literalFinset [2, 6, 9] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_88 : Finset (Fin 10) := literalFinset [3, 4, 6] (by decide +kernel)
noncomputable def vertices_152 : Finset (Fin 10) := literalFinset [3, 4, 7] (by decide +kernel)
noncomputable def vertices_280 : Finset (Fin 10) := literalFinset [3, 4, 8] (by decide +kernel)
noncomputable def vertices_104 : Finset (Fin 10) := literalFinset [3, 5, 6] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_200 : Finset (Fin 10) := literalFinset [3, 6, 7] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_224 : Finset (Fin 10) := literalFinset [5, 6, 7] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_608 : Finset (Fin 10) := literalFinset [5, 6, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_173, vertices_661, vertices_613, vertices_409, vertices_809, vertices_710, vertices_218, vertices_338, vertices_658, vertices_866, vertices_228, vertices_376, vertices_232] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_517, vertices_41, vertices_137, vertices_265, vertices_145, vertices_273, vertices_529, vertices_545, vertices_769, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_100, vertices_164, vertices_196, vertices_580, vertices_644, vertices_88, vertices_152, vertices_280, vertices_104, vertices_168, vertices_296, vertices_200, vertices_336, vertices_656, vertices_224, vertices_352, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_173), (false, vertices_661), (false, vertices_613), (false, vertices_409), (false, vertices_809), (true, vertices_82), (true, vertices_146), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_642), (true, vertices_196), (true, vertices_88), (true, vertices_104), (true, vertices_200), (true, vertices_336), (true, vertices_224), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 15, 19, 22, 23, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_173) then 16 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_613) then 18 else
  if p.val = (false, vertices_409) then 20 else
  if p.val = (false, vertices_809) then 21 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_352) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
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
  frame := ![0, 1, 5, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_710, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_194, (by decide +kernel)⟩ ⟨vertices_710, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 5]
  vertex := 6
  face := Sum.inl ⟨vertices_218, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_82, (by decide +kernel)⟩ ⟨vertices_218, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 4, 5, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_866, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_322, (by decide +kernel)⟩ ⟨vertices_866, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![2, 3, 4, 5]
  vertex := 7
  face := Sum.inl ⟨vertices_376, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_88, (by decide +kernel)⟩ ⟨vertices_376, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![1, 6, 0, 2]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_710, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_194, (by decide +kernel)⟩ ⟨vertices_710, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_218, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_82, (by decide +kernel)⟩ ⟨vertices_218, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_338, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_82, (by decide +kernel)⟩ ⟨vertices_338, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_658, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 3, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_146, (by decide +kernel)⟩ ⟨vertices_658, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_866, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![0, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_322, (by decide +kernel)⟩ ⟨vertices_866, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_228, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![1, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_100, (by decide +kernel)⟩ ⟨vertices_228, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_376, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![2, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_88, (by decide +kernel)⟩ ⟨vertices_376, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_232, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![2, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_104, (by decide +kernel)⟩ ⟨vertices_232, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0058

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m14e10q0_0063.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0063

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_155 : Finset (Fin 10) := literalFinset [0, 1, 3, 4, 7] (by decide +kernel)
noncomputable def vertices_51 : Finset (Fin 10) := literalFinset [0, 1, 4, 5] (by decide +kernel)
noncomputable def vertices_803 : Finset (Fin 10) := literalFinset [0, 1, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_451 : Finset (Fin 10) := literalFinset [0, 1, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_61 : Finset (Fin 10) := literalFinset [0, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_205 : Finset (Fin 10) := literalFinset [0, 2, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_357 : Finset (Fin 10) := literalFinset [0, 2, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_566 : Finset (Fin 10) := literalFinset [1, 2, 4, 5, 9] (by decide +kernel)
noncomputable def vertices_914 : Finset (Fin 10) := literalFinset [1, 4, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_604 : Finset (Fin 10) := literalFinset [2, 3, 4, 6, 9] (by decide +kernel)
noncomputable def vertices_612 : Finset (Fin 10) := literalFinset [2, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_664 : Finset (Fin 10) := literalFinset [3, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_712 : Finset (Fin 10) := literalFinset [3, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_992 : Finset (Fin 10) := literalFinset [5, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_19 : Finset (Fin 10) := literalFinset [0, 1, 4] (by decide +kernel)
noncomputable def vertices_35 : Finset (Fin 10) := literalFinset [0, 1, 5] (by decide +kernel)
noncomputable def vertices_131 : Finset (Fin 10) := literalFinset [0, 1, 7] (by decide +kernel)
noncomputable def vertices_259 : Finset (Fin 10) := literalFinset [0, 1, 8] (by decide +kernel)
noncomputable def vertices_13 : Finset (Fin 10) := literalFinset [0, 2, 3] (by decide +kernel)
noncomputable def vertices_37 : Finset (Fin 10) := literalFinset [0, 2, 5] (by decide +kernel)
noncomputable def vertices_69 : Finset (Fin 10) := literalFinset [0, 2, 6] (by decide +kernel)
noncomputable def vertices_25 : Finset (Fin 10) := literalFinset [0, 3, 4] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_193 : Finset (Fin 10) := literalFinset [0, 6, 7] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_50 : Finset (Fin 10) := literalFinset [1, 4, 5] (by decide +kernel)
noncomputable def vertices_146 : Finset (Fin 10) := literalFinset [1, 4, 7] (by decide +kernel)
noncomputable def vertices_530 : Finset (Fin 10) := literalFinset [1, 4, 9] (by decide +kernel)
noncomputable def vertices_546 : Finset (Fin 10) := literalFinset [1, 5, 9] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_28 : Finset (Fin 10) := literalFinset [2, 3, 4] (by decide +kernel)
noncomputable def vertices_76 : Finset (Fin 10) := literalFinset [2, 3, 6] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_532 : Finset (Fin 10) := literalFinset [2, 4, 9] (by decide +kernel)
noncomputable def vertices_100 : Finset (Fin 10) := literalFinset [2, 5, 6] (by decide +kernel)
noncomputable def vertices_548 : Finset (Fin 10) := literalFinset [2, 5, 9] (by decide +kernel)
noncomputable def vertices_580 : Finset (Fin 10) := literalFinset [2, 6, 9] (by decide +kernel)
noncomputable def vertices_152 : Finset (Fin 10) := literalFinset [3, 4, 7] (by decide +kernel)
noncomputable def vertices_536 : Finset (Fin 10) := literalFinset [3, 4, 9] (by decide +kernel)
noncomputable def vertices_200 : Finset (Fin 10) := literalFinset [3, 6, 7] (by decide +kernel)
noncomputable def vertices_584 : Finset (Fin 10) := literalFinset [3, 6, 9] (by decide +kernel)
noncomputable def vertices_648 : Finset (Fin 10) := literalFinset [3, 7, 9] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_608 : Finset (Fin 10) := literalFinset [5, 6, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_155, vertices_51, vertices_803, vertices_451, vertices_61, vertices_205, vertices_357, vertices_566, vertices_914, vertices_604, vertices_612, vertices_664, vertices_712, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_131, vertices_259, vertices_13, vertices_37, vertices_69, vertices_25, vertices_137, vertices_49, vertices_289, vertices_193, vertices_321, vertices_50, vertices_146, vertices_530, vertices_546, vertices_386, vertices_770, vertices_28, vertices_76, vertices_52, vertices_532, vertices_100, vertices_548, vertices_580, vertices_152, vertices_536, vertices_200, vertices_584, vertices_648, vertices_656, vertices_352, vertices_608, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_155), (false, vertices_51), (false, vertices_803), (false, vertices_451), (false, vertices_61), (false, vertices_205), (false, vertices_357), (true, vertices_530), (true, vertices_532), (true, vertices_548), (true, vertices_580), (true, vertices_536), (true, vertices_584), (true, vertices_648), (true, vertices_656), (true, vertices_608), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![12, 16, 20, 21, 22, 23, 24, 25, 26]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_155) then 13 else
  if p.val = (false, vertices_51) then 0 else
  if p.val = (false, vertices_803) then 14 else
  if p.val = (false, vertices_451) then 15 else
  if p.val = (false, vertices_61) then 17 else
  if p.val = (false, vertices_205) then 18 else
  if p.val = (false, vertices_357) then 19 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_580) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_656) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_51), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_155), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_61), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
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
  frame := ![1, 2, 3, 5]
  vertex := 8
  face := Sum.inl ⟨vertices_604, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_28, (by decide +kernel)⟩ ⟨vertices_604, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 3, 4]
  vertex := 8
  face := Sum.inl ⟨vertices_566, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_50, (by decide +kernel)⟩ ⟨vertices_566, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 3, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_914, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_146, (by decide +kernel)⟩ ⟨vertices_914, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
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
noncomputable def pivot : Fin 4 → Fin 9 := ![2, 1, 0, 4]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_566, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 3, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_50, (by decide +kernel)⟩ ⟨vertices_566, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_914, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 3, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_146, (by decide +kernel)⟩ ⟨vertices_914, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_604, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![1, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_28, (by decide +kernel)⟩ ⟨vertices_604, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_612, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![1, 4, 5, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_100, (by decide +kernel)⟩ ⟨vertices_612, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_664, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![2, 3, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_152, (by decide +kernel)⟩ ⟨vertices_664, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_712, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![2, 5, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_200, (by decide +kernel)⟩ ⟨vertices_712, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0063

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m14e10q0_0064.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0064

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_775 : Finset (Fin 10) := literalFinset [0, 1, 2, 8, 9] (by decide +kernel)
noncomputable def vertices_653 : Finset (Fin 10) := literalFinset [0, 2, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_421 : Finset (Fin 10) := literalFinset [0, 2, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_233 : Finset (Fin 10) := literalFinset [0, 3, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_841 : Finset (Fin 10) := literalFinset [0, 3, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_369 : Finset (Fin 10) := literalFinset [0, 4, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_662 : Finset (Fin 10) := literalFinset [1, 2, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_390 : Finset (Fin 10) := literalFinset [1, 2, 7, 8] (by decide +kernel)
noncomputable def vertices_186 : Finset (Fin 10) := literalFinset [1, 3, 4, 5, 7] (by decide +kernel)
noncomputable def vertices_306 : Finset (Fin 10) := literalFinset [1, 4, 5, 8] (by decide +kernel)
noncomputable def vertices_850 : Finset (Fin 10) := literalFinset [1, 4, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_418 : Finset (Fin 10) := literalFinset [1, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_632 : Finset (Fin 10) := literalFinset [3, 4, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_664 : Finset (Fin 10) := literalFinset [3, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_133 : Finset (Fin 10) := literalFinset [0, 2, 7] (by decide +kernel)
noncomputable def vertices_261 : Finset (Fin 10) := literalFinset [0, 2, 8] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_73 : Finset (Fin 10) := literalFinset [0, 3, 6] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_521 : Finset (Fin 10) := literalFinset [0, 3, 9] (by decide +kernel)
noncomputable def vertices_97 : Finset (Fin 10) := literalFinset [0, 5, 6] (by decide +kernel)
noncomputable def vertices_161 : Finset (Fin 10) := literalFinset [0, 5, 7] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_134 : Finset (Fin 10) := literalFinset [1, 2, 7] (by decide +kernel)
noncomputable def vertices_262 : Finset (Fin 10) := literalFinset [1, 2, 8] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_50 : Finset (Fin 10) := literalFinset [1, 4, 5] (by decide +kernel)
noncomputable def vertices_146 : Finset (Fin 10) := literalFinset [1, 4, 7] (by decide +kernel)
noncomputable def vertices_274 : Finset (Fin 10) := literalFinset [1, 4, 8] (by decide +kernel)
noncomputable def vertices_530 : Finset (Fin 10) := literalFinset [1, 4, 9] (by decide +kernel)
noncomputable def vertices_162 : Finset (Fin 10) := literalFinset [1, 5, 7] (by decide +kernel)
noncomputable def vertices_290 : Finset (Fin 10) := literalFinset [1, 5, 8] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_388 : Finset (Fin 10) := literalFinset [2, 7, 8] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_56 : Finset (Fin 10) := literalFinset [3, 4, 5] (by decide +kernel)
noncomputable def vertices_152 : Finset (Fin 10) := literalFinset [3, 4, 7] (by decide +kernel)
noncomputable def vertices_536 : Finset (Fin 10) := literalFinset [3, 4, 9] (by decide +kernel)
noncomputable def vertices_104 : Finset (Fin 10) := literalFinset [3, 5, 6] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_584 : Finset (Fin 10) := literalFinset [3, 6, 9] (by decide +kernel)
noncomputable def vertices_648 : Finset (Fin 10) := literalFinset [3, 7, 9] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_653, vertices_421, vertices_233, vertices_841, vertices_369, vertices_662, vertices_390, vertices_186, vertices_306, vertices_850, vertices_418, vertices_632, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_521, vertices_97, vertices_161, vertices_289, vertices_321, vertices_769, vertices_134, vertices_262, vertices_518, vertices_50, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_386, vertices_770, vertices_388, vertices_644, vertices_56, vertices_152, vertices_536, vertices_104, vertices_168, vertices_584, vertices_648, vertices_112, vertices_304, vertices_336, vertices_592, vertices_656, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_653), (false, vertices_421), (false, vertices_233), (false, vertices_841), (false, vertices_369), (true, vertices_134), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_290), (true, vertices_386), (true, vertices_56), (true, vertices_152), (true, vertices_536), (true, vertices_592), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 15, 18, 21, 23, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 14 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_421) then 17 else
  if p.val = (false, vertices_233) then 19 else
  if p.val = (false, vertices_841) then 20 else
  if p.val = (false, vertices_369) then 22 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_656) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
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
  frame := ![0, 1, 3, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_662, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_134, (by decide +kernel)⟩ ⟨vertices_662, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 4]
  vertex := 6
  face := Sum.inl ⟨vertices_186, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_50, (by decide +kernel)⟩ ⟨vertices_186, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 3, 5, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_850, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_274, (by decide +kernel)⟩ ⟨vertices_850, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
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

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![1, 6, 0, 2]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_662, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_134, (by decide +kernel)⟩ ⟨vertices_662, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_390, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 1, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_134, (by decide +kernel)⟩ ⟨vertices_390, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_186, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 2, 3, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_50, (by decide +kernel)⟩ ⟨vertices_186, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_306, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 3, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_50, (by decide +kernel)⟩ ⟨vertices_306, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_850, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![0, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_274, (by decide +kernel)⟩ ⟨vertices_850, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_418, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![0, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_162, (by decide +kernel)⟩ ⟨vertices_418, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_632, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![2, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_632, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_664, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![2, 3, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_152, (by decide +kernel)⟩ ⟨vertices_664, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0064

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m14e10q0_0067.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0067

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_835 : Finset (Fin 10) := literalFinset [0, 1, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_61 : Finset (Fin 10) := literalFinset [0, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_653 : Finset (Fin 10) := literalFinset [0, 2, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_805 : Finset (Fin 10) := literalFinset [0, 2, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_601 : Finset (Fin 10) := literalFinset [0, 3, 4, 6, 9] (by decide +kernel)
noncomputable def vertices_369 : Finset (Fin 10) := literalFinset [0, 4, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_902 : Finset (Fin 10) := literalFinset [1, 2, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_666 : Finset (Fin 10) := literalFinset [1, 3, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_242 : Finset (Fin 10) := literalFinset [1, 4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_594 : Finset (Fin 10) := literalFinset [1, 4, 6, 9] (by decide +kernel)
noncomputable def vertices_450 : Finset (Fin 10) := literalFinset [1, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_172 : Finset (Fin 10) := literalFinset [2, 3, 5, 7] (by decide +kernel)
noncomputable def vertices_484 : Finset (Fin 10) := literalFinset [2, 5, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_184 : Finset (Fin 10) := literalFinset [3, 4, 5, 7] (by decide +kernel)
noncomputable def vertices_13 : Finset (Fin 10) := literalFinset [0, 2, 3] (by decide +kernel)
noncomputable def vertices_37 : Finset (Fin 10) := literalFinset [0, 2, 5] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_25 : Finset (Fin 10) := literalFinset [0, 3, 4] (by decide +kernel)
noncomputable def vertices_521 : Finset (Fin 10) := literalFinset [0, 3, 9] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_82 : Finset (Fin 10) := literalFinset [1, 4, 6] (by decide +kernel)
noncomputable def vertices_146 : Finset (Fin 10) := literalFinset [1, 4, 7] (by decide +kernel)
noncomputable def vertices_530 : Finset (Fin 10) := literalFinset [1, 4, 9] (by decide +kernel)
noncomputable def vertices_194 : Finset (Fin 10) := literalFinset [1, 6, 7] (by decide +kernel)
noncomputable def vertices_322 : Finset (Fin 10) := literalFinset [1, 6, 8] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_140 : Finset (Fin 10) := literalFinset [2, 3, 7] (by decide +kernel)
noncomputable def vertices_164 : Finset (Fin 10) := literalFinset [2, 5, 7] (by decide +kernel)
noncomputable def vertices_292 : Finset (Fin 10) := literalFinset [2, 5, 8] (by decide +kernel)
noncomputable def vertices_388 : Finset (Fin 10) := literalFinset [2, 7, 8] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_56 : Finset (Fin 10) := literalFinset [3, 4, 5] (by decide +kernel)
noncomputable def vertices_152 : Finset (Fin 10) := literalFinset [3, 4, 7] (by decide +kernel)
noncomputable def vertices_536 : Finset (Fin 10) := literalFinset [3, 4, 9] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_648 : Finset (Fin 10) := literalFinset [3, 7, 9] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_224 : Finset (Fin 10) := literalFinset [5, 6, 7] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_61, vertices_653, vertices_805, vertices_601, vertices_369, vertices_902, vertices_666, vertices_242, vertices_594, vertices_450, vertices_172, vertices_484, vertices_184] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_517, vertices_25, vertices_521, vertices_49, vertices_81, vertices_289, vertices_321, vertices_577, vertices_769, vertices_82, vertices_146, vertices_530, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_44, vertices_140, vertices_164, vertices_292, vertices_388, vertices_644, vertices_772, vertices_56, vertices_152, vertices_536, vertices_168, vertices_648, vertices_112, vertices_176, vertices_592, vertices_224, vertices_352, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_61), (false, vertices_653), (false, vertices_805), (false, vertices_601), (false, vertices_369), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_164), (true, vertices_388), (true, vertices_152), (true, vertices_168), (true, vertices_176), (true, vertices_224), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 15, 19, 21, 23, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 14 else
  if p.val = (false, vertices_61) then 16 else
  if p.val = (false, vertices_653) then 17 else
  if p.val = (false, vertices_805) then 18 else
  if p.val = (false, vertices_601) then 20 else
  if p.val = (false, vertices_369) then 22 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_448) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_61), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
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
  frame := ![0, 2, 3, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_666, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_146, (by decide +kernel)⟩ ⟨vertices_666, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_902, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_386, (by decide +kernel)⟩ ⟨vertices_902, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 3, 4, 5]
  vertex := 6
  face := Sum.inl ⟨vertices_242, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_82, (by decide +kernel)⟩ ⟨vertices_242, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 4, 5, 6]
  vertex := 7
  face := Sum.inl ⟨vertices_484, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_164, (by decide +kernel)⟩ ⟨vertices_484, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![2, 8, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_902, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_386, (by decide +kernel)⟩ ⟨vertices_902, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_666, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 2, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_146, (by decide +kernel)⟩ ⟨vertices_666, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_242, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_82, (by decide +kernel)⟩ ⟨vertices_242, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_594, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 3, 5, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_82, (by decide +kernel)⟩ ⟨vertices_594, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_450, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![0, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_194, (by decide +kernel)⟩ ⟨vertices_450, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_172, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![1, 2, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_172, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_484, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![1, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_164, (by decide +kernel)⟩ ⟨vertices_484, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_184, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![2, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_184, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0067

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m14e10q0_0068.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0068

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_647 : Finset (Fin 10) := literalFinset [0, 1, 2, 7, 9] (by decide +kernel)
noncomputable def vertices_155 : Finset (Fin 10) := literalFinset [0, 1, 3, 4, 7] (by decide +kernel)
noncomputable def vertices_275 : Finset (Fin 10) := literalFinset [0, 1, 4, 8] (by decide +kernel)
noncomputable def vertices_835 : Finset (Fin 10) := literalFinset [0, 1, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_205 : Finset (Fin 10) := literalFinset [0, 2, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_613 : Finset (Fin 10) := literalFinset [0, 2, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_345 : Finset (Fin 10) := literalFinset [0, 3, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_818 : Finset (Fin 10) := literalFinset [1, 4, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_658 : Finset (Fin 10) := literalFinset [1, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_692 : Finset (Fin 10) := literalFinset [2, 4, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_228 : Finset (Fin 10) := literalFinset [2, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_440 : Finset (Fin 10) := literalFinset [3, 4, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_232 : Finset (Fin 10) := literalFinset [3, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_872 : Finset (Fin 10) := literalFinset [3, 5, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_19 : Finset (Fin 10) := literalFinset [0, 1, 4] (by decide +kernel)
noncomputable def vertices_131 : Finset (Fin 10) := literalFinset [0, 1, 7] (by decide +kernel)
noncomputable def vertices_259 : Finset (Fin 10) := literalFinset [0, 1, 8] (by decide +kernel)
noncomputable def vertices_515 : Finset (Fin 10) := literalFinset [0, 1, 9] (by decide +kernel)
noncomputable def vertices_69 : Finset (Fin 10) := literalFinset [0, 2, 6] (by decide +kernel)
noncomputable def vertices_133 : Finset (Fin 10) := literalFinset [0, 2, 7] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_25 : Finset (Fin 10) := literalFinset [0, 3, 4] (by decide +kernel)
noncomputable def vertices_73 : Finset (Fin 10) := literalFinset [0, 3, 6] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_273 : Finset (Fin 10) := literalFinset [0, 4, 8] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_146 : Finset (Fin 10) := literalFinset [1, 4, 7] (by decide +kernel)
noncomputable def vertices_274 : Finset (Fin 10) := literalFinset [1, 4, 8] (by decide +kernel)
noncomputable def vertices_530 : Finset (Fin 10) := literalFinset [1, 4, 9] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_100 : Finset (Fin 10) := literalFinset [2, 5, 6] (by decide +kernel)
noncomputable def vertices_164 : Finset (Fin 10) := literalFinset [2, 5, 7] (by decide +kernel)
noncomputable def vertices_548 : Finset (Fin 10) := literalFinset [2, 5, 9] (by decide +kernel)
noncomputable def vertices_196 : Finset (Fin 10) := literalFinset [2, 6, 7] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_152 : Finset (Fin 10) := literalFinset [3, 4, 7] (by decide +kernel)
noncomputable def vertices_280 : Finset (Fin 10) := literalFinset [3, 4, 8] (by decide +kernel)
noncomputable def vertices_104 : Finset (Fin 10) := literalFinset [3, 5, 6] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_200 : Finset (Fin 10) := literalFinset [3, 6, 7] (by decide +kernel)
noncomputable def vertices_328 : Finset (Fin 10) := literalFinset [3, 6, 8] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_224 : Finset (Fin 10) := literalFinset [5, 6, 7] (by decide +kernel)
noncomputable def vertices_608 : Finset (Fin 10) := literalFinset [5, 6, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_155, vertices_275, vertices_835, vertices_205, vertices_613, vertices_345, vertices_818, vertices_658, vertices_692, vertices_228, vertices_440, vertices_232, vertices_872] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_69, vertices_133, vertices_517, vertices_25, vertices_73, vertices_137, vertices_273, vertices_321, vertices_577, vertices_146, vertices_274, vertices_530, vertices_642, vertices_770, vertices_100, vertices_164, vertices_548, vertices_196, vertices_644, vertices_152, vertices_280, vertices_104, vertices_168, vertices_296, vertices_200, vertices_328, vertices_176, vertices_304, vertices_560, vertices_656, vertices_224, vertices_608, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_155), (false, vertices_275), (false, vertices_835), (false, vertices_205), (false, vertices_613), (false, vertices_345), (true, vertices_530), (true, vertices_164), (true, vertices_104), (true, vertices_168), (true, vertices_296), (true, vertices_176), (true, vertices_304), (true, vertices_560), (true, vertices_656), (true, vertices_224), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![12, 16, 19, 21, 22, 23, 24, 25, 26]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 13 else
  if p.val = (false, vertices_155) then 14 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_835) then 15 else
  if p.val = (false, vertices_205) then 17 else
  if p.val = (false, vertices_613) then 18 else
  if p.val = (false, vertices_345) then 20 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_104) then 3 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_155), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 21 => Sum.inl 3
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
  frame := ![0, 3, 4, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_818, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_274, (by decide +kernel)⟩ ⟨vertices_818, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
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
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_164, (by decide +kernel)⟩ ⟨vertices_692, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
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
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_152, (by decide +kernel)⟩ ⟨vertices_440, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![2, 4, 5, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_872, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_104, (by decide +kernel)⟩ ⟨vertices_872, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 1, 3, 2]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_818, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 3, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_274, (by decide +kernel)⟩ ⟨vertices_818, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_658, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 3, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_146, (by decide +kernel)⟩ ⟨vertices_658, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_692, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![1, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_164, (by decide +kernel)⟩ ⟨vertices_692, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_228, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![1, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_100, (by decide +kernel)⟩ ⟨vertices_228, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_440, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![2, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_152, (by decide +kernel)⟩ ⟨vertices_440, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_232, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![2, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_104, (by decide +kernel)⟩ ⟨vertices_232, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_872, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![2, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_104, (by decide +kernel)⟩ ⟨vertices_872, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0068

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m14e10q0_0069.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0069

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_675 : Finset (Fin 10) := literalFinset [0, 1, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_93 : Finset (Fin 10) := literalFinset [0, 2, 3, 4, 6] (by decide +kernel)
noncomputable def vertices_653 : Finset (Fin 10) := literalFinset [0, 2, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_837 : Finset (Fin 10) := literalFinset [0, 2, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_185 : Finset (Fin 10) := literalFinset [0, 3, 4, 5, 7] (by decide +kernel)
noncomputable def vertices_625 : Finset (Fin 10) := literalFinset [0, 4, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_782 : Finset (Fin 10) := literalFinset [1, 2, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_410 : Finset (Fin 10) := literalFinset [1, 3, 4, 7, 8] (by decide +kernel)
noncomputable def vertices_650 : Finset (Fin 10) := literalFinset [1, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_866 : Finset (Fin 10) := literalFinset [1, 5, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_418 : Finset (Fin 10) := literalFinset [1, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_284 : Finset (Fin 10) := literalFinset [2, 3, 4, 8] (by decide +kernel)
noncomputable def vertices_372 : Finset (Fin 10) := literalFinset [2, 4, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_432 : Finset (Fin 10) := literalFinset [4, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_13 : Finset (Fin 10) := literalFinset [0, 2, 3] (by decide +kernel)
noncomputable def vertices_69 : Finset (Fin 10) := literalFinset [0, 2, 6] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_25 : Finset (Fin 10) := literalFinset [0, 3, 4] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_161 : Finset (Fin 10) := literalFinset [0, 5, 7] (by decide +kernel)
noncomputable def vertices_545 : Finset (Fin 10) := literalFinset [0, 5, 9] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_138 : Finset (Fin 10) := literalFinset [1, 3, 7] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_522 : Finset (Fin 10) := literalFinset [1, 3, 9] (by decide +kernel)
noncomputable def vertices_162 : Finset (Fin 10) := literalFinset [1, 5, 7] (by decide +kernel)
noncomputable def vertices_290 : Finset (Fin 10) := literalFinset [1, 5, 8] (by decide +kernel)
noncomputable def vertices_546 : Finset (Fin 10) := literalFinset [1, 5, 9] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_28 : Finset (Fin 10) := literalFinset [2, 3, 4] (by decide +kernel)
noncomputable def vertices_268 : Finset (Fin 10) := literalFinset [2, 3, 8] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_324 : Finset (Fin 10) := literalFinset [2, 6, 8] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_152 : Finset (Fin 10) := literalFinset [3, 4, 7] (by decide +kernel)
noncomputable def vertices_280 : Finset (Fin 10) := literalFinset [3, 4, 8] (by decide +kernel)
noncomputable def vertices_648 : Finset (Fin 10) := literalFinset [3, 7, 9] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_608 : Finset (Fin 10) := literalFinset [5, 6, 9] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_93, vertices_653, vertices_837, vertices_185, vertices_625, vertices_782, vertices_410, vertices_650, vertices_866, vertices_418, vertices_284, vertices_372, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_517, vertices_25, vertices_137, vertices_49, vertices_81, vertices_161, vertices_545, vertices_577, vertices_641, vertices_138, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_28, vertices_268, vertices_524, vertices_84, vertices_276, vertices_324, vertices_772, vertices_152, vertices_280, vertices_648, vertices_112, vertices_176, vertices_304, vertices_400, vertices_352, vertices_608, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_93), (false, vertices_653), (false, vertices_837), (false, vertices_185), (false, vertices_625), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_290), (true, vertices_386), (true, vertices_770), (true, vertices_268), (true, vertices_276), (true, vertices_280), (true, vertices_304), (true, vertices_400), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 15, 19, 21, 23, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 14 else
  if p.val = (false, vertices_93) then 16 else
  if p.val = (false, vertices_653) then 17 else
  if p.val = (false, vertices_837) then 18 else
  if p.val = (false, vertices_185) then 20 else
  if p.val = (false, vertices_625) then 22 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_416) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
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
  frame := ![0, 2, 3, 6]
  vertex := 7
  face := Sum.inl ⟨vertices_410, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_138, (by decide +kernel)⟩ ⟨vertices_410, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
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
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_266, (by decide +kernel)⟩ ⟨vertices_782, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 4, 5, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_866, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_290, (by decide +kernel)⟩ ⟨vertices_866, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 3, 4, 5]
  vertex := 7
  face := Sum.inl ⟨vertices_372, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_372, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![6, 2, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_782, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_266, (by decide +kernel)⟩ ⟨vertices_782, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_410, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 2, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_138, (by decide +kernel)⟩ ⟨vertices_410, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_650, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 2, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_138, (by decide +kernel)⟩ ⟨vertices_650, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_866, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![0, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_290, (by decide +kernel)⟩ ⟨vertices_866, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_418, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![0, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_162, (by decide +kernel)⟩ ⟨vertices_418, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_284, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![1, 2, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_28, (by decide +kernel)⟩ ⟨vertices_284, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_372, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![1, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_372, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_432, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![3, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_176, (by decide +kernel)⟩ ⟨vertices_432, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0069

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m14e10q0_0070.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0070

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_307 : Finset (Fin 10) := literalFinset [0, 1, 4, 5, 8] (by decide +kernel)
noncomputable def vertices_659 : Finset (Fin 10) := literalFinset [0, 1, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_611 : Finset (Fin 10) := literalFinset [0, 1, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_357 : Finset (Fin 10) := literalFinset [0, 2, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_409 : Finset (Fin 10) := literalFinset [0, 3, 4, 7, 8] (by decide +kernel)
noncomputable def vertices_961 : Finset (Fin 10) := literalFinset [0, 6, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_558 : Finset (Fin 10) := literalFinset [1, 2, 3, 5, 9] (by decide +kernel)
noncomputable def vertices_282 : Finset (Fin 10) := literalFinset [1, 3, 4, 8] (by decide +kernel)
noncomputable def vertices_538 : Finset (Fin 10) := literalFinset [1, 3, 4, 9] (by decide +kernel)
noncomputable def vertices_298 : Finset (Fin 10) := literalFinset [1, 3, 5, 8] (by decide +kernel)
noncomputable def vertices_668 : Finset (Fin 10) := literalFinset [2, 3, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_300 : Finset (Fin 10) := literalFinset [2, 3, 5, 8] (by decide +kernel)
noncomputable def vertices_460 : Finset (Fin 10) := literalFinset [2, 3, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_740 : Finset (Fin 10) := literalFinset [2, 5, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_19 : Finset (Fin 10) := literalFinset [0, 1, 4] (by decide +kernel)
noncomputable def vertices_35 : Finset (Fin 10) := literalFinset [0, 1, 5] (by decide +kernel)
noncomputable def vertices_515 : Finset (Fin 10) := literalFinset [0, 1, 9] (by decide +kernel)
noncomputable def vertices_145 : Finset (Fin 10) := literalFinset [0, 4, 7] (by decide +kernel)
noncomputable def vertices_273 : Finset (Fin 10) := literalFinset [0, 4, 8] (by decide +kernel)
noncomputable def vertices_97 : Finset (Fin 10) := literalFinset [0, 5, 6] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_385 : Finset (Fin 10) := literalFinset [0, 7, 8] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_26 : Finset (Fin 10) := literalFinset [1, 3, 4] (by decide +kernel)
noncomputable def vertices_42 : Finset (Fin 10) := literalFinset [1, 3, 5] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_522 : Finset (Fin 10) := literalFinset [1, 3, 9] (by decide +kernel)
noncomputable def vertices_274 : Finset (Fin 10) := literalFinset [1, 4, 8] (by decide +kernel)
noncomputable def vertices_530 : Finset (Fin 10) := literalFinset [1, 4, 9] (by decide +kernel)
noncomputable def vertices_290 : Finset (Fin 10) := literalFinset [1, 5, 8] (by decide +kernel)
noncomputable def vertices_546 : Finset (Fin 10) := literalFinset [1, 5, 9] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_140 : Finset (Fin 10) := literalFinset [2, 3, 7] (by decide +kernel)
noncomputable def vertices_268 : Finset (Fin 10) := literalFinset [2, 3, 8] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_100 : Finset (Fin 10) := literalFinset [2, 5, 6] (by decide +kernel)
noncomputable def vertices_292 : Finset (Fin 10) := literalFinset [2, 5, 8] (by decide +kernel)
noncomputable def vertices_548 : Finset (Fin 10) := literalFinset [2, 5, 9] (by decide +kernel)
noncomputable def vertices_196 : Finset (Fin 10) := literalFinset [2, 6, 7] (by decide +kernel)
noncomputable def vertices_324 : Finset (Fin 10) := literalFinset [2, 6, 8] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_152 : Finset (Fin 10) := literalFinset [3, 4, 7] (by decide +kernel)
noncomputable def vertices_280 : Finset (Fin 10) := literalFinset [3, 4, 8] (by decide +kernel)
noncomputable def vertices_536 : Finset (Fin 10) := literalFinset [3, 4, 9] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_392 : Finset (Fin 10) := literalFinset [3, 7, 8] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_608 : Finset (Fin 10) := literalFinset [5, 6, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_659, vertices_611, vertices_357, vertices_409, vertices_961, vertices_558, vertices_282, vertices_538, vertices_298, vertices_668, vertices_300, vertices_460, vertices_740] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_515, vertices_145, vertices_273, vertices_97, vertices_289, vertices_321, vertices_577, vertices_385, vertices_641, vertices_26, vertices_42, vertices_266, vertices_522, vertices_274, vertices_530, vertices_290, vertices_546, vertices_44, vertices_140, vertices_268, vertices_524, vertices_100, vertices_292, vertices_548, vertices_196, vertices_324, vertices_644, vertices_152, vertices_280, vertices_536, vertices_296, vertices_392, vertices_656, vertices_608, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_659), (false, vertices_611), (false, vertices_357), (false, vertices_409), (false, vertices_961), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_44), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_548), (true, vertices_196), (true, vertices_644), (true, vertices_536), (true, vertices_296)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 17, 19, 21, 22, 23, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 14 else
  if p.val = (false, vertices_659) then 15 else
  if p.val = (false, vertices_611) then 16 else
  if p.val = (false, vertices_357) then 18 else
  if p.val = (false, vertices_409) then 20 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_296) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
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
  frame := ![0, 1, 2, 4]
  vertex := 8
  face := Sum.inl ⟨vertices_558, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_42, (by decide +kernel)⟩ ⟨vertices_558, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 3, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_668, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_140, (by decide +kernel)⟩ ⟨vertices_668, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 5, 6]
  vertex := 7
  face := Sum.inl ⟨vertices_460, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_140, (by decide +kernel)⟩ ⟨vertices_460, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 4, 5, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_740, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_100, (by decide +kernel)⟩ ⟨vertices_740, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 3, 2, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_558, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_42, (by decide +kernel)⟩ ⟨vertices_558, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_282, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 2, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_26, (by decide +kernel)⟩ ⟨vertices_282, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_538, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 2, 3, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_26, (by decide +kernel)⟩ ⟨vertices_538, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_298, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 2, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_42, (by decide +kernel)⟩ ⟨vertices_298, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_668, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![1, 2, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_140, (by decide +kernel)⟩ ⟨vertices_668, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_300, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![1, 2, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_300, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_460, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![1, 2, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_140, (by decide +kernel)⟩ ⟨vertices_460, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_740, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .oneRow ![1, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_100, (by decide +kernel)⟩ ⟨vertices_740, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0070

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m14e10q0_0071.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0071

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_115 : Finset (Fin 10) := literalFinset [0, 1, 4, 5, 6] (by decide +kernel)
noncomputable def vertices_403 : Finset (Fin 10) := literalFinset [0, 1, 4, 7, 8] (by decide +kernel)
noncomputable def vertices_707 : Finset (Fin 10) := literalFinset [0, 1, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_109 : Finset (Fin 10) := literalFinset [0, 2, 3, 5, 6] (by decide +kernel)
noncomputable def vertices_653 : Finset (Fin 10) := literalFinset [0, 2, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_581 : Finset (Fin 10) := literalFinset [0, 2, 6, 9] (by decide +kernel)
noncomputable def vertices_185 : Finset (Fin 10) := literalFinset [0, 3, 4, 5, 7] (by decide +kernel)
noncomputable def vertices_838 : Finset (Fin 10) := literalFinset [1, 2, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_906 : Finset (Fin 10) := literalFinset [1, 3, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_338 : Finset (Fin 10) := literalFinset [1, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_812 : Finset (Fin 10) := literalFinset [2, 3, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_372 : Finset (Fin 10) := literalFinset [2, 4, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_424 : Finset (Fin 10) := literalFinset [3, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_432 : Finset (Fin 10) := literalFinset [4, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_19 : Finset (Fin 10) := literalFinset [0, 1, 4] (by decide +kernel)
noncomputable def vertices_67 : Finset (Fin 10) := literalFinset [0, 1, 6] (by decide +kernel)
noncomputable def vertices_131 : Finset (Fin 10) := literalFinset [0, 1, 7] (by decide +kernel)
noncomputable def vertices_13 : Finset (Fin 10) := literalFinset [0, 2, 3] (by decide +kernel)
noncomputable def vertices_69 : Finset (Fin 10) := literalFinset [0, 2, 6] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_145 : Finset (Fin 10) := literalFinset [0, 4, 7] (by decide +kernel)
noncomputable def vertices_97 : Finset (Fin 10) := literalFinset [0, 5, 6] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_82 : Finset (Fin 10) := literalFinset [1, 4, 6] (by decide +kernel)
noncomputable def vertices_274 : Finset (Fin 10) := literalFinset [1, 4, 8] (by decide +kernel)
noncomputable def vertices_322 : Finset (Fin 10) := literalFinset [1, 6, 8] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_100 : Finset (Fin 10) := literalFinset [2, 5, 6] (by decide +kernel)
noncomputable def vertices_292 : Finset (Fin 10) := literalFinset [2, 5, 8] (by decide +kernel)
noncomputable def vertices_324 : Finset (Fin 10) := literalFinset [2, 6, 8] (by decide +kernel)
noncomputable def vertices_580 : Finset (Fin 10) := literalFinset [2, 6, 9] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_392 : Finset (Fin 10) := literalFinset [3, 7, 8] (by decide +kernel)
noncomputable def vertices_648 : Finset (Fin 10) := literalFinset [3, 7, 9] (by decide +kernel)
noncomputable def vertices_776 : Finset (Fin 10) := literalFinset [3, 8, 9] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_115, vertices_403, vertices_707, vertices_109, vertices_653, vertices_581, vertices_185, vertices_838, vertices_906, vertices_338, vertices_812, vertices_372, vertices_424, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_131, vertices_13, vertices_69, vertices_517, vertices_41, vertices_137, vertices_49, vertices_145, vertices_97, vertices_577, vertices_641, vertices_82, vertices_274, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_44, vertices_524, vertices_100, vertices_292, vertices_324, vertices_580, vertices_772, vertices_168, vertices_296, vertices_392, vertices_648, vertices_776, vertices_112, vertices_176, vertices_304, vertices_336, vertices_400, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_115), (false, vertices_403), (false, vertices_707), (false, vertices_109), (false, vertices_653), (false, vertices_581), (false, vertices_185), (true, vertices_322), (true, vertices_770), (true, vertices_292), (true, vertices_324), (true, vertices_772), (true, vertices_296), (true, vertices_392), (true, vertices_776), (true, vertices_304), (true, vertices_336), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![12, 16, 19, 21, 22, 23, 24, 25, 26]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_115) then 13 else
  if p.val = (false, vertices_403) then 14 else
  if p.val = (false, vertices_707) then 15 else
  if p.val = (false, vertices_109) then 17 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_581) then 0 else
  if p.val = (false, vertices_185) then 20 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_292) then 3 else
  if p.val = (true, vertices_324) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_392) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_416) then 11 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_581), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_115), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
  | 21 => Sum.inl 3
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
  frame := ![0, 2, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_906, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_386, (by decide +kernel)⟩ ⟨vertices_906, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
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
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_322, (by decide +kernel)⟩ ⟨vertices_838, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
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

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 3, 4, 5]
  vertex := 7
  face := Sum.inl ⟨vertices_372, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_100, (by decide +kernel)⟩ ⟨vertices_372, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![6, 0, 2, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_838, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_322, (by decide +kernel)⟩ ⟨vertices_838, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_906, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 2, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_386, (by decide +kernel)⟩ ⟨vertices_906, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_338, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_82, (by decide +kernel)⟩ ⟨vertices_338, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_812, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 2, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_812, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_372, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![1, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_100, (by decide +kernel)⟩ ⟨vertices_372, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_424, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![2, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_168, (by decide +kernel)⟩ ⟨vertices_424, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_432, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![3, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_176, (by decide +kernel)⟩ ⟨vertices_432, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0071

end
end BundlePart29
-- Explicit facial frame witnesses.

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_0210 : Certifies 210 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0009.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0211 : Certifies 211 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0011.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0212 : Certifies 212 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0012.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0213 : Certifies 213 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0013.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0214 : Certifies 214 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0023.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0215 : Certifies 215 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0024.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0216 : Certifies 216 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0029.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0217 : Certifies 217 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0032.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0218 : Certifies 218 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0033.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0219 : Certifies 219 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0034.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0220 : Certifies 220 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0035.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0221 : Certifies 221 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0036.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0222 : Certifies 222 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0037.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0223 : Certifies 223 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0040.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0224 : Certifies 224 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0041.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0225 : Certifies 225 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0042.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0226 : Certifies 226 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0045.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0227 : Certifies 227 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0046.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0228 : Certifies 228 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0051.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0229 : Certifies 229 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0052.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0230 : Certifies 230 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0054.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0231 : Certifies 231 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0057.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0232 : Certifies 232 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0058.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0233 : Certifies 233 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0063.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0234 : Certifies 234 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0064.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0235 : Certifies 235 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0067.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0236 : Certifies 236 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0068.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0237 : Certifies 237 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0069.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0238 : Certifies 238 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0070.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0239 : Certifies 239 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q0_0071.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B007 (j : Fin 30) :
    Certifies (210 + j.val) := by
  fin_cases j
  · exact projection_0210
  · exact projection_0211
  · exact projection_0212
  · exact projection_0213
  · exact projection_0214
  · exact projection_0215
  · exact projection_0216
  · exact projection_0217
  · exact projection_0218
  · exact projection_0219
  · exact projection_0220
  · exact projection_0221
  · exact projection_0222
  · exact projection_0223
  · exact projection_0224
  · exact projection_0225
  · exact projection_0226
  · exact projection_0227
  · exact projection_0228
  · exact projection_0229
  · exact projection_0230
  · exact projection_0231
  · exact projection_0232
  · exact projection_0233
  · exact projection_0234
  · exact projection_0235
  · exact projection_0236
  · exact projection_0237
  · exact projection_0238
  · exact projection_0239

end Nonrational.TerminalVerification
