module
public import TerminalGeometry
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Papers.FiniteProjectionChecks

section
set_option debug.skipKernelTC false


section BundlePart0
/- Source: ProjectionCertificates/R_m15e10q1_0273.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0273

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_539 : Finset (Fin 10) := literalFinset [0, 1, 3, 4, 9] (by decide +kernel)
noncomputable def vertices_781 : Finset (Fin 10) := literalFinset [0, 2, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_677 : Finset (Fin 10) := literalFinset [0, 2, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_453 : Finset (Fin 10) := literalFinset [0, 2, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_409 : Finset (Fin 10) := literalFinset [0, 3, 4, 7, 8] (by decide +kernel)
noncomputable def vertices_657 : Finset (Fin 10) := literalFinset [0, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_358 : Finset (Fin 10) := literalFinset [1, 2, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_218 : Finset (Fin 10) := literalFinset [1, 3, 4, 6, 7] (by decide +kernel)
noncomputable def vertices_810 : Finset (Fin 10) := literalFinset [1, 3, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_458 : Finset (Fin 10) := literalFinset [1, 3, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_114 : Finset (Fin 10) := literalFinset [1, 4, 5, 6] (by decide +kernel)
noncomputable def vertices_562 : Finset (Fin 10) := literalFinset [1, 4, 5, 9] (by decide +kernel)
noncomputable def vertices_244 : Finset (Fin 10) := literalFinset [2, 4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_804 : Finset (Fin 10) := literalFinset [2, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_688 : Finset (Fin 10) := literalFinset [4, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_133 : Finset (Fin 10) := literalFinset [0, 2, 7] (by decide +kernel)
noncomputable def vertices_261 : Finset (Fin 10) := literalFinset [0, 2, 8] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_25 : Finset (Fin 10) := literalFinset [0, 3, 4] (by decide +kernel)
noncomputable def vertices_265 : Finset (Fin 10) := literalFinset [0, 3, 8] (by decide +kernel)
noncomputable def vertices_521 : Finset (Fin 10) := literalFinset [0, 3, 9] (by decide +kernel)
noncomputable def vertices_145 : Finset (Fin 10) := literalFinset [0, 4, 7] (by decide +kernel)
noncomputable def vertices_529 : Finset (Fin 10) := literalFinset [0, 4, 9] (by decide +kernel)
noncomputable def vertices_385 : Finset (Fin 10) := literalFinset [0, 7, 8] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_26 : Finset (Fin 10) := literalFinset [1, 3, 4] (by decide +kernel)
noncomputable def vertices_202 : Finset (Fin 10) := literalFinset [1, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_522 : Finset (Fin 10) := literalFinset [1, 3, 9] (by decide +kernel)
noncomputable def vertices_50 : Finset (Fin 10) := literalFinset [1, 4, 5] (by decide +kernel)
noncomputable def vertices_82 : Finset (Fin 10) := literalFinset [1, 4, 6] (by decide +kernel)
noncomputable def vertices_530 : Finset (Fin 10) := literalFinset [1, 4, 9] (by decide +kernel)
noncomputable def vertices_98 : Finset (Fin 10) := literalFinset [1, 5, 6] (by decide +kernel)
noncomputable def vertices_290 : Finset (Fin 10) := literalFinset [1, 5, 8] (by decide +kernel)
noncomputable def vertices_546 : Finset (Fin 10) := literalFinset [1, 5, 9] (by decide +kernel)
noncomputable def vertices_322 : Finset (Fin 10) := literalFinset [1, 6, 8] (by decide +kernel)
noncomputable def vertices_100 : Finset (Fin 10) := literalFinset [2, 5, 6] (by decide +kernel)
noncomputable def vertices_164 : Finset (Fin 10) := literalFinset [2, 5, 7] (by decide +kernel)
noncomputable def vertices_292 : Finset (Fin 10) := literalFinset [2, 5, 8] (by decide +kernel)
noncomputable def vertices_548 : Finset (Fin 10) := literalFinset [2, 5, 9] (by decide +kernel)
noncomputable def vertices_196 : Finset (Fin 10) := literalFinset [2, 6, 7] (by decide +kernel)
noncomputable def vertices_324 : Finset (Fin 10) := literalFinset [2, 6, 8] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_152 : Finset (Fin 10) := literalFinset [3, 4, 7] (by decide +kernel)
noncomputable def vertices_392 : Finset (Fin 10) := literalFinset [3, 7, 8] (by decide +kernel)
noncomputable def vertices_776 : Finset (Fin 10) := literalFinset [3, 8, 9] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_208 : Finset (Fin 10) := literalFinset [4, 6, 7] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_539, vertices_781, vertices_677, vertices_453, vertices_409, vertices_657, vertices_358, vertices_218, vertices_810, vertices_458, vertices_114, vertices_562, vertices_244, vertices_804, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_25, vertices_265, vertices_521, vertices_145, vertices_529, vertices_385, vertices_641, vertices_26, vertices_202, vertices_266, vertices_522, vertices_50, vertices_82, vertices_530, vertices_98, vertices_290, vertices_546, vertices_322, vertices_100, vertices_164, vertices_292, vertices_548, vertices_196, vertices_324, vertices_772, vertices_152, vertices_392, vertices_776, vertices_112, vertices_176, vertices_560, vertices_208, vertices_656, vertices_672, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_539), (false, vertices_781), (false, vertices_677), (false, vertices_453), (false, vertices_409), (false, vertices_657), (true, vertices_202), (true, vertices_266), (true, vertices_50), (true, vertices_82), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_322), (true, vertices_100), (true, vertices_292), (true, vertices_112), (true, vertices_176), (true, vertices_560), (true, vertices_208), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![15, 18, 22, 24, 25, 26, 27, 28, 29]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_539) then 16 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_677) then 20 else
  if p.val = (false, vertices_453) then 21 else
  if p.val = (false, vertices_409) then 23 else
  if p.val = (false, vertices_657) then 0 else
  if p.val = (true, vertices_202) then 17 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_800) then 14 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_657), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 4, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_810, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_266, (by decide +kernel)⟩ ⟨vertices_810, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
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
  frame := ![0, 1, 4, 5]
  vertex := 7
  face := Sum.inl ⟨vertices_358, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_98, (by decide +kernel)⟩ ⟨vertices_358, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 3, 4, 5]
  vertex := 6
  face := Sum.inl ⟨vertices_244, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_100, (by decide +kernel)⟩ ⟨vertices_244, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![8, 2, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_358, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_98, (by decide +kernel)⟩ ⟨vertices_358, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_218, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_26, (by decide +kernel)⟩ ⟨vertices_218, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_810, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 2, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_266, (by decide +kernel)⟩ ⟨vertices_810, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_458, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![0, 2, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_202, (by decide +kernel)⟩ ⟨vertices_458, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_114, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![0, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_50, (by decide +kernel)⟩ ⟨vertices_114, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_562, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![0, 3, 4, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_50, (by decide +kernel)⟩ ⟨vertices_562, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_244, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![1, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_100, (by decide +kernel)⟩ ⟨vertices_244, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_804, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![1, 4, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_292, (by decide +kernel)⟩ ⟨vertices_804, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet8 : boundary.facets := ⟨vertices_688, by decide +kernel⟩
noncomputable def cover8 : FacetCoverage heightProof coverFacet8 :=
  .fundamental ![3, 4, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_176, (by decide +kernel)⟩ ⟨vertices_688, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coveringFacets : Fin 9 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6, coverFacet7, coverFacet8]
noncomputable def coveringProof (j : Fin 9) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (Fin.cases cover7 (Fin.cases cover8 (fun i => Fin.elim0 i)))))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 9, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0273

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e10q1_0274.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0274

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_203 : Finset (Fin 10) := literalFinset [0, 1, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_805 : Finset (Fin 10) := literalFinset [0, 2, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_681 : Finset (Fin 10) := literalFinset [0, 3, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_841 : Finset (Fin 10) := literalFinset [0, 3, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_433 : Finset (Fin 10) := literalFinset [0, 4, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_449 : Finset (Fin 10) := literalFinset [0, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_334 : Finset (Fin 10) := literalFinset [1, 2, 3, 6, 8] (by decide +kernel)
noncomputable def vertices_782 : Finset (Fin 10) := literalFinset [1, 2, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_566 : Finset (Fin 10) := literalFinset [1, 2, 4, 5, 9] (by decide +kernel)
noncomputable def vertices_86 : Finset (Fin 10) := literalFinset [1, 2, 4, 6] (by decide +kernel)
noncomputable def vertices_666 : Finset (Fin 10) := literalFinset [1, 3, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_210 : Finset (Fin 10) := literalFinset [1, 4, 6, 7] (by decide +kernel)
noncomputable def vertices_308 : Finset (Fin 10) := literalFinset [2, 4, 5, 8] (by decide +kernel)
noncomputable def vertices_468 : Finset (Fin 10) := literalFinset [2, 4, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_688 : Finset (Fin 10) := literalFinset [4, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_73 : Finset (Fin 10) := literalFinset [0, 3, 6] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_521 : Finset (Fin 10) := literalFinset [0, 3, 9] (by decide +kernel)
noncomputable def vertices_161 : Finset (Fin 10) := literalFinset [0, 5, 7] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_545 : Finset (Fin 10) := literalFinset [0, 5, 9] (by decide +kernel)
noncomputable def vertices_193 : Finset (Fin 10) := literalFinset [0, 6, 7] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_385 : Finset (Fin 10) := literalFinset [0, 7, 8] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_270 : Finset (Fin 10) := literalFinset [1, 2, 3, 8] (by decide +kernel)
noncomputable def vertices_22 : Finset (Fin 10) := literalFinset [1, 2, 4] (by decide +kernel)
noncomputable def vertices_70 : Finset (Fin 10) := literalFinset [1, 2, 6] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_74 : Finset (Fin 10) := literalFinset [1, 3, 6] (by decide +kernel)
noncomputable def vertices_138 : Finset (Fin 10) := literalFinset [1, 3, 7] (by decide +kernel)
noncomputable def vertices_522 : Finset (Fin 10) := literalFinset [1, 3, 9] (by decide +kernel)
noncomputable def vertices_82 : Finset (Fin 10) := literalFinset [1, 4, 6] (by decide +kernel)
noncomputable def vertices_146 : Finset (Fin 10) := literalFinset [1, 4, 7] (by decide +kernel)
noncomputable def vertices_530 : Finset (Fin 10) := literalFinset [1, 4, 9] (by decide +kernel)
noncomputable def vertices_194 : Finset (Fin 10) := literalFinset [1, 6, 7] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_292 : Finset (Fin 10) := literalFinset [2, 5, 8] (by decide +kernel)
noncomputable def vertices_548 : Finset (Fin 10) := literalFinset [2, 5, 9] (by decide +kernel)
noncomputable def vertices_324 : Finset (Fin 10) := literalFinset [2, 6, 8] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_328 : Finset (Fin 10) := literalFinset [3, 6, 8] (by decide +kernel)
noncomputable def vertices_648 : Finset (Fin 10) := literalFinset [3, 7, 9] (by decide +kernel)
noncomputable def vertices_776 : Finset (Fin 10) := literalFinset [3, 8, 9] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_208 : Finset (Fin 10) := literalFinset [4, 6, 7] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_203, vertices_805, vertices_681, vertices_841, vertices_433, vertices_449, vertices_334, vertices_782, vertices_566, vertices_86, vertices_666, vertices_210, vertices_308, vertices_468, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_521, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_385, vertices_769, vertices_270, vertices_22, vertices_70, vertices_518, vertices_74, vertices_138, vertices_522, vertices_82, vertices_146, vertices_530, vertices_194, vertices_52, vertices_84, vertices_276, vertices_292, vertices_548, vertices_324, vertices_772, vertices_328, vertices_648, vertices_776, vertices_176, vertices_304, vertices_560, vertices_208, vertices_400, vertices_656, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_203), (false, vertices_805), (false, vertices_681), (false, vertices_841), (false, vertices_433), (false, vertices_449), (true, vertices_270), (true, vertices_22), (true, vertices_70), (true, vertices_518), (true, vertices_522), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_52), (true, vertices_84), (true, vertices_276), (true, vertices_324), (true, vertices_560), (true, vertices_208), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![15, 18, 20, 23, 25, 26, 27, 28, 29]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_203) then 16 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (false, vertices_841) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_270) then 17 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_324) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_656) then 14 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_270), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 3, 4]
  vertex := 8
  face := Sum.inl ⟨vertices_566, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_566, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_666, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_138, (by decide +kernel)⟩ ⟨vertices_666, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 3
  frame := ![0, 1, 2]
  vertex := 7
  face := Sum.inr ⟨vertices_270, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_270, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
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

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![4, 8, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_334, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_270, (by decide +kernel)⟩ ⟨vertices_334, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_782, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 2, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_270, (by decide +kernel)⟩ ⟨vertices_782, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_566, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 1, 3, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_566, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_86, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 1, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_86, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_666, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![0, 2, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_138, (by decide +kernel)⟩ ⟨vertices_666, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_210, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![0, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_82, (by decide +kernel)⟩ ⟨vertices_210, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_308, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![1, 3, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_308, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_468, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .oneRow ![1, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_468, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet8 : boundary.facets := ⟨vertices_688, by decide +kernel⟩
noncomputable def cover8 : FacetCoverage heightProof coverFacet8 :=
  .fundamental ![3, 4, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_176, (by decide +kernel)⟩ ⟨vertices_688, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coveringFacets : Fin 9 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6, coverFacet7, coverFacet8]
noncomputable def coveringProof (j : Fin 9) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (Fin.cases cover7 (Fin.cases cover8 (fun i => Fin.elim0 i)))))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 9, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0274

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e10q1_0275.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0275

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_675 : Finset (Fin 10) := literalFinset [0, 1, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_589 : Finset (Fin 10) := literalFinset [0, 2, 3, 6, 9] (by decide +kernel)
noncomputable def vertices_805 : Finset (Fin 10) := literalFinset [0, 2, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_453 : Finset (Fin 10) := literalFinset [0, 2, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_433 : Finset (Fin 10) := literalFinset [0, 4, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_705 : Finset (Fin 10) := literalFinset [0, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_782 : Finset (Fin 10) := literalFinset [1, 2, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_314 : Finset (Fin 10) := literalFinset [1, 3, 4, 5, 8] (by decide +kernel)
noncomputable def vertices_602 : Finset (Fin 10) := literalFinset [1, 3, 4, 6, 9] (by decide +kernel)
noncomputable def vertices_178 : Finset (Fin 10) := literalFinset [1, 4, 5, 7] (by decide +kernel)
noncomputable def vertices_658 : Finset (Fin 10) := literalFinset [1, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_802 : Finset (Fin 10) := literalFinset [1, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_220 : Finset (Fin 10) := literalFinset [2, 3, 4, 6, 7] (by decide +kernel)
noncomputable def vertices_412 : Finset (Fin 10) := literalFinset [2, 3, 4, 7, 8] (by decide +kernel)
noncomputable def vertices_720 : Finset (Fin 10) := literalFinset [4, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_69 : Finset (Fin 10) := literalFinset [0, 2, 6] (by decide +kernel)
noncomputable def vertices_261 : Finset (Fin 10) := literalFinset [0, 2, 8] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_161 : Finset (Fin 10) := literalFinset [0, 5, 7] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_545 : Finset (Fin 10) := literalFinset [0, 5, 9] (by decide +kernel)
noncomputable def vertices_193 : Finset (Fin 10) := literalFinset [0, 6, 7] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_385 : Finset (Fin 10) := literalFinset [0, 7, 8] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_26 : Finset (Fin 10) := literalFinset [1, 3, 4] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_522 : Finset (Fin 10) := literalFinset [1, 3, 9] (by decide +kernel)
noncomputable def vertices_50 : Finset (Fin 10) := literalFinset [1, 4, 5] (by decide +kernel)
noncomputable def vertices_146 : Finset (Fin 10) := literalFinset [1, 4, 7] (by decide +kernel)
noncomputable def vertices_530 : Finset (Fin 10) := literalFinset [1, 4, 9] (by decide +kernel)
noncomputable def vertices_162 : Finset (Fin 10) := literalFinset [1, 5, 7] (by decide +kernel)
noncomputable def vertices_290 : Finset (Fin 10) := literalFinset [1, 5, 8] (by decide +kernel)
noncomputable def vertices_546 : Finset (Fin 10) := literalFinset [1, 5, 9] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_156 : Finset (Fin 10) := literalFinset [2, 3, 4, 7] (by decide +kernel)
noncomputable def vertices_76 : Finset (Fin 10) := literalFinset [2, 3, 6] (by decide +kernel)
noncomputable def vertices_268 : Finset (Fin 10) := literalFinset [2, 3, 8] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_196 : Finset (Fin 10) := literalFinset [2, 6, 7] (by decide +kernel)
noncomputable def vertices_388 : Finset (Fin 10) := literalFinset [2, 7, 8] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_88 : Finset (Fin 10) := literalFinset [3, 4, 6] (by decide +kernel)
noncomputable def vertices_280 : Finset (Fin 10) := literalFinset [3, 4, 8] (by decide +kernel)
noncomputable def vertices_584 : Finset (Fin 10) := literalFinset [3, 6, 9] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_208 : Finset (Fin 10) := literalFinset [4, 6, 7] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_589, vertices_805, vertices_453, vertices_433, vertices_705, vertices_782, vertices_314, vertices_602, vertices_178, vertices_658, vertices_802, vertices_220, vertices_412, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_641, vertices_26, vertices_266, vertices_522, vertices_50, vertices_146, vertices_530, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_156, vertices_76, vertices_268, vertices_524, vertices_196, vertices_388, vertices_772, vertices_88, vertices_280, vertices_584, vertices_176, vertices_304, vertices_208, vertices_592, vertices_400, vertices_656, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_589), (false, vertices_805), (false, vertices_453), (false, vertices_433), (false, vertices_705), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_146), (true, vertices_530), (true, vertices_290), (true, vertices_770), (true, vertices_156), (true, vertices_268), (true, vertices_88), (true, vertices_280), (true, vertices_208), (true, vertices_592), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![15, 20, 17, 23, 25, 26, 27, 28, 29]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_589) then 18 else
  if p.val = (false, vertices_805) then 21 else
  if p.val = (false, vertices_453) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (false, vertices_705) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_156) then 19 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_656) then 14 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_705), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_156), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 3
  frame := ![1, 2, 3]
  vertex := 6
  face := Sum.inr ⟨vertices_156, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_156, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
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
  frame := ![0, 2, 3, 4]
  vertex := 7
  face := Sum.inl ⟨vertices_314, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_26, (by decide +kernel)⟩ ⟨vertices_314, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 5]
  vertex := 8
  face := Sum.inl ⟨vertices_602, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_26, (by decide +kernel)⟩ ⟨vertices_602, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![6, 1, 4, 0]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_782, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_266, (by decide +kernel)⟩ ⟨vertices_782, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_314, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 2, 3, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_26, (by decide +kernel)⟩ ⟨vertices_314, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_602, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_26, (by decide +kernel)⟩ ⟨vertices_602, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_178, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_50, (by decide +kernel)⟩ ⟨vertices_178, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_658, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![0, 3, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_146, (by decide +kernel)⟩ ⟨vertices_658, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_802, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![0, 4, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_290, (by decide +kernel)⟩ ⟨vertices_802, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_220, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![1, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_156, (by decide +kernel)⟩ ⟨vertices_220, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_412, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .oneRow ![1, 2, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_156, (by decide +kernel)⟩ ⟨vertices_412, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet8 : boundary.facets := ⟨vertices_720, by decide +kernel⟩
noncomputable def cover8 : FacetCoverage heightProof coverFacet8 :=
  .fundamental ![3, 5, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_208, (by decide +kernel)⟩ ⟨vertices_720, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coveringFacets : Fin 9 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6, coverFacet7, coverFacet8]
noncomputable def coveringProof (j : Fin 9) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (Fin.cases cover7 (Fin.cases cover8 (fun i => Fin.elim0 i)))))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 9, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0275

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e10q1_0276.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0276

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_279 : Finset (Fin 10) := literalFinset [0, 1, 2, 4, 8] (by decide +kernel)
noncomputable def vertices_535 : Finset (Fin 10) := literalFinset [0, 1, 2, 4, 9] (by decide +kernel)
noncomputable def vertices_837 : Finset (Fin 10) := literalFinset [0, 2, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_313 : Finset (Fin 10) := literalFinset [0, 3, 4, 5, 8] (by decide +kernel)
noncomputable def vertices_625 : Finset (Fin 10) := literalFinset [0, 4, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_481 : Finset (Fin 10) := literalFinset [0, 5, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_654 : Finset (Fin 10) := literalFinset [1, 2, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_454 : Finset (Fin 10) := literalFinset [1, 2, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_570 : Finset (Fin 10) := literalFinset [1, 3, 4, 5, 9] (by decide +kernel)
noncomputable def vertices_154 : Finset (Fin 10) := literalFinset [1, 3, 4, 7] (by decide +kernel)
noncomputable def vertices_402 : Finset (Fin 10) := literalFinset [1, 4, 7, 8] (by decide +kernel)
noncomputable def vertices_740 : Finset (Fin 10) := literalFinset [2, 5, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_408 : Finset (Fin 10) := literalFinset [3, 4, 7, 8] (by decide +kernel)
noncomputable def vertices_424 : Finset (Fin 10) := literalFinset [3, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_680 : Finset (Fin 10) := literalFinset [3, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_23 : Finset (Fin 10) := literalFinset [0, 1, 2, 4] (by decide +kernel)
noncomputable def vertices_261 : Finset (Fin 10) := literalFinset [0, 2, 8] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_273 : Finset (Fin 10) := literalFinset [0, 4, 8] (by decide +kernel)
noncomputable def vertices_529 : Finset (Fin 10) := literalFinset [0, 4, 9] (by decide +kernel)
noncomputable def vertices_97 : Finset (Fin 10) := literalFinset [0, 5, 6] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_134 : Finset (Fin 10) := literalFinset [1, 2, 7] (by decide +kernel)
noncomputable def vertices_262 : Finset (Fin 10) := literalFinset [1, 2, 8] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_26 : Finset (Fin 10) := literalFinset [1, 3, 4] (by decide +kernel)
noncomputable def vertices_138 : Finset (Fin 10) := literalFinset [1, 3, 7] (by decide +kernel)
noncomputable def vertices_522 : Finset (Fin 10) := literalFinset [1, 3, 9] (by decide +kernel)
noncomputable def vertices_146 : Finset (Fin 10) := literalFinset [1, 4, 7] (by decide +kernel)
noncomputable def vertices_274 : Finset (Fin 10) := literalFinset [1, 4, 8] (by decide +kernel)
noncomputable def vertices_530 : Finset (Fin 10) := literalFinset [1, 4, 9] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_196 : Finset (Fin 10) := literalFinset [2, 6, 7] (by decide +kernel)
noncomputable def vertices_324 : Finset (Fin 10) := literalFinset [2, 6, 8] (by decide +kernel)
noncomputable def vertices_580 : Finset (Fin 10) := literalFinset [2, 6, 9] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_56 : Finset (Fin 10) := literalFinset [3, 4, 5] (by decide +kernel)
noncomputable def vertices_152 : Finset (Fin 10) := literalFinset [3, 4, 7] (by decide +kernel)
noncomputable def vertices_280 : Finset (Fin 10) := literalFinset [3, 4, 8] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_552 : Finset (Fin 10) := literalFinset [3, 5, 9] (by decide +kernel)
noncomputable def vertices_392 : Finset (Fin 10) := literalFinset [3, 7, 8] (by decide +kernel)
noncomputable def vertices_648 : Finset (Fin 10) := literalFinset [3, 7, 9] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_224 : Finset (Fin 10) := literalFinset [5, 6, 7] (by decide +kernel)
noncomputable def vertices_608 : Finset (Fin 10) := literalFinset [5, 6, 9] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_535, vertices_837, vertices_313, vertices_625, vertices_481, vertices_654, vertices_454, vertices_570, vertices_154, vertices_402, vertices_740, vertices_408, vertices_424, vertices_680] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_261, vertices_517, vertices_49, vertices_273, vertices_529, vertices_97, vertices_289, vertices_321, vertices_577, vertices_134, vertices_262, vertices_518, vertices_26, vertices_138, vertices_522, vertices_146, vertices_274, vertices_530, vertices_386, vertices_196, vertices_324, vertices_580, vertices_644, vertices_56, vertices_152, vertices_280, vertices_168, vertices_296, vertices_552, vertices_392, vertices_648, vertices_560, vertices_400, vertices_224, vertices_608, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_535), (false, vertices_837), (false, vertices_313), (false, vertices_625), (false, vertices_481), (true, vertices_134), (true, vertices_26), (true, vertices_138), (true, vertices_522), (true, vertices_146), (true, vertices_386), (true, vertices_196), (true, vertices_644), (true, vertices_152), (true, vertices_168), (true, vertices_552), (true, vertices_392), (true, vertices_648), (true, vertices_400), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![15, 18, 20, 22, 24, 26, 27, 28, 29]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 16 else
  if p.val = (false, vertices_535) then 17 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_313) then 21 else
  if p.val = (false, vertices_625) then 23 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_672) then 14 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_279), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 5, 6]
  vertex := 7
  face := Sum.inl ⟨vertices_454, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_134, (by decide +kernel)⟩ ⟨vertices_454, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
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

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 2, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_654, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_134, (by decide +kernel)⟩ ⟨vertices_654, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
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
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_196, (by decide +kernel)⟩ ⟨vertices_740, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![7, 3, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_654, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_134, (by decide +kernel)⟩ ⟨vertices_654, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_454, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_134, (by decide +kernel)⟩ ⟨vertices_454, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_570, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 2, 3, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_26, (by decide +kernel)⟩ ⟨vertices_570, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_154, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 2, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_26, (by decide +kernel)⟩ ⟨vertices_154, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_402, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![0, 3, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_146, (by decide +kernel)⟩ ⟨vertices_402, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_740, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![1, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_196, (by decide +kernel)⟩ ⟨vertices_740, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_408, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![2, 3, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_152, (by decide +kernel)⟩ ⟨vertices_408, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_424, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![2, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_168, (by decide +kernel)⟩ ⟨vertices_424, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet8 : boundary.facets := ⟨vertices_680, by decide +kernel⟩
noncomputable def cover8 : FacetCoverage heightProof coverFacet8 :=
  .fundamental ![2, 4, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_168, (by decide +kernel)⟩ ⟨vertices_680, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coveringFacets : Fin 9 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6, coverFacet7, coverFacet8]
noncomputable def coveringProof (j : Fin 9) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (Fin.cases cover7 (Fin.cases cover8 (fun i => Fin.elim0 i)))))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 9, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0276

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e10q1_0277.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0277

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_395 : Finset (Fin 10) := literalFinset [0, 1, 3, 7, 8] (by decide +kernel)
noncomputable def vertices_333 : Finset (Fin 10) := literalFinset [0, 2, 3, 6, 8] (by decide +kernel)
noncomputable def vertices_653 : Finset (Fin 10) := literalFinset [0, 2, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_597 : Finset (Fin 10) := literalFinset [0, 2, 4, 6, 9] (by decide +kernel)
noncomputable def vertices_369 : Finset (Fin 10) := literalFinset [0, 4, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_401 : Finset (Fin 10) := literalFinset [0, 4, 7, 8] (by decide +kernel)
noncomputable def vertices_657 : Finset (Fin 10) := literalFinset [0, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_302 : Finset (Fin 10) := literalFinset [1, 2, 3, 5, 8] (by decide +kernel)
noncomputable def vertices_558 : Finset (Fin 10) := literalFinset [1, 2, 3, 5, 9] (by decide +kernel)
noncomputable def vertices_666 : Finset (Fin 10) := literalFinset [1, 3, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_626 : Finset (Fin 10) := literalFinset [1, 4, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_178 : Finset (Fin 10) := literalFinset [1, 4, 5, 7] (by decide +kernel)
noncomputable def vertices_418 : Finset (Fin 10) := literalFinset [1, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_868 : Finset (Fin 10) := literalFinset [2, 5, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_432 : Finset (Fin 10) := literalFinset [4, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_13 : Finset (Fin 10) := literalFinset [0, 2, 3] (by decide +kernel)
noncomputable def vertices_69 : Finset (Fin 10) := literalFinset [0, 2, 6] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_265 : Finset (Fin 10) := literalFinset [0, 3, 8] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_145 : Finset (Fin 10) := literalFinset [0, 4, 7] (by decide +kernel)
noncomputable def vertices_273 : Finset (Fin 10) := literalFinset [0, 4, 8] (by decide +kernel)
noncomputable def vertices_529 : Finset (Fin 10) := literalFinset [0, 4, 9] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_385 : Finset (Fin 10) := literalFinset [0, 7, 8] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_46 : Finset (Fin 10) := literalFinset [1, 2, 3, 5] (by decide +kernel)
noncomputable def vertices_138 : Finset (Fin 10) := literalFinset [1, 3, 7] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_522 : Finset (Fin 10) := literalFinset [1, 3, 9] (by decide +kernel)
noncomputable def vertices_50 : Finset (Fin 10) := literalFinset [1, 4, 5] (by decide +kernel)
noncomputable def vertices_146 : Finset (Fin 10) := literalFinset [1, 4, 7] (by decide +kernel)
noncomputable def vertices_530 : Finset (Fin 10) := literalFinset [1, 4, 9] (by decide +kernel)
noncomputable def vertices_162 : Finset (Fin 10) := literalFinset [1, 5, 7] (by decide +kernel)
noncomputable def vertices_290 : Finset (Fin 10) := literalFinset [1, 5, 8] (by decide +kernel)
noncomputable def vertices_546 : Finset (Fin 10) := literalFinset [1, 5, 9] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_268 : Finset (Fin 10) := literalFinset [2, 3, 8] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_292 : Finset (Fin 10) := literalFinset [2, 5, 8] (by decide +kernel)
noncomputable def vertices_548 : Finset (Fin 10) := literalFinset [2, 5, 9] (by decide +kernel)
noncomputable def vertices_324 : Finset (Fin 10) := literalFinset [2, 6, 8] (by decide +kernel)
noncomputable def vertices_580 : Finset (Fin 10) := literalFinset [2, 6, 9] (by decide +kernel)
noncomputable def vertices_648 : Finset (Fin 10) := literalFinset [3, 7, 9] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_608 : Finset (Fin 10) := literalFinset [5, 6, 9] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_333, vertices_653, vertices_597, vertices_369, vertices_401, vertices_657, vertices_302, vertices_558, vertices_666, vertices_626, vertices_178, vertices_418, vertices_868, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_517, vertices_137, vertices_265, vertices_81, vertices_145, vertices_273, vertices_529, vertices_321, vertices_385, vertices_641, vertices_46, vertices_138, vertices_266, vertices_522, vertices_50, vertices_146, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_268, vertices_524, vertices_292, vertices_548, vertices_324, vertices_580, vertices_648, vertices_112, vertices_176, vertices_304, vertices_592, vertices_400, vertices_656, vertices_352, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_333), (false, vertices_653), (false, vertices_597), (false, vertices_369), (false, vertices_401), (false, vertices_657), (true, vertices_46), (true, vertices_522), (true, vertices_50), (true, vertices_146), (true, vertices_530), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_292), (true, vertices_548), (true, vertices_176), (true, vertices_608), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![14, 17, 21, 22, 24, 25, 26, 27, 28]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 15 else
  if p.val = (false, vertices_333) then 18 else
  if p.val = (false, vertices_653) then 19 else
  if p.val = (false, vertices_597) then 20 else
  if p.val = (false, vertices_369) then 23 else
  if p.val = (false, vertices_401) then 0 else
  if p.val = (false, vertices_657) then 1 else
  if p.val = (true, vertices_46) then 16 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_401), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_657), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_46), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
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
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_138, (by decide +kernel)⟩ ⟨vertices_666, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 3
  frame := ![0, 1, 2]
  vertex := 4
  face := Sum.inr ⟨vertices_46, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_46, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 3, 4, 5]
  vertex := 8
  face := Sum.inl ⟨vertices_626, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_50, (by decide +kernel)⟩ ⟨vertices_626, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
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
noncomputable def pivot : Fin 4 → Fin 9 := ![6, 2, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_302, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_46, (by decide +kernel)⟩ ⟨vertices_302, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_558, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 2, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_46, (by decide +kernel)⟩ ⟨vertices_558, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_666, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 2, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_138, (by decide +kernel)⟩ ⟨vertices_666, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_626, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![0, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_50, (by decide +kernel)⟩ ⟨vertices_626, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_178, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![0, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_50, (by decide +kernel)⟩ ⟨vertices_178, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_418, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![0, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_162, (by decide +kernel)⟩ ⟨vertices_418, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_868, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![1, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_292, (by decide +kernel)⟩ ⟨vertices_868, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0277

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e10q1_0278.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0278

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_279 : Finset (Fin 10) := literalFinset [0, 1, 2, 4, 8] (by decide +kernel)
noncomputable def vertices_535 : Finset (Fin 10) := literalFinset [0, 1, 2, 4, 9] (by decide +kernel)
noncomputable def vertices_557 : Finset (Fin 10) := literalFinset [0, 2, 3, 5, 9] (by decide +kernel)
noncomputable def vertices_421 : Finset (Fin 10) := literalFinset [0, 2, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_313 : Finset (Fin 10) := literalFinset [0, 3, 4, 5, 8] (by decide +kernel)
noncomputable def vertices_601 : Finset (Fin 10) := literalFinset [0, 3, 4, 6, 9] (by decide +kernel)
noncomputable def vertices_678 : Finset (Fin 10) := literalFinset [1, 2, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_454 : Finset (Fin 10) := literalFinset [1, 2, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_714 : Finset (Fin 10) := literalFinset [1, 3, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_850 : Finset (Fin 10) := literalFinset [1, 4, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_216 : Finset (Fin 10) := literalFinset [3, 4, 6, 7] (by decide +kernel)
noncomputable def vertices_408 : Finset (Fin 10) := literalFinset [3, 4, 7, 8] (by decide +kernel)
noncomputable def vertices_424 : Finset (Fin 10) := literalFinset [3, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_680 : Finset (Fin 10) := literalFinset [3, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_464 : Finset (Fin 10) := literalFinset [4, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_23 : Finset (Fin 10) := literalFinset [0, 1, 2, 4] (by decide +kernel)
noncomputable def vertices_37 : Finset (Fin 10) := literalFinset [0, 2, 5] (by decide +kernel)
noncomputable def vertices_261 : Finset (Fin 10) := literalFinset [0, 2, 8] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_25 : Finset (Fin 10) := literalFinset [0, 3, 4] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_521 : Finset (Fin 10) := literalFinset [0, 3, 9] (by decide +kernel)
noncomputable def vertices_273 : Finset (Fin 10) := literalFinset [0, 4, 8] (by decide +kernel)
noncomputable def vertices_529 : Finset (Fin 10) := literalFinset [0, 4, 9] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_134 : Finset (Fin 10) := literalFinset [1, 2, 7] (by decide +kernel)
noncomputable def vertices_262 : Finset (Fin 10) := literalFinset [1, 2, 8] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_274 : Finset (Fin 10) := literalFinset [1, 4, 8] (by decide +kernel)
noncomputable def vertices_530 : Finset (Fin 10) := literalFinset [1, 4, 9] (by decide +kernel)
noncomputable def vertices_194 : Finset (Fin 10) := literalFinset [1, 6, 7] (by decide +kernel)
noncomputable def vertices_322 : Finset (Fin 10) := literalFinset [1, 6, 8] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_164 : Finset (Fin 10) := literalFinset [2, 5, 7] (by decide +kernel)
noncomputable def vertices_548 : Finset (Fin 10) := literalFinset [2, 5, 9] (by decide +kernel)
noncomputable def vertices_388 : Finset (Fin 10) := literalFinset [2, 7, 8] (by decide +kernel)
noncomputable def vertices_88 : Finset (Fin 10) := literalFinset [3, 4, 6] (by decide +kernel)
noncomputable def vertices_152 : Finset (Fin 10) := literalFinset [3, 4, 7] (by decide +kernel)
noncomputable def vertices_280 : Finset (Fin 10) := literalFinset [3, 4, 8] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_552 : Finset (Fin 10) := literalFinset [3, 5, 9] (by decide +kernel)
noncomputable def vertices_200 : Finset (Fin 10) := literalFinset [3, 6, 7] (by decide +kernel)
noncomputable def vertices_584 : Finset (Fin 10) := literalFinset [3, 6, 9] (by decide +kernel)
noncomputable def vertices_392 : Finset (Fin 10) := literalFinset [3, 7, 8] (by decide +kernel)
noncomputable def vertices_648 : Finset (Fin 10) := literalFinset [3, 7, 9] (by decide +kernel)
noncomputable def vertices_208 : Finset (Fin 10) := literalFinset [4, 6, 7] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_535, vertices_557, vertices_421, vertices_313, vertices_601, vertices_678, vertices_454, vertices_714, vertices_850, vertices_216, vertices_408, vertices_424, vertices_680, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_37, vertices_261, vertices_517, vertices_25, vertices_41, vertices_521, vertices_273, vertices_529, vertices_289, vertices_134, vertices_262, vertices_518, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_642, vertices_164, vertices_548, vertices_388, vertices_88, vertices_152, vertices_280, vertices_168, vertices_296, vertices_552, vertices_200, vertices_584, vertices_392, vertices_648, vertices_208, vertices_336, vertices_592, vertices_400, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_535), (false, vertices_557), (false, vertices_421), (false, vertices_313), (false, vertices_601), (true, vertices_134), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_642), (true, vertices_152), (true, vertices_168), (true, vertices_200), (true, vertices_392), (true, vertices_648), (true, vertices_208), (true, vertices_336), (true, vertices_400), (true, vertices_672), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![15, 18, 21, 24, 25, 26, 27, 28, 29]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 16 else
  if p.val = (false, vertices_535) then 17 else
  if p.val = (false, vertices_557) then 19 else
  if p.val = (false, vertices_421) then 20 else
  if p.val = (false, vertices_313) then 22 else
  if p.val = (false, vertices_601) then 23 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_392) then 8 else
  if p.val = (true, vertices_648) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_672) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_279), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 4, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_678, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_134, (by decide +kernel)⟩ ⟨vertices_678, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 5, 6]
  vertex := 7
  face := Sum.inl ⟨vertices_454, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_134, (by decide +kernel)⟩ ⟨vertices_454, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
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
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_194, (by decide +kernel)⟩ ⟨vertices_714, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
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
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_274, (by decide +kernel)⟩ ⟨vertices_850, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![4, 1, 2, 0]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_678, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_134, (by decide +kernel)⟩ ⟨vertices_678, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_454, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_134, (by decide +kernel)⟩ ⟨vertices_454, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_714, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 2, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_194, (by decide +kernel)⟩ ⟨vertices_714, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_850, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![0, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_274, (by decide +kernel)⟩ ⟨vertices_850, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_216, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![2, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_88, (by decide +kernel)⟩ ⟨vertices_216, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_408, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![2, 3, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_152, (by decide +kernel)⟩ ⟨vertices_408, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_424, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![2, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_168, (by decide +kernel)⟩ ⟨vertices_424, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_680, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![2, 4, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_168, (by decide +kernel)⟩ ⟨vertices_680, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet8 : boundary.facets := ⟨vertices_464, by decide +kernel⟩
noncomputable def cover8 : FacetCoverage heightProof coverFacet8 :=
  .fundamental ![3, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_208, (by decide +kernel)⟩ ⟨vertices_464, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coveringFacets : Fin 9 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6, coverFacet7, coverFacet8]
noncomputable def coveringProof (j : Fin 9) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (Fin.cases cover7 (Fin.cases cover8 (fun i => Fin.elim0 i)))))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 9, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0278

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e10q1_0279.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0279

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_647 : Finset (Fin 10) := literalFinset [0, 1, 2, 7, 9] (by decide +kernel)
noncomputable def vertices_109 : Finset (Fin 10) := literalFinset [0, 2, 3, 5, 6] (by decide +kernel)
noncomputable def vertices_589 : Finset (Fin 10) := literalFinset [0, 2, 3, 6, 9] (by decide +kernel)
noncomputable def vertices_421 : Finset (Fin 10) := literalFinset [0, 2, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_313 : Finset (Fin 10) := literalFinset [0, 3, 4, 5, 8] (by decide +kernel)
noncomputable def vertices_905 : Finset (Fin 10) := literalFinset [0, 3, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_598 : Finset (Fin 10) := literalFinset [1, 2, 4, 6, 9] (by decide +kernel)
noncomputable def vertices_198 : Finset (Fin 10) := literalFinset [1, 2, 6, 7] (by decide +kernel)
noncomputable def vertices_794 : Finset (Fin 10) := literalFinset [1, 3, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_338 : Finset (Fin 10) := literalFinset [1, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_482 : Finset (Fin 10) := literalFinset [1, 5, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_898 : Finset (Fin 10) := literalFinset [1, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_228 : Finset (Fin 10) := literalFinset [2, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_632 : Finset (Fin 10) := literalFinset [3, 4, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_368 : Finset (Fin 10) := literalFinset [4, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_77 : Finset (Fin 10) := literalFinset [0, 2, 3, 6] (by decide +kernel)
noncomputable def vertices_37 : Finset (Fin 10) := literalFinset [0, 2, 5] (by decide +kernel)
noncomputable def vertices_133 : Finset (Fin 10) := literalFinset [0, 2, 7] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_265 : Finset (Fin 10) := literalFinset [0, 3, 8] (by decide +kernel)
noncomputable def vertices_521 : Finset (Fin 10) := literalFinset [0, 3, 9] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_385 : Finset (Fin 10) := literalFinset [0, 7, 8] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_70 : Finset (Fin 10) := literalFinset [1, 2, 6] (by decide +kernel)
noncomputable def vertices_134 : Finset (Fin 10) := literalFinset [1, 2, 7] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_82 : Finset (Fin 10) := literalFinset [1, 4, 6] (by decide +kernel)
noncomputable def vertices_274 : Finset (Fin 10) := literalFinset [1, 4, 8] (by decide +kernel)
noncomputable def vertices_530 : Finset (Fin 10) := literalFinset [1, 4, 9] (by decide +kernel)
noncomputable def vertices_194 : Finset (Fin 10) := literalFinset [1, 6, 7] (by decide +kernel)
noncomputable def vertices_322 : Finset (Fin 10) := literalFinset [1, 6, 8] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_100 : Finset (Fin 10) := literalFinset [2, 5, 6] (by decide +kernel)
noncomputable def vertices_164 : Finset (Fin 10) := literalFinset [2, 5, 7] (by decide +kernel)
noncomputable def vertices_196 : Finset (Fin 10) := literalFinset [2, 6, 7] (by decide +kernel)
noncomputable def vertices_580 : Finset (Fin 10) := literalFinset [2, 6, 9] (by decide +kernel)
noncomputable def vertices_56 : Finset (Fin 10) := literalFinset [3, 4, 5] (by decide +kernel)
noncomputable def vertices_280 : Finset (Fin 10) := literalFinset [3, 4, 8] (by decide +kernel)
noncomputable def vertices_536 : Finset (Fin 10) := literalFinset [3, 4, 9] (by decide +kernel)
noncomputable def vertices_104 : Finset (Fin 10) := literalFinset [3, 5, 6] (by decide +kernel)
noncomputable def vertices_584 : Finset (Fin 10) := literalFinset [3, 6, 9] (by decide +kernel)
noncomputable def vertices_776 : Finset (Fin 10) := literalFinset [3, 8, 9] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_224 : Finset (Fin 10) := literalFinset [5, 6, 7] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_109, vertices_589, vertices_421, vertices_313, vertices_905, vertices_598, vertices_198, vertices_794, vertices_338, vertices_482, vertices_898, vertices_228, vertices_632, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_77, vertices_37, vertices_133, vertices_517, vertices_41, vertices_265, vertices_521, vertices_289, vertices_385, vertices_641, vertices_70, vertices_134, vertices_518, vertices_82, vertices_274, vertices_530, vertices_194, vertices_322, vertices_386, vertices_642, vertices_770, vertices_100, vertices_164, vertices_196, vertices_580, vertices_56, vertices_280, vertices_536, vertices_104, vertices_584, vertices_776, vertices_112, vertices_304, vertices_336, vertices_592, vertices_224, vertices_352, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_109), (false, vertices_589), (false, vertices_421), (false, vertices_313), (false, vertices_905), (true, vertices_70), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_194), (true, vertices_322), (true, vertices_386), (true, vertices_770), (true, vertices_196), (true, vertices_536), (true, vertices_112), (true, vertices_336), (true, vertices_592), (true, vertices_224), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![15, 17, 21, 24, 25, 26, 27, 28, 29]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 16 else
  if p.val = (false, vertices_109) then 18 else
  if p.val = (false, vertices_589) then 19 else
  if p.val = (false, vertices_421) then 20 else
  if p.val = (false, vertices_313) then 22 else
  if p.val = (false, vertices_905) then 23 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_352) then 14 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 3, 5]
  vertex := 8
  face := Sum.inl ⟨vertices_598, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_70, (by decide +kernel)⟩ ⟨vertices_598, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 4, 5, 6]
  vertex := 7
  face := Sum.inl ⟨vertices_482, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_194, (by decide +kernel)⟩ ⟨vertices_482, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_794, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_274, (by decide +kernel)⟩ ⟨vertices_794, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
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

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_598, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_70, (by decide +kernel)⟩ ⟨vertices_598, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_198, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 1, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_70, (by decide +kernel)⟩ ⟨vertices_198, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_794, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 2, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_274, (by decide +kernel)⟩ ⟨vertices_794, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_338, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_82, (by decide +kernel)⟩ ⟨vertices_338, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_482, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![0, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_194, (by decide +kernel)⟩ ⟨vertices_482, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_898, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![0, 6, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_386, (by decide +kernel)⟩ ⟨vertices_898, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_228, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![1, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_100, (by decide +kernel)⟩ ⟨vertices_228, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_632, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .oneRow ![2, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_632, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet8 : boundary.facets := ⟨vertices_368, by decide +kernel⟩
noncomputable def cover8 : FacetCoverage heightProof coverFacet8 :=
  .fundamental ![3, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_368, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coveringFacets : Fin 9 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6, coverFacet7, coverFacet8]
noncomputable def coveringProof (j : Fin 9) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (Fin.cases cover7 (Fin.cases cover8 (fun i => Fin.elim0 i)))))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 9, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0279

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e10q1_0280.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0280

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_279 : Finset (Fin 10) := literalFinset [0, 1, 2, 4, 8] (by decide +kernel)
noncomputable def vertices_535 : Finset (Fin 10) := literalFinset [0, 1, 2, 4, 9] (by decide +kernel)
noncomputable def vertices_899 : Finset (Fin 10) := literalFinset [0, 1, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_357 : Finset (Fin 10) := literalFinset [0, 2, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_709 : Finset (Fin 10) := literalFinset [0, 2, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_457 : Finset (Fin 10) := literalFinset [0, 3, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_570 : Finset (Fin 10) := literalFinset [1, 3, 4, 5, 9] (by decide +kernel)
noncomputable def vertices_154 : Finset (Fin 10) := literalFinset [1, 3, 4, 7] (by decide +kernel)
noncomputable def vertices_714 : Finset (Fin 10) := literalFinset [1, 3, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_402 : Finset (Fin 10) := literalFinset [1, 4, 7, 8] (by decide +kernel)
noncomputable def vertices_316 : Finset (Fin 10) := literalFinset [2, 3, 4, 5, 8] (by decide +kernel)
noncomputable def vertices_628 : Finset (Fin 10) := literalFinset [2, 4, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_408 : Finset (Fin 10) := literalFinset [3, 4, 7, 8] (by decide +kernel)
noncomputable def vertices_360 : Finset (Fin 10) := literalFinset [3, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_616 : Finset (Fin 10) := literalFinset [3, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_23 : Finset (Fin 10) := literalFinset [0, 1, 2, 4] (by decide +kernel)
noncomputable def vertices_259 : Finset (Fin 10) := literalFinset [0, 1, 8] (by decide +kernel)
noncomputable def vertices_515 : Finset (Fin 10) := literalFinset [0, 1, 9] (by decide +kernel)
noncomputable def vertices_69 : Finset (Fin 10) := literalFinset [0, 2, 6] (by decide +kernel)
noncomputable def vertices_261 : Finset (Fin 10) := literalFinset [0, 2, 8] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_193 : Finset (Fin 10) := literalFinset [0, 6, 7] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_385 : Finset (Fin 10) := literalFinset [0, 7, 8] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_26 : Finset (Fin 10) := literalFinset [1, 3, 4] (by decide +kernel)
noncomputable def vertices_138 : Finset (Fin 10) := literalFinset [1, 3, 7] (by decide +kernel)
noncomputable def vertices_522 : Finset (Fin 10) := literalFinset [1, 3, 9] (by decide +kernel)
noncomputable def vertices_146 : Finset (Fin 10) := literalFinset [1, 4, 7] (by decide +kernel)
noncomputable def vertices_274 : Finset (Fin 10) := literalFinset [1, 4, 8] (by decide +kernel)
noncomputable def vertices_530 : Finset (Fin 10) := literalFinset [1, 4, 9] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_532 : Finset (Fin 10) := literalFinset [2, 4, 9] (by decide +kernel)
noncomputable def vertices_100 : Finset (Fin 10) := literalFinset [2, 5, 6] (by decide +kernel)
noncomputable def vertices_292 : Finset (Fin 10) := literalFinset [2, 5, 8] (by decide +kernel)
noncomputable def vertices_580 : Finset (Fin 10) := literalFinset [2, 6, 9] (by decide +kernel)
noncomputable def vertices_56 : Finset (Fin 10) := literalFinset [3, 4, 5] (by decide +kernel)
noncomputable def vertices_152 : Finset (Fin 10) := literalFinset [3, 4, 7] (by decide +kernel)
noncomputable def vertices_280 : Finset (Fin 10) := literalFinset [3, 4, 8] (by decide +kernel)
noncomputable def vertices_104 : Finset (Fin 10) := literalFinset [3, 5, 6] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_552 : Finset (Fin 10) := literalFinset [3, 5, 9] (by decide +kernel)
noncomputable def vertices_200 : Finset (Fin 10) := literalFinset [3, 6, 7] (by decide +kernel)
noncomputable def vertices_328 : Finset (Fin 10) := literalFinset [3, 6, 8] (by decide +kernel)
noncomputable def vertices_584 : Finset (Fin 10) := literalFinset [3, 6, 9] (by decide +kernel)
noncomputable def vertices_392 : Finset (Fin 10) := literalFinset [3, 7, 8] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_608 : Finset (Fin 10) := literalFinset [5, 6, 9] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_535, vertices_899, vertices_357, vertices_709, vertices_457, vertices_570, vertices_154, vertices_714, vertices_402, vertices_316, vertices_628, vertices_408, vertices_360, vertices_616] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_259, vertices_515, vertices_69, vertices_261, vertices_517, vertices_193, vertices_321, vertices_385, vertices_641, vertices_26, vertices_138, vertices_522, vertices_146, vertices_274, vertices_530, vertices_386, vertices_642, vertices_52, vertices_276, vertices_532, vertices_100, vertices_292, vertices_580, vertices_56, vertices_152, vertices_280, vertices_104, vertices_296, vertices_552, vertices_200, vertices_328, vertices_584, vertices_392, vertices_560, vertices_400, vertices_352, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_535), (false, vertices_899), (false, vertices_357), (false, vertices_709), (false, vertices_457), (true, vertices_26), (true, vertices_138), (true, vertices_522), (true, vertices_146), (true, vertices_52), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_104), (true, vertices_296), (true, vertices_552), (true, vertices_584), (true, vertices_560), (true, vertices_400), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![15, 19, 22, 24, 25, 26, 27, 28, 29]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 16 else
  if p.val = (false, vertices_535) then 17 else
  if p.val = (false, vertices_899) then 18 else
  if p.val = (false, vertices_357) then 20 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_457) then 23 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_56) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_608) then 14 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_279), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
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

noncomputable def row1 : HeightRow boundary where
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

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 3, 4]
  vertex := 7
  face := Sum.inl ⟨vertices_316, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_316, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
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
noncomputable def pivot : Fin 4 → Fin 9 := ![6, 0, 2, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_570, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 2, 3, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_26, (by decide +kernel)⟩ ⟨vertices_570, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_154, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 2, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_26, (by decide +kernel)⟩ ⟨vertices_154, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_714, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 2, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_138, (by decide +kernel)⟩ ⟨vertices_714, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_402, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 3, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_146, (by decide +kernel)⟩ ⟨vertices_402, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_316, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![1, 2, 3, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_316, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_628, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![1, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_628, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_408, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![2, 3, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_152, (by decide +kernel)⟩ ⟨vertices_408, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_360, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![2, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_104, (by decide +kernel)⟩ ⟨vertices_360, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet8 : boundary.facets := ⟨vertices_616, by decide +kernel⟩
noncomputable def cover8 : FacetCoverage heightProof coverFacet8 :=
  .fundamental ![2, 4, 5, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_104, (by decide +kernel)⟩ ⟨vertices_616, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coveringFacets : Fin 9 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6, coverFacet7, coverFacet8]
noncomputable def coveringProof (j : Fin 9) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (Fin.cases cover7 (Fin.cases cover8 (fun i => Fin.elim0 i)))))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 9, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0280

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e10q1_0281.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0281

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_647 : Finset (Fin 10) := literalFinset [0, 1, 2, 7, 9] (by decide +kernel)
noncomputable def vertices_775 : Finset (Fin 10) := literalFinset [0, 1, 2, 8, 9] (by decide +kernel)
noncomputable def vertices_301 : Finset (Fin 10) := literalFinset [0, 2, 3, 5, 8] (by decide +kernel)
noncomputable def vertices_205 : Finset (Fin 10) := literalFinset [0, 2, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_841 : Finset (Fin 10) := literalFinset [0, 3, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_721 : Finset (Fin 10) := literalFinset [0, 4, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_174 : Finset (Fin 10) := literalFinset [1, 2, 3, 5, 7] (by decide +kernel)
noncomputable def vertices_310 : Finset (Fin 10) := literalFinset [1, 2, 4, 5, 8] (by decide +kernel)
noncomputable def vertices_242 : Finset (Fin 10) := literalFinset [1, 4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_402 : Finset (Fin 10) := literalFinset [1, 4, 7, 8] (by decide +kernel)
noncomputable def vertices_898 : Finset (Fin 10) := literalFinset [1, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_232 : Finset (Fin 10) := literalFinset [3, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_360 : Finset (Fin 10) := literalFinset [3, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_880 : Finset (Fin 10) := literalFinset [4, 5, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_912 : Finset (Fin 10) := literalFinset [4, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_519 : Finset (Fin 10) := literalFinset [0, 1, 2, 9] (by decide +kernel)
noncomputable def vertices_13 : Finset (Fin 10) := literalFinset [0, 2, 3] (by decide +kernel)
noncomputable def vertices_133 : Finset (Fin 10) := literalFinset [0, 2, 7] (by decide +kernel)
noncomputable def vertices_261 : Finset (Fin 10) := literalFinset [0, 2, 8] (by decide +kernel)
noncomputable def vertices_73 : Finset (Fin 10) := literalFinset [0, 3, 6] (by decide +kernel)
noncomputable def vertices_265 : Finset (Fin 10) := literalFinset [0, 3, 8] (by decide +kernel)
noncomputable def vertices_193 : Finset (Fin 10) := literalFinset [0, 6, 7] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_38 : Finset (Fin 10) := literalFinset [1, 2, 5] (by decide +kernel)
noncomputable def vertices_134 : Finset (Fin 10) := literalFinset [1, 2, 7] (by decide +kernel)
noncomputable def vertices_262 : Finset (Fin 10) := literalFinset [1, 2, 8] (by decide +kernel)
noncomputable def vertices_50 : Finset (Fin 10) := literalFinset [1, 4, 5] (by decide +kernel)
noncomputable def vertices_146 : Finset (Fin 10) := literalFinset [1, 4, 7] (by decide +kernel)
noncomputable def vertices_274 : Finset (Fin 10) := literalFinset [1, 4, 8] (by decide +kernel)
noncomputable def vertices_162 : Finset (Fin 10) := literalFinset [1, 5, 7] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_140 : Finset (Fin 10) := literalFinset [2, 3, 7] (by decide +kernel)
noncomputable def vertices_292 : Finset (Fin 10) := literalFinset [2, 5, 8] (by decide +kernel)
noncomputable def vertices_104 : Finset (Fin 10) := literalFinset [3, 5, 6] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_200 : Finset (Fin 10) := literalFinset [3, 6, 7] (by decide +kernel)
noncomputable def vertices_328 : Finset (Fin 10) := literalFinset [3, 6, 8] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_208 : Finset (Fin 10) := literalFinset [4, 6, 7] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_784 : Finset (Fin 10) := literalFinset [4, 8, 9] (by decide +kernel)
noncomputable def vertices_224 : Finset (Fin 10) := literalFinset [5, 6, 7] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_775, vertices_301, vertices_205, vertices_841, vertices_721, vertices_174, vertices_310, vertices_242, vertices_402, vertices_898, vertices_232, vertices_360, vertices_880, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_519, vertices_13, vertices_133, vertices_261, vertices_73, vertices_265, vertices_193, vertices_577, vertices_641, vertices_769, vertices_38, vertices_134, vertices_262, vertices_50, vertices_146, vertices_274, vertices_162, vertices_386, vertices_642, vertices_770, vertices_44, vertices_140, vertices_292, vertices_104, vertices_168, vertices_296, vertices_200, vertices_328, vertices_112, vertices_304, vertices_208, vertices_592, vertices_400, vertices_656, vertices_784, vertices_224, vertices_352, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_775), (false, vertices_301), (false, vertices_205), (false, vertices_841), (false, vertices_721), (true, vertices_38), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_162), (true, vertices_386), (true, vertices_104), (true, vertices_168), (true, vertices_112), (true, vertices_304), (true, vertices_400), (true, vertices_784), (true, vertices_224), (true, vertices_352), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![15, 18, 21, 23, 25, 26, 27, 28, 29]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 16 else
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_301) then 19 else
  if p.val = (false, vertices_205) then 20 else
  if p.val = (false, vertices_841) then 22 else
  if p.val = (false, vertices_721) then 24 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_352) then 13 else
  if p.val = (true, vertices_896) then 14 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 2, 4]
  vertex := 6
  face := Sum.inl ⟨vertices_174, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_38, (by decide +kernel)⟩ ⟨vertices_174, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
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
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_38, (by decide +kernel)⟩ ⟨vertices_310, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
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
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_50, (by decide +kernel)⟩ ⟨vertices_242, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
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
noncomputable def pivot : Fin 4 → Fin 9 := ![2, 1, 0, 3]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_174, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_38, (by decide +kernel)⟩ ⟨vertices_174, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_310, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 3, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_38, (by decide +kernel)⟩ ⟨vertices_310, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_242, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_50, (by decide +kernel)⟩ ⟨vertices_242, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_402, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 3, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_146, (by decide +kernel)⟩ ⟨vertices_402, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_898, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![0, 6, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_386, (by decide +kernel)⟩ ⟨vertices_898, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_232, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![2, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_104, (by decide +kernel)⟩ ⟨vertices_232, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_360, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![2, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_104, (by decide +kernel)⟩ ⟨vertices_360, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_880, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .oneRow ![3, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_880, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet8 : boundary.facets := ⟨vertices_912, by decide +kernel⟩
noncomputable def cover8 : FacetCoverage heightProof coverFacet8 :=
  .fundamental ![3, 6, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_400, (by decide +kernel)⟩ ⟨vertices_912, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coveringFacets : Fin 9 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6, coverFacet7, coverFacet8]
noncomputable def coveringProof (j : Fin 9) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (Fin.cases cover7 (Fin.cases cover8 (fun i => Fin.elim0 i)))))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 9, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0281

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m15e10q1_0282.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0282

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_307 : Finset (Fin 10) := literalFinset [0, 1, 4, 5, 8] (by decide +kernel)
noncomputable def vertices_285 : Finset (Fin 10) := literalFinset [0, 2, 3, 4, 8] (by decide +kernel)
noncomputable def vertices_541 : Finset (Fin 10) := literalFinset [0, 2, 3, 4, 9] (by decide +kernel)
noncomputable def vertices_837 : Finset (Fin 10) := literalFinset [0, 2, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_625 : Finset (Fin 10) := literalFinset [0, 4, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_481 : Finset (Fin 10) := literalFinset [0, 5, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_654 : Finset (Fin 10) := literalFinset [1, 2, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_570 : Finset (Fin 10) := literalFinset [1, 3, 4, 5, 9] (by decide +kernel)
noncomputable def vertices_282 : Finset (Fin 10) := literalFinset [1, 3, 4, 8] (by decide +kernel)
noncomputable def vertices_458 : Finset (Fin 10) := literalFinset [1, 3, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_418 : Finset (Fin 10) := literalFinset [1, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_674 : Finset (Fin 10) := literalFinset [1, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_204 : Finset (Fin 10) := literalFinset [2, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_332 : Finset (Fin 10) := literalFinset [2, 3, 6, 8] (by decide +kernel)
noncomputable def vertices_740 : Finset (Fin 10) := literalFinset [2, 5, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_29 : Finset (Fin 10) := literalFinset [0, 2, 3, 4] (by decide +kernel)
noncomputable def vertices_261 : Finset (Fin 10) := literalFinset [0, 2, 8] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_273 : Finset (Fin 10) := literalFinset [0, 4, 8] (by decide +kernel)
noncomputable def vertices_529 : Finset (Fin 10) := literalFinset [0, 4, 9] (by decide +kernel)
noncomputable def vertices_97 : Finset (Fin 10) := literalFinset [0, 5, 6] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_26 : Finset (Fin 10) := literalFinset [1, 3, 4] (by decide +kernel)
noncomputable def vertices_138 : Finset (Fin 10) := literalFinset [1, 3, 7] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_522 : Finset (Fin 10) := literalFinset [1, 3, 9] (by decide +kernel)
noncomputable def vertices_50 : Finset (Fin 10) := literalFinset [1, 4, 5] (by decide +kernel)
noncomputable def vertices_274 : Finset (Fin 10) := literalFinset [1, 4, 8] (by decide +kernel)
noncomputable def vertices_162 : Finset (Fin 10) := literalFinset [1, 5, 7] (by decide +kernel)
noncomputable def vertices_290 : Finset (Fin 10) := literalFinset [1, 5, 8] (by decide +kernel)
noncomputable def vertices_546 : Finset (Fin 10) := literalFinset [1, 5, 9] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_76 : Finset (Fin 10) := literalFinset [2, 3, 6] (by decide +kernel)
noncomputable def vertices_140 : Finset (Fin 10) := literalFinset [2, 3, 7] (by decide +kernel)
noncomputable def vertices_268 : Finset (Fin 10) := literalFinset [2, 3, 8] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_196 : Finset (Fin 10) := literalFinset [2, 6, 7] (by decide +kernel)
noncomputable def vertices_324 : Finset (Fin 10) := literalFinset [2, 6, 8] (by decide +kernel)
noncomputable def vertices_580 : Finset (Fin 10) := literalFinset [2, 6, 9] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_280 : Finset (Fin 10) := literalFinset [3, 4, 8] (by decide +kernel)
noncomputable def vertices_536 : Finset (Fin 10) := literalFinset [3, 4, 9] (by decide +kernel)
noncomputable def vertices_200 : Finset (Fin 10) := literalFinset [3, 6, 7] (by decide +kernel)
noncomputable def vertices_328 : Finset (Fin 10) := literalFinset [3, 6, 8] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_224 : Finset (Fin 10) := literalFinset [5, 6, 7] (by decide +kernel)
noncomputable def vertices_608 : Finset (Fin 10) := literalFinset [5, 6, 9] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_285, vertices_541, vertices_837, vertices_625, vertices_481, vertices_654, vertices_570, vertices_282, vertices_458, vertices_418, vertices_674, vertices_204, vertices_332, vertices_740] (by decide +kernel)
  polygons := literalFinset [vertices_29, vertices_261, vertices_517, vertices_49, vertices_273, vertices_529, vertices_97, vertices_289, vertices_321, vertices_577, vertices_26, vertices_138, vertices_266, vertices_522, vertices_50, vertices_274, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_76, vertices_140, vertices_268, vertices_524, vertices_196, vertices_324, vertices_580, vertices_644, vertices_280, vertices_536, vertices_200, vertices_328, vertices_560, vertices_224, vertices_608, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_285), (false, vertices_541), (false, vertices_837), (false, vertices_625), (false, vertices_481), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_162), (true, vertices_546), (true, vertices_386), (true, vertices_642), (true, vertices_76), (true, vertices_140), (true, vertices_196), (true, vertices_644), (true, vertices_200), (true, vertices_328), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![15, 17, 21, 22, 24, 26, 27, 28, 29]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 16 else
  if p.val = (false, vertices_285) then 18 else
  if p.val = (false, vertices_541) then 19 else
  if p.val = (false, vertices_837) then 20 else
  if p.val = (false, vertices_625) then 23 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_140) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_328) then 13 else
  if p.val = (true, vertices_672) then 14 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
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
  frame := ![0, 2, 5, 6]
  vertex := 7
  face := Sum.inl ⟨vertices_458, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_138, (by decide +kernel)⟩ ⟨vertices_458, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 2, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_654, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_138, (by decide +kernel)⟩ ⟨vertices_654, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
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
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_196, (by decide +kernel)⟩ ⟨vertices_740, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![3, 7, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_654, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_138, (by decide +kernel)⟩ ⟨vertices_654, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_570, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 2, 3, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_26, (by decide +kernel)⟩ ⟨vertices_570, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_282, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 2, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_26, (by decide +kernel)⟩ ⟨vertices_282, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_458, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![0, 2, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_138, (by decide +kernel)⟩ ⟨vertices_458, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_418, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![0, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_162, (by decide +kernel)⟩ ⟨vertices_418, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_674, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![0, 4, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_162, (by decide +kernel)⟩ ⟨vertices_674, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_204, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![1, 2, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_76, (by decide +kernel)⟩ ⟨vertices_204, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_332, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![1, 2, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_76, (by decide +kernel)⟩ ⟨vertices_332, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet8 : boundary.facets := ⟨vertices_740, by decide +kernel⟩
noncomputable def cover8 : FacetCoverage heightProof coverFacet8 :=
  .oneRow ![1, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_196, (by decide +kernel)⟩ ⟨vertices_740, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coveringFacets : Fin 9 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6, coverFacet7, coverFacet8]
noncomputable def coveringProof (j : Fin 9) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (Fin.cases cover7 (Fin.cases cover8 (fun i => Fin.elim0 i)))))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 9, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0282

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m15e10q1_0283.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0283

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_279 : Finset (Fin 10) := literalFinset [0, 1, 2, 4, 8] (by decide +kernel)
noncomputable def vertices_535 : Finset (Fin 10) := literalFinset [0, 1, 2, 4, 9] (by decide +kernel)
noncomputable def vertices_651 : Finset (Fin 10) := literalFinset [0, 1, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_419 : Finset (Fin 10) := literalFinset [0, 1, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_357 : Finset (Fin 10) := literalFinset [0, 2, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_677 : Finset (Fin 10) := literalFinset [0, 2, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_602 : Finset (Fin 10) := literalFinset [1, 3, 4, 6, 9] (by decide +kernel)
noncomputable def vertices_154 : Finset (Fin 10) := literalFinset [1, 3, 4, 7] (by decide +kernel)
noncomputable def vertices_402 : Finset (Fin 10) := literalFinset [1, 4, 7, 8] (by decide +kernel)
noncomputable def vertices_620 : Finset (Fin 10) := literalFinset [2, 3, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_852 : Finset (Fin 10) := literalFinset [2, 4, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_216 : Finset (Fin 10) := literalFinset [3, 4, 6, 7] (by decide +kernel)
noncomputable def vertices_232 : Finset (Fin 10) := literalFinset [3, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_680 : Finset (Fin 10) := literalFinset [3, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_496 : Finset (Fin 10) := literalFinset [4, 5, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_23 : Finset (Fin 10) := literalFinset [0, 1, 2, 4] (by decide +kernel)
noncomputable def vertices_131 : Finset (Fin 10) := literalFinset [0, 1, 7] (by decide +kernel)
noncomputable def vertices_259 : Finset (Fin 10) := literalFinset [0, 1, 8] (by decide +kernel)
noncomputable def vertices_515 : Finset (Fin 10) := literalFinset [0, 1, 9] (by decide +kernel)
noncomputable def vertices_37 : Finset (Fin 10) := literalFinset [0, 2, 5] (by decide +kernel)
noncomputable def vertices_261 : Finset (Fin 10) := literalFinset [0, 2, 8] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_161 : Finset (Fin 10) := literalFinset [0, 5, 7] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_26 : Finset (Fin 10) := literalFinset [1, 3, 4] (by decide +kernel)
noncomputable def vertices_138 : Finset (Fin 10) := literalFinset [1, 3, 7] (by decide +kernel)
noncomputable def vertices_522 : Finset (Fin 10) := literalFinset [1, 3, 9] (by decide +kernel)
noncomputable def vertices_146 : Finset (Fin 10) := literalFinset [1, 4, 7] (by decide +kernel)
noncomputable def vertices_274 : Finset (Fin 10) := literalFinset [1, 4, 8] (by decide +kernel)
noncomputable def vertices_530 : Finset (Fin 10) := literalFinset [1, 4, 9] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_532 : Finset (Fin 10) := literalFinset [2, 4, 9] (by decide +kernel)
noncomputable def vertices_100 : Finset (Fin 10) := literalFinset [2, 5, 6] (by decide +kernel)
noncomputable def vertices_548 : Finset (Fin 10) := literalFinset [2, 5, 9] (by decide +kernel)
noncomputable def vertices_324 : Finset (Fin 10) := literalFinset [2, 6, 8] (by decide +kernel)
noncomputable def vertices_580 : Finset (Fin 10) := literalFinset [2, 6, 9] (by decide +kernel)
noncomputable def vertices_88 : Finset (Fin 10) := literalFinset [3, 4, 6] (by decide +kernel)
noncomputable def vertices_152 : Finset (Fin 10) := literalFinset [3, 4, 7] (by decide +kernel)
noncomputable def vertices_104 : Finset (Fin 10) := literalFinset [3, 5, 6] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_552 : Finset (Fin 10) := literalFinset [3, 5, 9] (by decide +kernel)
noncomputable def vertices_200 : Finset (Fin 10) := literalFinset [3, 6, 7] (by decide +kernel)
noncomputable def vertices_584 : Finset (Fin 10) := literalFinset [3, 6, 9] (by decide +kernel)
noncomputable def vertices_648 : Finset (Fin 10) := literalFinset [3, 7, 9] (by decide +kernel)
noncomputable def vertices_208 : Finset (Fin 10) := literalFinset [4, 6, 7] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_224 : Finset (Fin 10) := literalFinset [5, 6, 7] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_535, vertices_651, vertices_419, vertices_357, vertices_677, vertices_602, vertices_154, vertices_402, vertices_620, vertices_852, vertices_216, vertices_232, vertices_680, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_131, vertices_259, vertices_515, vertices_37, vertices_261, vertices_517, vertices_161, vertices_289, vertices_641, vertices_26, vertices_138, vertices_522, vertices_146, vertices_274, vertices_530, vertices_386, vertices_276, vertices_532, vertices_100, vertices_548, vertices_324, vertices_580, vertices_88, vertices_152, vertices_104, vertices_168, vertices_552, vertices_200, vertices_584, vertices_648, vertices_208, vertices_336, vertices_592, vertices_400, vertices_224, vertices_352, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_535), (false, vertices_651), (false, vertices_419), (false, vertices_357), (false, vertices_677), (true, vertices_26), (true, vertices_146), (true, vertices_580), (true, vertices_88), (true, vertices_152), (true, vertices_104), (true, vertices_168), (true, vertices_552), (true, vertices_200), (true, vertices_584), (true, vertices_208), (true, vertices_336), (true, vertices_592), (true, vertices_400), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![17, 21, 15, 24, 25, 26, 27, 28, 29]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 18 else
  if p.val = (false, vertices_535) then 19 else
  if p.val = (false, vertices_651) then 16 else
  if p.val = (false, vertices_419) then 20 else
  if p.val = (false, vertices_357) then 22 else
  if p.val = (false, vertices_677) then 23 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_580) then 2 else
  if p.val = (true, vertices_88) then 3 else
  if p.val = (true, vertices_152) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_224) then 14 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_279), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 5]
  vertex := 8
  face := Sum.inl ⟨vertices_602, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_26, (by decide +kernel)⟩ ⟨vertices_602, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
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
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_100, (by decide +kernel)⟩ ⟨vertices_620, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
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

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![3, 4, 5, 6]
  vertex := 7
  face := Sum.inl ⟨vertices_496, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_208, (by decide +kernel)⟩ ⟨vertices_496, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 2, 1, 3]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_602, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_26, (by decide +kernel)⟩ ⟨vertices_602, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_154, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 2, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_26, (by decide +kernel)⟩ ⟨vertices_154, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_402, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 3, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_146, (by decide +kernel)⟩ ⟨vertices_402, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_620, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 2, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_100, (by decide +kernel)⟩ ⟨vertices_620, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_852, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![1, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_276, (by decide +kernel)⟩ ⟨vertices_852, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_216, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![2, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_88, (by decide +kernel)⟩ ⟨vertices_216, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_232, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![2, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_104, (by decide +kernel)⟩ ⟨vertices_232, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_680, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![2, 4, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_168, (by decide +kernel)⟩ ⟨vertices_680, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet8 : boundary.facets := ⟨vertices_496, by decide +kernel⟩
noncomputable def cover8 : FacetCoverage heightProof coverFacet8 :=
  .oneRow ![3, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_208, (by decide +kernel)⟩ ⟨vertices_496, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coveringFacets : Fin 9 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6, coverFacet7, coverFacet8]
noncomputable def coveringProof (j : Fin 9) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (Fin.cases cover7 (Fin.cases cover8 (fun i => Fin.elim0 i)))))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 9, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0283

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m15e10q1_0284.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0284

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_675 : Finset (Fin 10) := literalFinset [0, 1, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_589 : Finset (Fin 10) := literalFinset [0, 2, 3, 6, 9] (by decide +kernel)
noncomputable def vertices_809 : Finset (Fin 10) := literalFinset [0, 3, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_457 : Finset (Fin 10) := literalFinset [0, 3, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_433 : Finset (Fin 10) := literalFinset [0, 4, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_705 : Finset (Fin 10) := literalFinset [0, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_782 : Finset (Fin 10) := literalFinset [1, 2, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_310 : Finset (Fin 10) := literalFinset [1, 2, 4, 5, 8] (by decide +kernel)
noncomputable def vertices_534 : Finset (Fin 10) := literalFinset [1, 2, 4, 9] (by decide +kernel)
noncomputable def vertices_178 : Finset (Fin 10) := literalFinset [1, 4, 5, 7] (by decide +kernel)
noncomputable def vertices_722 : Finset (Fin 10) := literalFinset [1, 4, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_802 : Finset (Fin 10) := literalFinset [1, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_220 : Finset (Fin 10) := literalFinset [2, 3, 4, 6, 7] (by decide +kernel)
noncomputable def vertices_412 : Finset (Fin 10) := literalFinset [2, 3, 4, 7, 8] (by decide +kernel)
noncomputable def vertices_596 : Finset (Fin 10) := literalFinset [2, 4, 6, 9] (by decide +kernel)
noncomputable def vertices_73 : Finset (Fin 10) := literalFinset [0, 3, 6] (by decide +kernel)
noncomputable def vertices_265 : Finset (Fin 10) := literalFinset [0, 3, 8] (by decide +kernel)
noncomputable def vertices_521 : Finset (Fin 10) := literalFinset [0, 3, 9] (by decide +kernel)
noncomputable def vertices_161 : Finset (Fin 10) := literalFinset [0, 5, 7] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_545 : Finset (Fin 10) := literalFinset [0, 5, 9] (by decide +kernel)
noncomputable def vertices_193 : Finset (Fin 10) := literalFinset [0, 6, 7] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_385 : Finset (Fin 10) := literalFinset [0, 7, 8] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_22 : Finset (Fin 10) := literalFinset [1, 2, 4] (by decide +kernel)
noncomputable def vertices_262 : Finset (Fin 10) := literalFinset [1, 2, 8] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_50 : Finset (Fin 10) := literalFinset [1, 4, 5] (by decide +kernel)
noncomputable def vertices_146 : Finset (Fin 10) := literalFinset [1, 4, 7] (by decide +kernel)
noncomputable def vertices_530 : Finset (Fin 10) := literalFinset [1, 4, 9] (by decide +kernel)
noncomputable def vertices_162 : Finset (Fin 10) := literalFinset [1, 5, 7] (by decide +kernel)
noncomputable def vertices_290 : Finset (Fin 10) := literalFinset [1, 5, 8] (by decide +kernel)
noncomputable def vertices_546 : Finset (Fin 10) := literalFinset [1, 5, 9] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_156 : Finset (Fin 10) := literalFinset [2, 3, 4, 7] (by decide +kernel)
noncomputable def vertices_76 : Finset (Fin 10) := literalFinset [2, 3, 6] (by decide +kernel)
noncomputable def vertices_268 : Finset (Fin 10) := literalFinset [2, 3, 8] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_532 : Finset (Fin 10) := literalFinset [2, 4, 9] (by decide +kernel)
noncomputable def vertices_580 : Finset (Fin 10) := literalFinset [2, 6, 9] (by decide +kernel)
noncomputable def vertices_200 : Finset (Fin 10) := literalFinset [3, 6, 7] (by decide +kernel)
noncomputable def vertices_392 : Finset (Fin 10) := literalFinset [3, 7, 8] (by decide +kernel)
noncomputable def vertices_776 : Finset (Fin 10) := literalFinset [3, 8, 9] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_208 : Finset (Fin 10) := literalFinset [4, 6, 7] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_589, vertices_809, vertices_457, vertices_433, vertices_705, vertices_782, vertices_310, vertices_534, vertices_178, vertices_722, vertices_802, vertices_220, vertices_412, vertices_596] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_265, vertices_521, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_641, vertices_22, vertices_262, vertices_518, vertices_50, vertices_146, vertices_530, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_156, vertices_76, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_580, vertices_200, vertices_392, vertices_776, vertices_176, vertices_304, vertices_208, vertices_592, vertices_400, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_589), (false, vertices_809), (false, vertices_457), (false, vertices_433), (false, vertices_705), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_50), (true, vertices_146), (true, vertices_530), (true, vertices_290), (true, vertices_770), (true, vertices_156), (true, vertices_268), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_208), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![15, 17, 20, 23, 25, 26, 27, 28, 29]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_589) then 18 else
  if p.val = (false, vertices_809) then 21 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (false, vertices_705) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_156) then 19 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_84) then 10 else
  if p.val = (true, vertices_276) then 11 else
  if p.val = (true, vertices_532) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_592) then 14 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_705), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_156), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 3, 4]
  vertex := 7
  face := Sum.inl ⟨vertices_310, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_310, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
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
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_262, (by decide +kernel)⟩ ⟨vertices_782, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 3
  frame := ![1, 2, 3]
  vertex := 6
  face := Sum.inr ⟨vertices_156, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_156, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 3, 5, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_722, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_146, (by decide +kernel)⟩ ⟨vertices_722, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![4, 7, 1, 0]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_782, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_262, (by decide +kernel)⟩ ⟨vertices_782, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_310, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 3, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_310, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_534, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 1, 3, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_534, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_178, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_50, (by decide +kernel)⟩ ⟨vertices_178, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_722, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![0, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_146, (by decide +kernel)⟩ ⟨vertices_722, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_802, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![0, 4, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_290, (by decide +kernel)⟩ ⟨vertices_802, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_220, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![1, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_156, (by decide +kernel)⟩ ⟨vertices_220, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_412, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .oneRow ![1, 2, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_156, (by decide +kernel)⟩ ⟨vertices_412, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet8 : boundary.facets := ⟨vertices_596, by decide +kernel⟩
noncomputable def cover8 : FacetCoverage heightProof coverFacet8 :=
  .fundamental ![1, 3, 5, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_596, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coveringFacets : Fin 9 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6, coverFacet7, coverFacet8]
noncomputable def coveringProof (j : Fin 9) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (Fin.cases cover7 (Fin.cases cover8 (fun i => Fin.elim0 i)))))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 9, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0284

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m15e10q1_0285.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0285

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_611 : Finset (Fin 10) := literalFinset [0, 1, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_397 : Finset (Fin 10) := literalFinset [0, 2, 3, 7, 8] (by decide +kernel)
noncomputable def vertices_805 : Finset (Fin 10) := literalFinset [0, 2, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_709 : Finset (Fin 10) := literalFinset [0, 2, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_369 : Finset (Fin 10) := literalFinset [0, 4, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_449 : Finset (Fin 10) := literalFinset [0, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_206 : Finset (Fin 10) := literalFinset [1, 2, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_590 : Finset (Fin 10) := literalFinset [1, 2, 3, 6, 9] (by decide +kernel)
noncomputable def vertices_570 : Finset (Fin 10) := literalFinset [1, 3, 4, 5, 9] (by decide +kernel)
noncomputable def vertices_410 : Finset (Fin 10) := literalFinset [1, 3, 4, 7, 8] (by decide +kernel)
noncomputable def vertices_114 : Finset (Fin 10) := literalFinset [1, 4, 5, 6] (by decide +kernel)
noncomputable def vertices_210 : Finset (Fin 10) := literalFinset [1, 4, 6, 7] (by decide +kernel)
noncomputable def vertices_796 : Finset (Fin 10) := literalFinset [2, 3, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_816 : Finset (Fin 10) := literalFinset [4, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_464 : Finset (Fin 10) := literalFinset [4, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_133 : Finset (Fin 10) := literalFinset [0, 2, 7] (by decide +kernel)
noncomputable def vertices_261 : Finset (Fin 10) := literalFinset [0, 2, 8] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_97 : Finset (Fin 10) := literalFinset [0, 5, 6] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_545 : Finset (Fin 10) := literalFinset [0, 5, 9] (by decide +kernel)
noncomputable def vertices_193 : Finset (Fin 10) := literalFinset [0, 6, 7] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_385 : Finset (Fin 10) := literalFinset [0, 7, 8] (by decide +kernel)
noncomputable def vertices_78 : Finset (Fin 10) := literalFinset [1, 2, 3, 6] (by decide +kernel)
noncomputable def vertices_26 : Finset (Fin 10) := literalFinset [1, 3, 4] (by decide +kernel)
noncomputable def vertices_138 : Finset (Fin 10) := literalFinset [1, 3, 7] (by decide +kernel)
noncomputable def vertices_522 : Finset (Fin 10) := literalFinset [1, 3, 9] (by decide +kernel)
noncomputable def vertices_50 : Finset (Fin 10) := literalFinset [1, 4, 5] (by decide +kernel)
noncomputable def vertices_82 : Finset (Fin 10) := literalFinset [1, 4, 6] (by decide +kernel)
noncomputable def vertices_146 : Finset (Fin 10) := literalFinset [1, 4, 7] (by decide +kernel)
noncomputable def vertices_98 : Finset (Fin 10) := literalFinset [1, 5, 6] (by decide +kernel)
noncomputable def vertices_546 : Finset (Fin 10) := literalFinset [1, 5, 9] (by decide +kernel)
noncomputable def vertices_194 : Finset (Fin 10) := literalFinset [1, 6, 7] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_140 : Finset (Fin 10) := literalFinset [2, 3, 7] (by decide +kernel)
noncomputable def vertices_268 : Finset (Fin 10) := literalFinset [2, 3, 8] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_196 : Finset (Fin 10) := literalFinset [2, 6, 7] (by decide +kernel)
noncomputable def vertices_580 : Finset (Fin 10) := literalFinset [2, 6, 9] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_280 : Finset (Fin 10) := literalFinset [3, 4, 8] (by decide +kernel)
noncomputable def vertices_536 : Finset (Fin 10) := literalFinset [3, 4, 9] (by decide +kernel)
noncomputable def vertices_392 : Finset (Fin 10) := literalFinset [3, 7, 8] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_208 : Finset (Fin 10) := literalFinset [4, 6, 7] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_784 : Finset (Fin 10) := literalFinset [4, 8, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_397, vertices_805, vertices_709, vertices_369, vertices_449, vertices_206, vertices_590, vertices_570, vertices_410, vertices_114, vertices_210, vertices_796, vertices_816, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_97, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_78, vertices_26, vertices_138, vertices_522, vertices_50, vertices_82, vertices_146, vertices_98, vertices_546, vertices_194, vertices_578, vertices_140, vertices_268, vertices_524, vertices_196, vertices_580, vertices_772, vertices_280, vertices_536, vertices_392, vertices_112, vertices_304, vertices_560, vertices_208, vertices_336, vertices_400, vertices_784, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_397), (false, vertices_805), (false, vertices_709), (false, vertices_369), (false, vertices_449), (true, vertices_78), (true, vertices_26), (true, vertices_138), (true, vertices_522), (true, vertices_50), (true, vertices_82), (true, vertices_146), (true, vertices_194), (true, vertices_524), (true, vertices_280), (true, vertices_536), (true, vertices_560), (true, vertices_208), (true, vertices_400), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![15, 18, 22, 23, 25, 26, 27, 28, 29]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 16 else
  if p.val = (false, vertices_397) then 19 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_784) then 14 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_78), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 3
  frame := ![0, 1, 2]
  vertex := 5
  face := Sum.inr ⟨vertices_78, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_78, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
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

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 6]
  vertex := 7
  face := Sum.inl ⟨vertices_410, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_26, (by decide +kernel)⟩ ⟨vertices_410, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 3, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_796, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_268, (by decide +kernel)⟩ ⟨vertices_796, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![5, 4, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_206, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_78, (by decide +kernel)⟩ ⟨vertices_206, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_590, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 2, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_78, (by decide +kernel)⟩ ⟨vertices_590, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_570, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 2, 3, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_26, (by decide +kernel)⟩ ⟨vertices_570, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_410, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![0, 2, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_26, (by decide +kernel)⟩ ⟨vertices_410, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_114, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![0, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_50, (by decide +kernel)⟩ ⟨vertices_114, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_210, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![0, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_82, (by decide +kernel)⟩ ⟨vertices_210, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_796, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![1, 2, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_268, (by decide +kernel)⟩ ⟨vertices_796, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_816, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![3, 4, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_304, (by decide +kernel)⟩ ⟨vertices_816, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet8 : boundary.facets := ⟨vertices_464, by decide +kernel⟩
noncomputable def cover8 : FacetCoverage heightProof coverFacet8 :=
  .fundamental ![3, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_208, (by decide +kernel)⟩ ⟨vertices_464, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coveringFacets : Fin 9 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6, coverFacet7, coverFacet8]
noncomputable def coveringProof (j : Fin 9) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (Fin.cases cover7 (Fin.cases cover8 (fun i => Fin.elim0 i)))))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 9, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0285

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m15e10q1_0286.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0286

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_339 : Finset (Fin 10) := literalFinset [0, 1, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_285 : Finset (Fin 10) := literalFinset [0, 2, 3, 4, 8] (by decide +kernel)
noncomputable def vertices_541 : Finset (Fin 10) := literalFinset [0, 2, 3, 4, 9] (by decide +kernel)
noncomputable def vertices_361 : Finset (Fin 10) := literalFinset [0, 3, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_681 : Finset (Fin 10) := literalFinset [0, 3, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_625 : Finset (Fin 10) := literalFinset [0, 4, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_214 : Finset (Fin 10) := literalFinset [1, 2, 4, 6, 7] (by decide +kernel)
noncomputable def vertices_426 : Finset (Fin 10) := literalFinset [1, 3, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_402 : Finset (Fin 10) := literalFinset [1, 4, 7, 8] (by decide +kernel)
noncomputable def vertices_226 : Finset (Fin 10) := literalFinset [1, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_354 : Finset (Fin 10) := literalFinset [1, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_908 : Finset (Fin 10) := literalFinset [2, 3, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_596 : Finset (Fin 10) := literalFinset [2, 4, 6, 9] (by decide +kernel)
noncomputable def vertices_404 : Finset (Fin 10) := literalFinset [2, 4, 7, 8] (by decide +kernel)
noncomputable def vertices_740 : Finset (Fin 10) := literalFinset [2, 5, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_29 : Finset (Fin 10) := literalFinset [0, 2, 3, 4] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_265 : Finset (Fin 10) := literalFinset [0, 3, 8] (by decide +kernel)
noncomputable def vertices_521 : Finset (Fin 10) := literalFinset [0, 3, 9] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_273 : Finset (Fin 10) := literalFinset [0, 4, 8] (by decide +kernel)
noncomputable def vertices_529 : Finset (Fin 10) := literalFinset [0, 4, 9] (by decide +kernel)
noncomputable def vertices_97 : Finset (Fin 10) := literalFinset [0, 5, 6] (by decide +kernel)
noncomputable def vertices_545 : Finset (Fin 10) := literalFinset [0, 5, 9] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_82 : Finset (Fin 10) := literalFinset [1, 4, 6] (by decide +kernel)
noncomputable def vertices_146 : Finset (Fin 10) := literalFinset [1, 4, 7] (by decide +kernel)
noncomputable def vertices_274 : Finset (Fin 10) := literalFinset [1, 4, 8] (by decide +kernel)
noncomputable def vertices_98 : Finset (Fin 10) := literalFinset [1, 5, 6] (by decide +kernel)
noncomputable def vertices_162 : Finset (Fin 10) := literalFinset [1, 5, 7] (by decide +kernel)
noncomputable def vertices_290 : Finset (Fin 10) := literalFinset [1, 5, 8] (by decide +kernel)
noncomputable def vertices_194 : Finset (Fin 10) := literalFinset [1, 6, 7] (by decide +kernel)
noncomputable def vertices_322 : Finset (Fin 10) := literalFinset [1, 6, 8] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_268 : Finset (Fin 10) := literalFinset [2, 3, 8] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_148 : Finset (Fin 10) := literalFinset [2, 4, 7] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_532 : Finset (Fin 10) := literalFinset [2, 4, 9] (by decide +kernel)
noncomputable def vertices_196 : Finset (Fin 10) := literalFinset [2, 6, 7] (by decide +kernel)
noncomputable def vertices_580 : Finset (Fin 10) := literalFinset [2, 6, 9] (by decide +kernel)
noncomputable def vertices_388 : Finset (Fin 10) := literalFinset [2, 7, 8] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_392 : Finset (Fin 10) := literalFinset [3, 7, 8] (by decide +kernel)
noncomputable def vertices_648 : Finset (Fin 10) := literalFinset [3, 7, 9] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_224 : Finset (Fin 10) := literalFinset [5, 6, 7] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_608 : Finset (Fin 10) := literalFinset [5, 6, 9] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_285, vertices_541, vertices_361, vertices_681, vertices_625, vertices_214, vertices_426, vertices_402, vertices_226, vertices_354, vertices_908, vertices_596, vertices_404, vertices_740] (by decide +kernel)
  polygons := literalFinset [vertices_29, vertices_41, vertices_265, vertices_521, vertices_81, vertices_273, vertices_529, vertices_97, vertices_545, vertices_321, vertices_82, vertices_146, vertices_274, vertices_98, vertices_162, vertices_290, vertices_194, vertices_322, vertices_386, vertices_268, vertices_524, vertices_84, vertices_148, vertices_276, vertices_532, vertices_196, vertices_580, vertices_388, vertices_644, vertices_168, vertices_296, vertices_392, vertices_648, vertices_592, vertices_400, vertices_224, vertices_352, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_285), (false, vertices_541), (false, vertices_361), (false, vertices_681), (false, vertices_625), (true, vertices_146), (true, vertices_98), (true, vertices_162), (true, vertices_290), (true, vertices_194), (true, vertices_386), (true, vertices_84), (true, vertices_148), (true, vertices_196), (true, vertices_580), (true, vertices_388), (true, vertices_644), (true, vertices_392), (true, vertices_400), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![15, 17, 20, 23, 25, 26, 27, 28, 29]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 16 else
  if p.val = (false, vertices_285) then 18 else
  if p.val = (false, vertices_541) then 19 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_681) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (true, vertices_146) then 0 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_224) then 14 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 3, 5]
  vertex := 6
  face := Sum.inl ⟨vertices_214, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_82, (by decide +kernel)⟩ ⟨vertices_214, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 4, 6]
  vertex := 7
  face := Sum.inl ⟨vertices_426, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_162, (by decide +kernel)⟩ ⟨vertices_426, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
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
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_268, (by decide +kernel)⟩ ⟨vertices_908, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
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
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_196, (by decide +kernel)⟩ ⟨vertices_740, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![3, 0, 2, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_214, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_82, (by decide +kernel)⟩ ⟨vertices_214, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_426, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 2, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_162, (by decide +kernel)⟩ ⟨vertices_426, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_402, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 3, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_146, (by decide +kernel)⟩ ⟨vertices_402, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_226, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_98, (by decide +kernel)⟩ ⟨vertices_226, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_354, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![0, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_98, (by decide +kernel)⟩ ⟨vertices_354, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_908, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![1, 2, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_268, (by decide +kernel)⟩ ⟨vertices_908, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_596, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![1, 3, 5, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_596, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_404, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![1, 3, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_148, (by decide +kernel)⟩ ⟨vertices_404, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet8 : boundary.facets := ⟨vertices_740, by decide +kernel⟩
noncomputable def cover8 : FacetCoverage heightProof coverFacet8 :=
  .oneRow ![1, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_196, (by decide +kernel)⟩ ⟨vertices_740, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coveringFacets : Fin 9 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6, coverFacet7, coverFacet8]
noncomputable def coveringProof (j : Fin 9) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (Fin.cases cover7 (Fin.cases cover8 (fun i => Fin.elim0 i)))))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 9, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0286

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m15e10q1_0287.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0287

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_295 : Finset (Fin 10) := literalFinset [0, 1, 2, 5, 8] (by decide +kernel)
noncomputable def vertices_551 : Finset (Fin 10) := literalFinset [0, 1, 2, 5, 9] (by decide +kernel)
noncomputable def vertices_653 : Finset (Fin 10) := literalFinset [0, 2, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_453 : Finset (Fin 10) := literalFinset [0, 2, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_721 : Finset (Fin 10) := literalFinset [0, 4, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_865 : Finset (Fin 10) := literalFinset [0, 5, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_542 : Finset (Fin 10) := literalFinset [1, 2, 3, 4, 9] (by decide +kernel)
noncomputable def vertices_398 : Finset (Fin 10) := literalFinset [1, 2, 3, 7, 8] (by decide +kernel)
noncomputable def vertices_282 : Finset (Fin 10) := literalFinset [1, 3, 4, 8] (by decide +kernel)
noncomputable def vertices_626 : Finset (Fin 10) := literalFinset [1, 4, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_306 : Finset (Fin 10) := literalFinset [1, 4, 5, 8] (by decide +kernel)
noncomputable def vertices_376 : Finset (Fin 10) := literalFinset [3, 4, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_216 : Finset (Fin 10) := literalFinset [3, 4, 6, 7] (by decide +kernel)
noncomputable def vertices_664 : Finset (Fin 10) := literalFinset [3, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_456 : Finset (Fin 10) := literalFinset [3, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_39 : Finset (Fin 10) := literalFinset [0, 1, 2, 5] (by decide +kernel)
noncomputable def vertices_133 : Finset (Fin 10) := literalFinset [0, 2, 7] (by decide +kernel)
noncomputable def vertices_261 : Finset (Fin 10) := literalFinset [0, 2, 8] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_545 : Finset (Fin 10) := literalFinset [0, 5, 9] (by decide +kernel)
noncomputable def vertices_193 : Finset (Fin 10) := literalFinset [0, 6, 7] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_262 : Finset (Fin 10) := literalFinset [1, 2, 8] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_26 : Finset (Fin 10) := literalFinset [1, 3, 4] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_50 : Finset (Fin 10) := literalFinset [1, 4, 5] (by decide +kernel)
noncomputable def vertices_274 : Finset (Fin 10) := literalFinset [1, 4, 8] (by decide +kernel)
noncomputable def vertices_530 : Finset (Fin 10) := literalFinset [1, 4, 9] (by decide +kernel)
noncomputable def vertices_290 : Finset (Fin 10) := literalFinset [1, 5, 8] (by decide +kernel)
noncomputable def vertices_546 : Finset (Fin 10) := literalFinset [1, 5, 9] (by decide +kernel)
noncomputable def vertices_140 : Finset (Fin 10) := literalFinset [2, 3, 7] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_388 : Finset (Fin 10) := literalFinset [2, 7, 8] (by decide +kernel)
noncomputable def vertices_88 : Finset (Fin 10) := literalFinset [3, 4, 6] (by decide +kernel)
noncomputable def vertices_152 : Finset (Fin 10) := literalFinset [3, 4, 7] (by decide +kernel)
noncomputable def vertices_280 : Finset (Fin 10) := literalFinset [3, 4, 8] (by decide +kernel)
noncomputable def vertices_536 : Finset (Fin 10) := literalFinset [3, 4, 9] (by decide +kernel)
noncomputable def vertices_200 : Finset (Fin 10) := literalFinset [3, 6, 7] (by decide +kernel)
noncomputable def vertices_328 : Finset (Fin 10) := literalFinset [3, 6, 8] (by decide +kernel)
noncomputable def vertices_392 : Finset (Fin 10) := literalFinset [3, 7, 8] (by decide +kernel)
noncomputable def vertices_648 : Finset (Fin 10) := literalFinset [3, 7, 9] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_208 : Finset (Fin 10) := literalFinset [4, 6, 7] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_608 : Finset (Fin 10) := literalFinset [5, 6, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_551, vertices_653, vertices_453, vertices_721, vertices_865, vertices_542, vertices_398, vertices_282, vertices_626, vertices_306, vertices_376, vertices_216, vertices_664, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_39, vertices_133, vertices_261, vertices_517, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_641, vertices_14, vertices_262, vertices_518, vertices_26, vertices_266, vertices_50, vertices_274, vertices_530, vertices_290, vertices_546, vertices_140, vertices_524, vertices_388, vertices_88, vertices_152, vertices_280, vertices_536, vertices_200, vertices_328, vertices_392, vertices_648, vertices_112, vertices_304, vertices_208, vertices_592, vertices_656, vertices_352, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_551), (false, vertices_653), (false, vertices_453), (false, vertices_721), (false, vertices_865), (true, vertices_14), (true, vertices_26), (true, vertices_266), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_200), (true, vertices_328), (true, vertices_392), (true, vertices_112), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![15, 18, 21, 22, 24, 26, 27, 28, 29]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 16 else
  if p.val = (false, vertices_551) then 17 else
  if p.val = (false, vertices_653) then 19 else
  if p.val = (false, vertices_453) then 20 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_304) then 14 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 2, 6]
  vertex := 7
  face := Sum.inl ⟨vertices_398, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_398, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 2, 3]
  vertex := 8
  face := Sum.inl ⟨vertices_542, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_542, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 3, 4, 5]
  vertex := 8
  face := Sum.inl ⟨vertices_626, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_50, (by decide +kernel)⟩ ⟨vertices_626, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
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
noncomputable def pivot : Fin 4 → Fin 9 := ![6, 1, 0, 2]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_542, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 3] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_542, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_398, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 2, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_398, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_282, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 2, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_26, (by decide +kernel)⟩ ⟨vertices_282, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_626, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![0, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_50, (by decide +kernel)⟩ ⟨vertices_626, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_306, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![0, 3, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_50, (by decide +kernel)⟩ ⟨vertices_306, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_376, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![2, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_88, (by decide +kernel)⟩ ⟨vertices_376, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_216, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![2, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_88, (by decide +kernel)⟩ ⟨vertices_216, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_664, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![2, 3, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_152, (by decide +kernel)⟩ ⟨vertices_664, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet8 : boundary.facets := ⟨vertices_456, by decide +kernel⟩
noncomputable def cover8 : FacetCoverage heightProof coverFacet8 :=
  .fundamental ![2, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_200, (by decide +kernel)⟩ ⟨vertices_456, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coveringFacets : Fin 9 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6, coverFacet7, coverFacet8]
noncomputable def coveringProof (j : Fin 9) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (Fin.cases cover7 (Fin.cases cover8 (fun i => Fin.elim0 i)))))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 9, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0287

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m15e10q1_0288.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0288

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_587 : Finset (Fin 10) := literalFinset [0, 1, 3, 6, 9] (by decide +kernel)
noncomputable def vertices_301 : Finset (Fin 10) := literalFinset [0, 2, 3, 5, 8] (by decide +kernel)
noncomputable def vertices_781 : Finset (Fin 10) := literalFinset [0, 2, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_181 : Finset (Fin 10) := literalFinset [0, 2, 4, 5, 7] (by decide +kernel)
noncomputable def vertices_709 : Finset (Fin 10) := literalFinset [0, 2, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_233 : Finset (Fin 10) := literalFinset [0, 3, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_662 : Finset (Fin 10) := literalFinset [1, 2, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_794 : Finset (Fin 10) := literalFinset [1, 3, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_362 : Finset (Fin 10) := literalFinset [1, 3, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_210 : Finset (Fin 10) := literalFinset [1, 4, 6, 7] (by decide +kernel)
noncomputable def vertices_338 : Finset (Fin 10) := literalFinset [1, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_706 : Finset (Fin 10) := literalFinset [1, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_820 : Finset (Fin 10) := literalFinset [2, 4, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_240 : Finset (Fin 10) := literalFinset [4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_368 : Finset (Fin 10) := literalFinset [4, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_269 : Finset (Fin 10) := literalFinset [0, 2, 3, 8] (by decide +kernel)
noncomputable def vertices_37 : Finset (Fin 10) := literalFinset [0, 2, 5] (by decide +kernel)
noncomputable def vertices_133 : Finset (Fin 10) := literalFinset [0, 2, 7] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_73 : Finset (Fin 10) := literalFinset [0, 3, 6] (by decide +kernel)
noncomputable def vertices_521 : Finset (Fin 10) := literalFinset [0, 3, 9] (by decide +kernel)
noncomputable def vertices_161 : Finset (Fin 10) := literalFinset [0, 5, 7] (by decide +kernel)
noncomputable def vertices_193 : Finset (Fin 10) := literalFinset [0, 6, 7] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_74 : Finset (Fin 10) := literalFinset [1, 3, 6] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_522 : Finset (Fin 10) := literalFinset [1, 3, 9] (by decide +kernel)
noncomputable def vertices_82 : Finset (Fin 10) := literalFinset [1, 4, 6] (by decide +kernel)
noncomputable def vertices_146 : Finset (Fin 10) := literalFinset [1, 4, 7] (by decide +kernel)
noncomputable def vertices_274 : Finset (Fin 10) := literalFinset [1, 4, 8] (by decide +kernel)
noncomputable def vertices_530 : Finset (Fin 10) := literalFinset [1, 4, 9] (by decide +kernel)
noncomputable def vertices_194 : Finset (Fin 10) := literalFinset [1, 6, 7] (by decide +kernel)
noncomputable def vertices_322 : Finset (Fin 10) := literalFinset [1, 6, 8] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_148 : Finset (Fin 10) := literalFinset [2, 4, 7] (by decide +kernel)
noncomputable def vertices_532 : Finset (Fin 10) := literalFinset [2, 4, 9] (by decide +kernel)
noncomputable def vertices_292 : Finset (Fin 10) := literalFinset [2, 5, 8] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_104 : Finset (Fin 10) := literalFinset [3, 5, 6] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_776 : Finset (Fin 10) := literalFinset [3, 8, 9] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_208 : Finset (Fin 10) := literalFinset [4, 6, 7] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_784 : Finset (Fin 10) := literalFinset [4, 8, 9] (by decide +kernel)
noncomputable def vertices_224 : Finset (Fin 10) := literalFinset [5, 6, 7] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_301, vertices_781, vertices_181, vertices_709, vertices_233, vertices_662, vertices_794, vertices_362, vertices_210, vertices_338, vertices_706, vertices_820, vertices_240, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_269, vertices_37, vertices_133, vertices_517, vertices_41, vertices_73, vertices_521, vertices_161, vertices_193, vertices_577, vertices_74, vertices_266, vertices_522, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_642, vertices_52, vertices_148, vertices_532, vertices_292, vertices_644, vertices_772, vertices_104, vertices_296, vertices_776, vertices_112, vertices_176, vertices_304, vertices_208, vertices_336, vertices_784, vertices_224, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_301), (false, vertices_781), (false, vertices_181), (false, vertices_709), (false, vertices_233), (true, vertices_266), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_194), (true, vertices_322), (true, vertices_642), (true, vertices_532), (true, vertices_112), (true, vertices_304), (true, vertices_208), (true, vertices_336), (true, vertices_784), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![15, 21, 17, 24, 25, 26, 27, 28, 29]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 16 else
  if p.val = (false, vertices_301) then 18 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_181) then 22 else
  if p.val = (false, vertices_709) then 23 else
  if p.val = (false, vertices_233) then 20 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_784) then 13 else
  if p.val = (true, vertices_352) then 14 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
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
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_146, (by decide +kernel)⟩ ⟨vertices_662, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 4, 5]
  vertex := 7
  face := Sum.inl ⟨vertices_362, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_74, (by decide +kernel)⟩ ⟨vertices_362, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
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
noncomputable def pivot : Fin 4 → Fin 9 := ![6, 5, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_662, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_146, (by decide +kernel)⟩ ⟨vertices_662, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_794, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 2, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_266, (by decide +kernel)⟩ ⟨vertices_794, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_362, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 2, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_74, (by decide +kernel)⟩ ⟨vertices_362, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_210, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_82, (by decide +kernel)⟩ ⟨vertices_210, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_338, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![0, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_82, (by decide +kernel)⟩ ⟨vertices_338, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_706, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![0, 5, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_194, (by decide +kernel)⟩ ⟨vertices_706, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_820, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![1, 3, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_820, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_240, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![3, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_240, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet8 : boundary.facets := ⟨vertices_368, by decide +kernel⟩
noncomputable def cover8 : FacetCoverage heightProof coverFacet8 :=
  .fundamental ![3, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_368, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coveringFacets : Fin 9 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6, coverFacet7, coverFacet8]
noncomputable def coveringProof (j : Fin 9) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (Fin.cases cover7 (Fin.cases cover8 (fun i => Fin.elim0 i)))))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 9, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0288

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e10q1_0289.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0289

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_779 : Finset (Fin 10) := literalFinset [0, 1, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_419 : Finset (Fin 10) := literalFinset [0, 1, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_643 : Finset (Fin 10) := literalFinset [0, 1, 7, 9] (by decide +kernel)
noncomputable def vertices_589 : Finset (Fin 10) := literalFinset [0, 2, 3, 6, 9] (by decide +kernel)
noncomputable def vertices_457 : Finset (Fin 10) := literalFinset [0, 3, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_721 : Finset (Fin 10) := literalFinset [0, 4, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_310 : Finset (Fin 10) := literalFinset [1, 2, 4, 5, 8] (by decide +kernel)
noncomputable def vertices_242 : Finset (Fin 10) := literalFinset [1, 4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_658 : Finset (Fin 10) := literalFinset [1, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_786 : Finset (Fin 10) := literalFinset [1, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_796 : Finset (Fin 10) := literalFinset [2, 3, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_236 : Finset (Fin 10) := literalFinset [2, 3, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_428 : Finset (Fin 10) := literalFinset [2, 3, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_116 : Finset (Fin 10) := literalFinset [2, 4, 5, 6] (by decide +kernel)
noncomputable def vertices_596 : Finset (Fin 10) := literalFinset [2, 4, 6, 9] (by decide +kernel)
noncomputable def vertices_131 : Finset (Fin 10) := literalFinset [0, 1, 7] (by decide +kernel)
noncomputable def vertices_259 : Finset (Fin 10) := literalFinset [0, 1, 8] (by decide +kernel)
noncomputable def vertices_515 : Finset (Fin 10) := literalFinset [0, 1, 9] (by decide +kernel)
noncomputable def vertices_73 : Finset (Fin 10) := literalFinset [0, 3, 6] (by decide +kernel)
noncomputable def vertices_265 : Finset (Fin 10) := literalFinset [0, 3, 8] (by decide +kernel)
noncomputable def vertices_521 : Finset (Fin 10) := literalFinset [0, 3, 9] (by decide +kernel)
noncomputable def vertices_193 : Finset (Fin 10) := literalFinset [0, 6, 7] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_385 : Finset (Fin 10) := literalFinset [0, 7, 8] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_50 : Finset (Fin 10) := literalFinset [1, 4, 5] (by decide +kernel)
noncomputable def vertices_146 : Finset (Fin 10) := literalFinset [1, 4, 7] (by decide +kernel)
noncomputable def vertices_274 : Finset (Fin 10) := literalFinset [1, 4, 8] (by decide +kernel)
noncomputable def vertices_530 : Finset (Fin 10) := literalFinset [1, 4, 9] (by decide +kernel)
noncomputable def vertices_162 : Finset (Fin 10) := literalFinset [1, 5, 7] (by decide +kernel)
noncomputable def vertices_290 : Finset (Fin 10) := literalFinset [1, 5, 8] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_172 : Finset (Fin 10) := literalFinset [2, 3, 5, 7] (by decide +kernel)
noncomputable def vertices_76 : Finset (Fin 10) := literalFinset [2, 3, 6] (by decide +kernel)
noncomputable def vertices_268 : Finset (Fin 10) := literalFinset [2, 3, 8] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_532 : Finset (Fin 10) := literalFinset [2, 4, 9] (by decide +kernel)
noncomputable def vertices_100 : Finset (Fin 10) := literalFinset [2, 5, 6] (by decide +kernel)
noncomputable def vertices_292 : Finset (Fin 10) := literalFinset [2, 5, 8] (by decide +kernel)
noncomputable def vertices_580 : Finset (Fin 10) := literalFinset [2, 6, 9] (by decide +kernel)
noncomputable def vertices_200 : Finset (Fin 10) := literalFinset [3, 6, 7] (by decide +kernel)
noncomputable def vertices_392 : Finset (Fin 10) := literalFinset [3, 7, 8] (by decide +kernel)
noncomputable def vertices_776 : Finset (Fin 10) := literalFinset [3, 8, 9] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_208 : Finset (Fin 10) := literalFinset [4, 6, 7] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_784 : Finset (Fin 10) := literalFinset [4, 8, 9] (by decide +kernel)
noncomputable def vertices_224 : Finset (Fin 10) := literalFinset [5, 6, 7] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_419, vertices_643, vertices_589, vertices_457, vertices_721, vertices_310, vertices_242, vertices_658, vertices_786, vertices_796, vertices_236, vertices_428, vertices_116, vertices_596] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_73, vertices_265, vertices_521, vertices_193, vertices_577, vertices_385, vertices_641, vertices_50, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_642, vertices_770, vertices_172, vertices_76, vertices_268, vertices_524, vertices_52, vertices_84, vertices_276, vertices_532, vertices_100, vertices_292, vertices_580, vertices_200, vertices_392, vertices_776, vertices_112, vertices_208, vertices_592, vertices_656, vertices_784, vertices_224, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_419), (false, vertices_643), (false, vertices_589), (false, vertices_457), (false, vertices_721), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_172), (true, vertices_268), (true, vertices_52), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_100), (true, vertices_292), (true, vertices_112), (true, vertices_784), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![15, 18, 21, 23, 25, 26, 27, 28, 29]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_419) then 17 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_589) then 19 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (false, vertices_721) then 24 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_172) then 20 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_100) then 10 else
  if p.val = (true, vertices_292) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_784) then 13 else
  if p.val = (true, vertices_224) then 14 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_172), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 3, 4, 5]
  vertex := 6
  face := Sum.inl ⟨vertices_242, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_50, (by decide +kernel)⟩ ⟨vertices_242, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 3
  frame := ![1, 2, 4]
  vertex := 6
  face := Sum.inr ⟨vertices_172, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_172, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
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

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 3, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_796, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_268, (by decide +kernel)⟩ ⟨vertices_796, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![5, 6, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_310, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 3, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_50, (by decide +kernel)⟩ ⟨vertices_310, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_242, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_50, (by decide +kernel)⟩ ⟨vertices_242, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_658, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 3, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_146, (by decide +kernel)⟩ ⟨vertices_658, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_786, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 3, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_274, (by decide +kernel)⟩ ⟨vertices_786, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_796, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![1, 2, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_268, (by decide +kernel)⟩ ⟨vertices_796, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_236, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![1, 2, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_172, (by decide +kernel)⟩ ⟨vertices_236, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_428, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![1, 2, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_172, (by decide +kernel)⟩ ⟨vertices_428, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_116, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![1, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_116, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet8 : boundary.facets := ⟨vertices_596, by decide +kernel⟩
noncomputable def cover8 : FacetCoverage heightProof coverFacet8 :=
  .fundamental ![1, 3, 5, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_596, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coveringFacets : Fin 9 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6, coverFacet7, coverFacet8]
noncomputable def coveringProof (j : Fin 9) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (Fin.cases cover7 (Fin.cases cover8 (fun i => Fin.elim0 i)))))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 9, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0289

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e10q1_0290.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0290

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_659 : Finset (Fin 10) := literalFinset [0, 1, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_805 : Finset (Fin 10) := literalFinset [0, 2, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_217 : Finset (Fin 10) := literalFinset [0, 3, 4, 6, 7] (by decide +kernel)
noncomputable def vertices_625 : Finset (Fin 10) := literalFinset [0, 4, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_481 : Finset (Fin 10) := literalFinset [0, 5, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_897 : Finset (Fin 10) := literalFinset [0, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_94 : Finset (Fin 10) := literalFinset [1, 2, 3, 4, 6] (by decide +kernel)
noncomputable def vertices_302 : Finset (Fin 10) := literalFinset [1, 2, 3, 5, 8] (by decide +kernel)
noncomputable def vertices_598 : Finset (Fin 10) := literalFinset [1, 2, 4, 6, 9] (by decide +kernel)
noncomputable def vertices_902 : Finset (Fin 10) := literalFinset [1, 2, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_154 : Finset (Fin 10) := literalFinset [1, 3, 4, 7] (by decide +kernel)
noncomputable def vertices_394 : Finset (Fin 10) := literalFinset [1, 3, 7, 8] (by decide +kernel)
noncomputable def vertices_620 : Finset (Fin 10) := literalFinset [2, 3, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_232 : Finset (Fin 10) := literalFinset [3, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_424 : Finset (Fin 10) := literalFinset [3, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_145 : Finset (Fin 10) := literalFinset [0, 4, 7] (by decide +kernel)
noncomputable def vertices_529 : Finset (Fin 10) := literalFinset [0, 4, 9] (by decide +kernel)
noncomputable def vertices_97 : Finset (Fin 10) := literalFinset [0, 5, 6] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_545 : Finset (Fin 10) := literalFinset [0, 5, 9] (by decide +kernel)
noncomputable def vertices_193 : Finset (Fin 10) := literalFinset [0, 6, 7] (by decide +kernel)
noncomputable def vertices_385 : Finset (Fin 10) := literalFinset [0, 7, 8] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_86 : Finset (Fin 10) := literalFinset [1, 2, 4, 6] (by decide +kernel)
noncomputable def vertices_262 : Finset (Fin 10) := literalFinset [1, 2, 8] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_26 : Finset (Fin 10) := literalFinset [1, 3, 4] (by decide +kernel)
noncomputable def vertices_138 : Finset (Fin 10) := literalFinset [1, 3, 7] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_146 : Finset (Fin 10) := literalFinset [1, 4, 7] (by decide +kernel)
noncomputable def vertices_530 : Finset (Fin 10) := literalFinset [1, 4, 9] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_76 : Finset (Fin 10) := literalFinset [2, 3, 6] (by decide +kernel)
noncomputable def vertices_292 : Finset (Fin 10) := literalFinset [2, 5, 8] (by decide +kernel)
noncomputable def vertices_548 : Finset (Fin 10) := literalFinset [2, 5, 9] (by decide +kernel)
noncomputable def vertices_580 : Finset (Fin 10) := literalFinset [2, 6, 9] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_88 : Finset (Fin 10) := literalFinset [3, 4, 6] (by decide +kernel)
noncomputable def vertices_152 : Finset (Fin 10) := literalFinset [3, 4, 7] (by decide +kernel)
noncomputable def vertices_104 : Finset (Fin 10) := literalFinset [3, 5, 6] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_200 : Finset (Fin 10) := literalFinset [3, 6, 7] (by decide +kernel)
noncomputable def vertices_392 : Finset (Fin 10) := literalFinset [3, 7, 8] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_224 : Finset (Fin 10) := literalFinset [5, 6, 7] (by decide +kernel)
noncomputable def vertices_608 : Finset (Fin 10) := literalFinset [5, 6, 9] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_805, vertices_217, vertices_625, vertices_481, vertices_897, vertices_94, vertices_302, vertices_598, vertices_902, vertices_154, vertices_394, vertices_620, vertices_232, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_145, vertices_529, vertices_97, vertices_289, vertices_545, vertices_193, vertices_385, vertices_641, vertices_769, vertices_14, vertices_86, vertices_262, vertices_518, vertices_26, vertices_138, vertices_266, vertices_146, vertices_530, vertices_386, vertices_642, vertices_44, vertices_76, vertices_292, vertices_548, vertices_580, vertices_772, vertices_88, vertices_152, vertices_104, vertices_168, vertices_296, vertices_200, vertices_392, vertices_592, vertices_224, vertices_608, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_805), (false, vertices_217), (false, vertices_625), (false, vertices_481), (false, vertices_897), (true, vertices_14), (true, vertices_86), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_386), (true, vertices_44), (true, vertices_76), (true, vertices_580), (true, vertices_104), (true, vertices_168), (true, vertices_296), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![15, 18, 20, 22, 24, 26, 27, 28, 29]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 16 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_217) then 21 else
  if p.val = (false, vertices_625) then 23 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_86) then 17 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_76) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_392) then 14 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_86), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 3
  frame := ![0, 1, 3]
  vertex := 5
  face := Sum.inr ⟨vertices_86, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_86, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
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
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_262, (by decide +kernel)⟩ ⟨vertices_902, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 2, 4]
  vertex := 7
  face := Sum.inl ⟨vertices_302, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_302, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
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

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![3, 6, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_94, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 3] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_94, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_302, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 2, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_302, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_598, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 1, 3, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_86, (by decide +kernel)⟩ ⟨vertices_598, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_902, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![0, 1, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_262, (by decide +kernel)⟩ ⟨vertices_902, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_154, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![0, 2, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_26, (by decide +kernel)⟩ ⟨vertices_154, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_394, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![0, 2, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_138, (by decide +kernel)⟩ ⟨vertices_394, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_620, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![1, 2, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_620, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_232, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![2, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_104, (by decide +kernel)⟩ ⟨vertices_232, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet8 : boundary.facets := ⟨vertices_424, by decide +kernel⟩
noncomputable def cover8 : FacetCoverage heightProof coverFacet8 :=
  .fundamental ![2, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_168, (by decide +kernel)⟩ ⟨vertices_424, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coveringFacets : Fin 9 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6, coverFacet7, coverFacet8]
noncomputable def coveringProof (j : Fin 9) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (Fin.cases cover7 (Fin.cases cover8 (fun i => Fin.elim0 i)))))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 9, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0290

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e10q1_0291.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0291

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_355 : Finset (Fin 10) := literalFinset [0, 1, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_661 : Finset (Fin 10) := literalFinset [0, 2, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_809 : Finset (Fin 10) := literalFinset [0, 3, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_465 : Finset (Fin 10) := literalFinset [0, 4, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_785 : Finset (Fin 10) := literalFinset [0, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_737 : Finset (Fin 10) := literalFinset [0, 5, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_110 : Finset (Fin 10) := literalFinset [1, 2, 3, 5, 6] (by decide +kernel)
noncomputable def vertices_142 : Finset (Fin 10) := literalFinset [1, 2, 3, 7] (by decide +kernel)
noncomputable def vertices_710 : Finset (Fin 10) := literalFinset [1, 2, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_410 : Finset (Fin 10) := literalFinset [1, 3, 4, 7, 8] (by decide +kernel)
noncomputable def vertices_298 : Finset (Fin 10) := literalFinset [1, 3, 5, 8] (by decide +kernel)
noncomputable def vertices_450 : Finset (Fin 10) := literalFinset [1, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_156 : Finset (Fin 10) := literalFinset [2, 3, 4, 7] (by decide +kernel)
noncomputable def vertices_796 : Finset (Fin 10) := literalFinset [2, 3, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_620 : Finset (Fin 10) := literalFinset [2, 3, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_145 : Finset (Fin 10) := literalFinset [0, 4, 7] (by decide +kernel)
noncomputable def vertices_273 : Finset (Fin 10) := literalFinset [0, 4, 8] (by decide +kernel)
noncomputable def vertices_529 : Finset (Fin 10) := literalFinset [0, 4, 9] (by decide +kernel)
noncomputable def vertices_97 : Finset (Fin 10) := literalFinset [0, 5, 6] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_545 : Finset (Fin 10) := literalFinset [0, 5, 9] (by decide +kernel)
noncomputable def vertices_193 : Finset (Fin 10) := literalFinset [0, 6, 7] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_70 : Finset (Fin 10) := literalFinset [1, 2, 6] (by decide +kernel)
noncomputable def vertices_134 : Finset (Fin 10) := literalFinset [1, 2, 7] (by decide +kernel)
noncomputable def vertices_42 : Finset (Fin 10) := literalFinset [1, 3, 5] (by decide +kernel)
noncomputable def vertices_138 : Finset (Fin 10) := literalFinset [1, 3, 7] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_98 : Finset (Fin 10) := literalFinset [1, 5, 6] (by decide +kernel)
noncomputable def vertices_290 : Finset (Fin 10) := literalFinset [1, 5, 8] (by decide +kernel)
noncomputable def vertices_194 : Finset (Fin 10) := literalFinset [1, 6, 7] (by decide +kernel)
noncomputable def vertices_322 : Finset (Fin 10) := literalFinset [1, 6, 8] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_28 : Finset (Fin 10) := literalFinset [2, 3, 4] (by decide +kernel)
noncomputable def vertices_108 : Finset (Fin 10) := literalFinset [2, 3, 5, 6] (by decide +kernel)
noncomputable def vertices_140 : Finset (Fin 10) := literalFinset [2, 3, 7] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_148 : Finset (Fin 10) := literalFinset [2, 4, 7] (by decide +kernel)
noncomputable def vertices_532 : Finset (Fin 10) := literalFinset [2, 4, 9] (by decide +kernel)
noncomputable def vertices_580 : Finset (Fin 10) := literalFinset [2, 6, 9] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_152 : Finset (Fin 10) := literalFinset [3, 4, 7] (by decide +kernel)
noncomputable def vertices_280 : Finset (Fin 10) := literalFinset [3, 4, 8] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_552 : Finset (Fin 10) := literalFinset [3, 5, 9] (by decide +kernel)
noncomputable def vertices_776 : Finset (Fin 10) := literalFinset [3, 8, 9] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_784 : Finset (Fin 10) := literalFinset [4, 8, 9] (by decide +kernel)
noncomputable def vertices_608 : Finset (Fin 10) := literalFinset [5, 6, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_355, vertices_661, vertices_809, vertices_465, vertices_785, vertices_737, vertices_110, vertices_142, vertices_710, vertices_410, vertices_298, vertices_450, vertices_156, vertices_796, vertices_620] (by decide +kernel)
  polygons := literalFinset [vertices_145, vertices_273, vertices_529, vertices_97, vertices_289, vertices_545, vertices_193, vertices_321, vertices_641, vertices_769, vertices_14, vertices_70, vertices_134, vertices_42, vertices_138, vertices_266, vertices_98, vertices_290, vertices_194, vertices_322, vertices_386, vertices_28, vertices_108, vertices_140, vertices_524, vertices_148, vertices_532, vertices_580, vertices_644, vertices_152, vertices_280, vertices_296, vertices_552, vertices_776, vertices_400, vertices_784, vertices_608, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_355), (false, vertices_661), (false, vertices_809), (false, vertices_465), (false, vertices_785), (false, vertices_737), (true, vertices_14), (true, vertices_70), (true, vertices_134), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_194), (true, vertices_386), (true, vertices_28), (true, vertices_108), (true, vertices_140), (true, vertices_524), (true, vertices_580), (true, vertices_152), (true, vertices_280)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![15, 17, 20, 22, 24, 26, 27, 28, 29]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_355) then 16 else
  if p.val = (false, vertices_661) then 18 else
  if p.val = (false, vertices_809) then 21 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (false, vertices_785) then 0 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_108) then 19 else
  if p.val = (true, vertices_140) then 10 else
  if p.val = (true, vertices_524) then 11 else
  if p.val = (true, vertices_580) then 12 else
  if p.val = (true, vertices_152) then 13 else
  if p.val = (true, vertices_280) then 14 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_785), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_108), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 3
  frame := ![1, 2, 4]
  vertex := 5
  face := Sum.inr ⟨vertices_108, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_108, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 5, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_710, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_70, (by decide +kernel)⟩ ⟨vertices_710, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
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

noncomputable def row3 : HeightRow boundary where
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

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![4, 5, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_110, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_110, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_142, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 1, 2, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_142, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_710, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 1, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_70, (by decide +kernel)⟩ ⟨vertices_710, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_410, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![0, 2, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_138, (by decide +kernel)⟩ ⟨vertices_410, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_298, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![0, 2, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_42, (by decide +kernel)⟩ ⟨vertices_298, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_450, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![0, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_194, (by decide +kernel)⟩ ⟨vertices_450, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_156, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![1, 2, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_28, (by decide +kernel)⟩ ⟨vertices_156, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_796, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .oneRow ![1, 2, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_28, (by decide +kernel)⟩ ⟨vertices_796, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet8 : boundary.facets := ⟨vertices_620, by decide +kernel⟩
noncomputable def cover8 : FacetCoverage heightProof coverFacet8 :=
  .oneRow ![1, 2, 4, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_108, (by decide +kernel)⟩ ⟨vertices_620, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coveringFacets : Fin 9 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6, coverFacet7, coverFacet8]
noncomputable def coveringProof (j : Fin 9) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (Fin.cases cover7 (Fin.cases cover8 (fun i => Fin.elim0 i)))))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 9, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0291

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e10q1_0292.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0292

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_779 : Finset (Fin 10) := literalFinset [0, 1, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_541 : Finset (Fin 10) := literalFinset [0, 2, 3, 4, 9] (by decide +kernel)
noncomputable def vertices_153 : Finset (Fin 10) := literalFinset [0, 3, 4, 7] (by decide +kernel)
noncomputable def vertices_425 : Finset (Fin 10) := literalFinset [0, 3, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_241 : Finset (Fin 10) := literalFinset [0, 4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_817 : Finset (Fin 10) := literalFinset [0, 4, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_334 : Finset (Fin 10) := literalFinset [1, 2, 3, 6, 8] (by decide +kernel)
noncomputable def vertices_590 : Finset (Fin 10) := literalFinset [1, 2, 3, 6, 9] (by decide +kernel)
noncomputable def vertices_626 : Finset (Fin 10) := literalFinset [1, 4, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_354 : Finset (Fin 10) := literalFinset [1, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_802 : Finset (Fin 10) := literalFinset [1, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_156 : Finset (Fin 10) := literalFinset [2, 3, 4, 7] (by decide +kernel)
noncomputable def vertices_396 : Finset (Fin 10) := literalFinset [2, 3, 7, 8] (by decide +kernel)
noncomputable def vertices_724 : Finset (Fin 10) := literalFinset [2, 4, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_484 : Finset (Fin 10) := literalFinset [2, 5, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_25 : Finset (Fin 10) := literalFinset [0, 3, 4] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_265 : Finset (Fin 10) := literalFinset [0, 3, 8] (by decide +kernel)
noncomputable def vertices_521 : Finset (Fin 10) := literalFinset [0, 3, 9] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_145 : Finset (Fin 10) := literalFinset [0, 4, 7] (by decide +kernel)
noncomputable def vertices_529 : Finset (Fin 10) := literalFinset [0, 4, 9] (by decide +kernel)
noncomputable def vertices_161 : Finset (Fin 10) := literalFinset [0, 5, 7] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_78 : Finset (Fin 10) := literalFinset [1, 2, 3, 6] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_522 : Finset (Fin 10) := literalFinset [1, 3, 9] (by decide +kernel)
noncomputable def vertices_98 : Finset (Fin 10) := literalFinset [1, 5, 6] (by decide +kernel)
noncomputable def vertices_290 : Finset (Fin 10) := literalFinset [1, 5, 8] (by decide +kernel)
noncomputable def vertices_546 : Finset (Fin 10) := literalFinset [1, 5, 9] (by decide +kernel)
noncomputable def vertices_322 : Finset (Fin 10) := literalFinset [1, 6, 8] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_28 : Finset (Fin 10) := literalFinset [2, 3, 4] (by decide +kernel)
noncomputable def vertices_140 : Finset (Fin 10) := literalFinset [2, 3, 7] (by decide +kernel)
noncomputable def vertices_268 : Finset (Fin 10) := literalFinset [2, 3, 8] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_148 : Finset (Fin 10) := literalFinset [2, 4, 7] (by decide +kernel)
noncomputable def vertices_532 : Finset (Fin 10) := literalFinset [2, 4, 9] (by decide +kernel)
noncomputable def vertices_196 : Finset (Fin 10) := literalFinset [2, 6, 7] (by decide +kernel)
noncomputable def vertices_324 : Finset (Fin 10) := literalFinset [2, 6, 8] (by decide +kernel)
noncomputable def vertices_580 : Finset (Fin 10) := literalFinset [2, 6, 9] (by decide +kernel)
noncomputable def vertices_388 : Finset (Fin 10) := literalFinset [2, 7, 8] (by decide +kernel)
noncomputable def vertices_152 : Finset (Fin 10) := literalFinset [3, 4, 7] (by decide +kernel)
noncomputable def vertices_392 : Finset (Fin 10) := literalFinset [3, 7, 8] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_208 : Finset (Fin 10) := literalFinset [4, 6, 7] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_224 : Finset (Fin 10) := literalFinset [5, 6, 7] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_541, vertices_153, vertices_425, vertices_241, vertices_817, vertices_334, vertices_590, vertices_626, vertices_354, vertices_802, vertices_156, vertices_396, vertices_724, vertices_484] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_265, vertices_521, vertices_49, vertices_145, vertices_529, vertices_161, vertices_289, vertices_769, vertices_78, vertices_266, vertices_522, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_28, vertices_140, vertices_268, vertices_524, vertices_148, vertices_532, vertices_196, vertices_324, vertices_580, vertices_388, vertices_152, vertices_392, vertices_112, vertices_560, vertices_208, vertices_592, vertices_224, vertices_352, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_541), (false, vertices_153), (false, vertices_425), (false, vertices_241), (false, vertices_817), (true, vertices_78), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_322), (true, vertices_578), (true, vertices_140), (true, vertices_268), (true, vertices_148), (true, vertices_196), (true, vertices_324), (true, vertices_580), (true, vertices_388), (true, vertices_592), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![15, 18, 20, 22, 25, 26, 27, 28, 29]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_541) then 19 else
  if p.val = (false, vertices_153) then 0 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (false, vertices_817) then 24 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_388) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_352) then 14 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_153), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_78), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 3
  frame := ![0, 1, 2]
  vertex := 5
  face := Sum.inr ⟨vertices_78, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_78, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 3, 4, 5]
  vertex := 8
  face := Sum.inl ⟨vertices_626, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_98, (by decide +kernel)⟩ ⟨vertices_626, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
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
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_148, (by decide +kernel)⟩ ⟨vertices_724, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
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
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_196, (by decide +kernel)⟩ ⟨vertices_484, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![2, 0, 3, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_334, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_78, (by decide +kernel)⟩ ⟨vertices_334, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_590, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 2, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_78, (by decide +kernel)⟩ ⟨vertices_590, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_626, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_98, (by decide +kernel)⟩ ⟨vertices_626, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_354, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_98, (by decide +kernel)⟩ ⟨vertices_354, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_802, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![0, 4, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_290, (by decide +kernel)⟩ ⟨vertices_802, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_156, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![1, 2, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_28, (by decide +kernel)⟩ ⟨vertices_156, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_396, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![1, 2, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_140, (by decide +kernel)⟩ ⟨vertices_396, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_724, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .oneRow ![1, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_148, (by decide +kernel)⟩ ⟨vertices_724, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet8 : boundary.facets := ⟨vertices_484, by decide +kernel⟩
noncomputable def cover8 : FacetCoverage heightProof coverFacet8 :=
  .oneRow ![1, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_196, (by decide +kernel)⟩ ⟨vertices_484, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coveringFacets : Fin 9 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6, coverFacet7, coverFacet8]
noncomputable def coveringProof (j : Fin 9) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (Fin.cases cover7 (Fin.cases cover8 (fun i => Fin.elim0 i)))))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 9, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0292

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e10q1_0293.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0293

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_227 : Finset (Fin 10) := literalFinset [0, 1, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_541 : Finset (Fin 10) := literalFinset [0, 2, 3, 4, 9] (by decide +kernel)
noncomputable def vertices_153 : Finset (Fin 10) := literalFinset [0, 3, 4, 7] (by decide +kernel)
noncomputable def vertices_713 : Finset (Fin 10) := literalFinset [0, 3, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_625 : Finset (Fin 10) := literalFinset [0, 4, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_433 : Finset (Fin 10) := literalFinset [0, 4, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_206 : Finset (Fin 10) := literalFinset [1, 2, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_334 : Finset (Fin 10) := literalFinset [1, 2, 3, 6, 8] (by decide +kernel)
noncomputable def vertices_406 : Finset (Fin 10) := literalFinset [1, 2, 4, 7, 8] (by decide +kernel)
noncomputable def vertices_354 : Finset (Fin 10) := literalFinset [1, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_418 : Finset (Fin 10) := literalFinset [1, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_156 : Finset (Fin 10) := literalFinset [2, 3, 4, 7] (by decide +kernel)
noncomputable def vertices_780 : Finset (Fin 10) := literalFinset [2, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_820 : Finset (Fin 10) := literalFinset [2, 4, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_872 : Finset (Fin 10) := literalFinset [3, 5, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_25 : Finset (Fin 10) := literalFinset [0, 3, 4] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_521 : Finset (Fin 10) := literalFinset [0, 3, 9] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_145 : Finset (Fin 10) := literalFinset [0, 4, 7] (by decide +kernel)
noncomputable def vertices_529 : Finset (Fin 10) := literalFinset [0, 4, 9] (by decide +kernel)
noncomputable def vertices_97 : Finset (Fin 10) := literalFinset [0, 5, 6] (by decide +kernel)
noncomputable def vertices_161 : Finset (Fin 10) := literalFinset [0, 5, 7] (by decide +kernel)
noncomputable def vertices_193 : Finset (Fin 10) := literalFinset [0, 6, 7] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_78 : Finset (Fin 10) := literalFinset [1, 2, 3, 6] (by decide +kernel)
noncomputable def vertices_134 : Finset (Fin 10) := literalFinset [1, 2, 7] (by decide +kernel)
noncomputable def vertices_262 : Finset (Fin 10) := literalFinset [1, 2, 8] (by decide +kernel)
noncomputable def vertices_98 : Finset (Fin 10) := literalFinset [1, 5, 6] (by decide +kernel)
noncomputable def vertices_162 : Finset (Fin 10) := literalFinset [1, 5, 7] (by decide +kernel)
noncomputable def vertices_290 : Finset (Fin 10) := literalFinset [1, 5, 8] (by decide +kernel)
noncomputable def vertices_194 : Finset (Fin 10) := literalFinset [1, 6, 7] (by decide +kernel)
noncomputable def vertices_322 : Finset (Fin 10) := literalFinset [1, 6, 8] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_28 : Finset (Fin 10) := literalFinset [2, 3, 4] (by decide +kernel)
noncomputable def vertices_140 : Finset (Fin 10) := literalFinset [2, 3, 7] (by decide +kernel)
noncomputable def vertices_268 : Finset (Fin 10) := literalFinset [2, 3, 8] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_148 : Finset (Fin 10) := literalFinset [2, 4, 7] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_532 : Finset (Fin 10) := literalFinset [2, 4, 9] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_152 : Finset (Fin 10) := literalFinset [3, 4, 7] (by decide +kernel)
noncomputable def vertices_200 : Finset (Fin 10) := literalFinset [3, 6, 7] (by decide +kernel)
noncomputable def vertices_328 : Finset (Fin 10) := literalFinset [3, 6, 8] (by decide +kernel)
noncomputable def vertices_584 : Finset (Fin 10) := literalFinset [3, 6, 9] (by decide +kernel)
noncomputable def vertices_776 : Finset (Fin 10) := literalFinset [3, 8, 9] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_608 : Finset (Fin 10) := literalFinset [5, 6, 9] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_227, vertices_541, vertices_153, vertices_713, vertices_625, vertices_433, vertices_206, vertices_334, vertices_406, vertices_354, vertices_418, vertices_156, vertices_780, vertices_820, vertices_872] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_521, vertices_49, vertices_145, vertices_529, vertices_97, vertices_161, vertices_193, vertices_577, vertices_78, vertices_134, vertices_262, vertices_98, vertices_162, vertices_290, vertices_194, vertices_322, vertices_386, vertices_28, vertices_140, vertices_268, vertices_524, vertices_148, vertices_276, vertices_532, vertices_772, vertices_152, vertices_200, vertices_328, vertices_584, vertices_776, vertices_304, vertices_560, vertices_400, vertices_352, vertices_608, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_227), (false, vertices_541), (false, vertices_153), (false, vertices_713), (false, vertices_625), (false, vertices_433), (true, vertices_78), (true, vertices_134), (true, vertices_262), (true, vertices_290), (true, vertices_322), (true, vertices_386), (true, vertices_140), (true, vertices_268), (true, vertices_148), (true, vertices_276), (true, vertices_772), (true, vertices_328), (true, vertices_776), (true, vertices_352), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![15, 18, 20, 22, 25, 26, 27, 28, 29]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_227) then 16 else
  if p.val = (false, vertices_541) then 19 else
  if p.val = (false, vertices_153) then 0 else
  if p.val = (false, vertices_713) then 21 else
  if p.val = (false, vertices_625) then 23 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_352) then 13 else
  if p.val = (true, vertices_800) then 14 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_153), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_78), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 3, 6]
  vertex := 7
  face := Sum.inl ⟨vertices_406, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_134, (by decide +kernel)⟩ ⟨vertices_406, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 3
  frame := ![0, 1, 2]
  vertex := 5
  face := Sum.inr ⟨vertices_78, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_78, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
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
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_276, (by decide +kernel)⟩ ⟨vertices_820, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
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
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_328, (by decide +kernel)⟩ ⟨vertices_872, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![6, 0, 1, 2]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_206, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_78, (by decide +kernel)⟩ ⟨vertices_206, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_334, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 2, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_78, (by decide +kernel)⟩ ⟨vertices_334, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_406, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 1, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_134, (by decide +kernel)⟩ ⟨vertices_406, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_354, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_98, (by decide +kernel)⟩ ⟨vertices_354, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_418, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![0, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_162, (by decide +kernel)⟩ ⟨vertices_418, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_156, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![1, 2, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_28, (by decide +kernel)⟩ ⟨vertices_156, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_780, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![1, 2, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_268, (by decide +kernel)⟩ ⟨vertices_780, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_820, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .oneRow ![1, 3, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_276, (by decide +kernel)⟩ ⟨vertices_820, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet8 : boundary.facets := ⟨vertices_872, by decide +kernel⟩
noncomputable def cover8 : FacetCoverage heightProof coverFacet8 :=
  .oneRow ![2, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_328, (by decide +kernel)⟩ ⟨vertices_872, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coveringFacets : Fin 9 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6, coverFacet7, coverFacet8]
noncomputable def coveringProof (j : Fin 9) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (Fin.cases cover7 (Fin.cases cover8 (fun i => Fin.elim0 i)))))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 9, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0293

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m15e10q1_0294.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0294

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_707 : Finset (Fin 10) := literalFinset [0, 1, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_61 : Finset (Fin 10) := literalFinset [0, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_665 : Finset (Fin 10) := literalFinset [0, 3, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_361 : Finset (Fin 10) := literalFinset [0, 3, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_201 : Finset (Fin 10) := literalFinset [0, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_625 : Finset (Fin 10) := literalFinset [0, 4, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_206 : Finset (Fin 10) := literalFinset [1, 2, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_334 : Finset (Fin 10) := literalFinset [1, 2, 3, 6, 8] (by decide +kernel)
noncomputable def vertices_406 : Finset (Fin 10) := literalFinset [1, 2, 4, 7, 8] (by decide +kernel)
noncomputable def vertices_866 : Finset (Fin 10) := literalFinset [1, 5, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_898 : Finset (Fin 10) := literalFinset [1, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_156 : Finset (Fin 10) := literalFinset [2, 3, 4, 7] (by decide +kernel)
noncomputable def vertices_300 : Finset (Fin 10) := literalFinset [2, 3, 5, 8] (by decide +kernel)
noncomputable def vertices_308 : Finset (Fin 10) := literalFinset [2, 4, 5, 8] (by decide +kernel)
noncomputable def vertices_944 : Finset (Fin 10) := literalFinset [4, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_25 : Finset (Fin 10) := literalFinset [0, 3, 4] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_73 : Finset (Fin 10) := literalFinset [0, 3, 6] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_529 : Finset (Fin 10) := literalFinset [0, 4, 9] (by decide +kernel)
noncomputable def vertices_97 : Finset (Fin 10) := literalFinset [0, 5, 6] (by decide +kernel)
noncomputable def vertices_193 : Finset (Fin 10) := literalFinset [0, 6, 7] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_78 : Finset (Fin 10) := literalFinset [1, 2, 3, 6] (by decide +kernel)
noncomputable def vertices_134 : Finset (Fin 10) := literalFinset [1, 2, 7] (by decide +kernel)
noncomputable def vertices_262 : Finset (Fin 10) := literalFinset [1, 2, 8] (by decide +kernel)
noncomputable def vertices_194 : Finset (Fin 10) := literalFinset [1, 6, 7] (by decide +kernel)
noncomputable def vertices_322 : Finset (Fin 10) := literalFinset [1, 6, 8] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_28 : Finset (Fin 10) := literalFinset [2, 3, 4] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_140 : Finset (Fin 10) := literalFinset [2, 3, 7] (by decide +kernel)
noncomputable def vertices_268 : Finset (Fin 10) := literalFinset [2, 3, 8] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_148 : Finset (Fin 10) := literalFinset [2, 4, 7] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_292 : Finset (Fin 10) := literalFinset [2, 5, 8] (by decide +kernel)
noncomputable def vertices_152 : Finset (Fin 10) := literalFinset [3, 4, 7] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_200 : Finset (Fin 10) := literalFinset [3, 6, 7] (by decide +kernel)
noncomputable def vertices_328 : Finset (Fin 10) := literalFinset [3, 6, 8] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_608 : Finset (Fin 10) := literalFinset [5, 6, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_896 : Finset (Fin 10) := literalFinset [7, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_61, vertices_665, vertices_361, vertices_201, vertices_625, vertices_206, vertices_334, vertices_406, vertices_866, vertices_898, vertices_156, vertices_300, vertices_308, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_73, vertices_137, vertices_49, vertices_529, vertices_97, vertices_193, vertices_577, vertices_641, vertices_78, vertices_134, vertices_262, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_140, vertices_268, vertices_52, vertices_148, vertices_276, vertices_292, vertices_152, vertices_296, vertices_200, vertices_328, vertices_304, vertices_560, vertices_400, vertices_656, vertices_352, vertices_608, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_61), (false, vertices_665), (false, vertices_361), (false, vertices_201), (false, vertices_625), (true, vertices_78), (true, vertices_134), (true, vertices_262), (true, vertices_322), (true, vertices_386), (true, vertices_770), (true, vertices_140), (true, vertices_268), (true, vertices_148), (true, vertices_276), (true, vertices_292), (true, vertices_304), (true, vertices_400), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![15, 18, 20, 23, 25, 26, 27, 28, 29]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_61) then 19 else
  if p.val = (false, vertices_665) then 21 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_201) then 0 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_800) then 13 else
  if p.val = (true, vertices_896) then 14 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_201), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_78), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_61), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 3
  frame := ![0, 1, 2]
  vertex := 5
  face := Sum.inr ⟨vertices_78, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_78, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 3, 6]
  vertex := 7
  face := Sum.inl ⟨vertices_406, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_134, (by decide +kernel)⟩ ⟨vertices_406, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
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
  frame := ![3, 4, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_944, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_304, (by decide +kernel)⟩ ⟨vertices_944, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![2, 1, 0, 3]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_206, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_78, (by decide +kernel)⟩ ⟨vertices_206, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_334, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 2, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_78, (by decide +kernel)⟩ ⟨vertices_334, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_406, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 1, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_134, (by decide +kernel)⟩ ⟨vertices_406, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_866, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![0, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_322, (by decide +kernel)⟩ ⟨vertices_866, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_898, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![0, 6, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_386, (by decide +kernel)⟩ ⟨vertices_898, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_156, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![1, 2, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_28, (by decide +kernel)⟩ ⟨vertices_156, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_300, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![1, 2, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_300, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_308, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![1, 3, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_308, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet8 : boundary.facets := ⟨vertices_944, by decide +kernel⟩
noncomputable def cover8 : FacetCoverage heightProof coverFacet8 :=
  .oneRow ![3, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_304, (by decide +kernel)⟩ ⟨vertices_944, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coveringFacets : Fin 9 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6, coverFacet7, coverFacet8]
noncomputable def coveringProof (j : Fin 9) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (Fin.cases cover7 (Fin.cases cover8 (fun i => Fin.elim0 i)))))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 9, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0294

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m15e10q1_0295.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0295

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_659 : Finset (Fin 10) := literalFinset [0, 1, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_333 : Finset (Fin 10) := literalFinset [0, 2, 3, 6, 8] (by decide +kernel)
noncomputable def vertices_597 : Finset (Fin 10) := literalFinset [0, 2, 4, 6, 9] (by decide +kernel)
noncomputable def vertices_901 : Finset (Fin 10) := literalFinset [0, 2, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_433 : Finset (Fin 10) := literalFinset [0, 4, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_337 : Finset (Fin 10) := literalFinset [0, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_398 : Finset (Fin 10) := literalFinset [1, 2, 3, 7, 8] (by decide +kernel)
noncomputable def vertices_654 : Finset (Fin 10) := literalFinset [1, 2, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_570 : Finset (Fin 10) := literalFinset [1, 3, 4, 5, 9] (by decide +kernel)
noncomputable def vertices_362 : Finset (Fin 10) := literalFinset [1, 3, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_178 : Finset (Fin 10) := literalFinset [1, 4, 5, 7] (by decide +kernel)
noncomputable def vertices_418 : Finset (Fin 10) := literalFinset [1, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_620 : Finset (Fin 10) := literalFinset [2, 3, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_368 : Finset (Fin 10) := literalFinset [4, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_624 : Finset (Fin 10) := literalFinset [4, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_69 : Finset (Fin 10) := literalFinset [0, 2, 6] (by decide +kernel)
noncomputable def vertices_261 : Finset (Fin 10) := literalFinset [0, 2, 8] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_145 : Finset (Fin 10) := literalFinset [0, 4, 7] (by decide +kernel)
noncomputable def vertices_273 : Finset (Fin 10) := literalFinset [0, 4, 8] (by decide +kernel)
noncomputable def vertices_529 : Finset (Fin 10) := literalFinset [0, 4, 9] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_385 : Finset (Fin 10) := literalFinset [0, 7, 8] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_142 : Finset (Fin 10) := literalFinset [1, 2, 3, 7] (by decide +kernel)
noncomputable def vertices_42 : Finset (Fin 10) := literalFinset [1, 3, 5] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_522 : Finset (Fin 10) := literalFinset [1, 3, 9] (by decide +kernel)
noncomputable def vertices_50 : Finset (Fin 10) := literalFinset [1, 4, 5] (by decide +kernel)
noncomputable def vertices_146 : Finset (Fin 10) := literalFinset [1, 4, 7] (by decide +kernel)
noncomputable def vertices_530 : Finset (Fin 10) := literalFinset [1, 4, 9] (by decide +kernel)
noncomputable def vertices_162 : Finset (Fin 10) := literalFinset [1, 5, 7] (by decide +kernel)
noncomputable def vertices_290 : Finset (Fin 10) := literalFinset [1, 5, 8] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_76 : Finset (Fin 10) := literalFinset [2, 3, 6] (by decide +kernel)
noncomputable def vertices_268 : Finset (Fin 10) := literalFinset [2, 3, 8] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_580 : Finset (Fin 10) := literalFinset [2, 6, 9] (by decide +kernel)
noncomputable def vertices_388 : Finset (Fin 10) := literalFinset [2, 7, 8] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_104 : Finset (Fin 10) := literalFinset [3, 5, 6] (by decide +kernel)
noncomputable def vertices_552 : Finset (Fin 10) := literalFinset [3, 5, 9] (by decide +kernel)
noncomputable def vertices_328 : Finset (Fin 10) := literalFinset [3, 6, 8] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_592 : Finset (Fin 10) := literalFinset [4, 6, 9] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_608 : Finset (Fin 10) := literalFinset [5, 6, 9] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_333, vertices_597, vertices_901, vertices_433, vertices_337, vertices_398, vertices_654, vertices_570, vertices_362, vertices_178, vertices_418, vertices_620, vertices_368, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_81, vertices_145, vertices_273, vertices_529, vertices_321, vertices_385, vertices_641, vertices_142, vertices_42, vertices_266, vertices_522, vertices_50, vertices_146, vertices_530, vertices_162, vertices_290, vertices_386, vertices_642, vertices_76, vertices_268, vertices_524, vertices_580, vertices_388, vertices_644, vertices_104, vertices_552, vertices_328, vertices_112, vertices_176, vertices_304, vertices_560, vertices_336, vertices_592, vertices_352, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_333), (false, vertices_597), (false, vertices_901), (false, vertices_433), (false, vertices_337), (true, vertices_142), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_162), (true, vertices_290), (true, vertices_386), (true, vertices_524), (true, vertices_104), (true, vertices_552), (true, vertices_112), (true, vertices_560), (true, vertices_352), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![15, 18, 22, 23, 25, 26, 27, 28, 29]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 16 else
  if p.val = (false, vertices_333) then 19 else
  if p.val = (false, vertices_597) then 20 else
  if p.val = (false, vertices_901) then 21 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (true, vertices_142) then 17 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_352) then 13 else
  if p.val = (true, vertices_608) then 14 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_337), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_142), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 3
  frame := ![0, 1, 2]
  vertex := 6
  face := Sum.inr ⟨vertices_142, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_142, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 4]
  vertex := 8
  face := Sum.inl ⟨vertices_570, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_42, (by decide +kernel)⟩ ⟨vertices_570, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 4, 5]
  vertex := 7
  face := Sum.inl ⟨vertices_362, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_42, (by decide +kernel)⟩ ⟨vertices_362, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 4, 5]
  vertex := 8
  face := Sum.inl ⟨vertices_620, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_76, (by decide +kernel)⟩ ⟨vertices_620, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![6, 3, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_398, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_142, (by decide +kernel)⟩ ⟨vertices_398, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_654, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 2, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_142, (by decide +kernel)⟩ ⟨vertices_654, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_570, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 2, 3, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_42, (by decide +kernel)⟩ ⟨vertices_570, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_362, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![0, 2, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_42, (by decide +kernel)⟩ ⟨vertices_362, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_178, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![0, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_50, (by decide +kernel)⟩ ⟨vertices_178, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_418, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![0, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_162, (by decide +kernel)⟩ ⟨vertices_418, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_620, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![1, 2, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_76, (by decide +kernel)⟩ ⟨vertices_620, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_368, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![3, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_368, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet8 : boundary.facets := ⟨vertices_624, by decide +kernel⟩
noncomputable def cover8 : FacetCoverage heightProof coverFacet8 :=
  .fundamental ![3, 4, 5, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_624, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coveringFacets : Fin 9 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6, coverFacet7, coverFacet8]
noncomputable def coveringProof (j : Fin 9) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (Fin.cases cover7 (Fin.cases cover8 (fun i => Fin.elim0 i)))))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 9, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0295

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m15e10q1_0296.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0296

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_583 : Finset (Fin 10) := literalFinset [0, 1, 2, 6, 9] (by decide +kernel)
noncomputable def vertices_173 : Finset (Fin 10) := literalFinset [0, 2, 3, 5, 7] (by decide +kernel)
noncomputable def vertices_653 : Finset (Fin 10) := literalFinset [0, 2, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_357 : Finset (Fin 10) := literalFinset [0, 2, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_313 : Finset (Fin 10) := literalFinset [0, 3, 4, 5, 8] (by decide +kernel)
noncomputable def vertices_841 : Finset (Fin 10) := literalFinset [0, 3, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_662 : Finset (Fin 10) := literalFinset [1, 2, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_198 : Finset (Fin 10) := literalFinset [1, 2, 6, 7] (by decide +kernel)
noncomputable def vertices_794 : Finset (Fin 10) := literalFinset [1, 3, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_370 : Finset (Fin 10) := literalFinset [1, 4, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_210 : Finset (Fin 10) := literalFinset [1, 4, 6, 7] (by decide +kernel)
noncomputable def vertices_834 : Finset (Fin 10) := literalFinset [1, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_228 : Finset (Fin 10) := literalFinset [2, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_696 : Finset (Fin 10) := literalFinset [3, 4, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_240 : Finset (Fin 10) := literalFinset [4, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_141 : Finset (Fin 10) := literalFinset [0, 2, 3, 7] (by decide +kernel)
noncomputable def vertices_37 : Finset (Fin 10) := literalFinset [0, 2, 5] (by decide +kernel)
noncomputable def vertices_69 : Finset (Fin 10) := literalFinset [0, 2, 6] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_41 : Finset (Fin 10) := literalFinset [0, 3, 5] (by decide +kernel)
noncomputable def vertices_265 : Finset (Fin 10) := literalFinset [0, 3, 8] (by decide +kernel)
noncomputable def vertices_521 : Finset (Fin 10) := literalFinset [0, 3, 9] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_70 : Finset (Fin 10) := literalFinset [1, 2, 6] (by decide +kernel)
noncomputable def vertices_134 : Finset (Fin 10) := literalFinset [1, 2, 7] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_82 : Finset (Fin 10) := literalFinset [1, 4, 6] (by decide +kernel)
noncomputable def vertices_146 : Finset (Fin 10) := literalFinset [1, 4, 7] (by decide +kernel)
noncomputable def vertices_274 : Finset (Fin 10) := literalFinset [1, 4, 8] (by decide +kernel)
noncomputable def vertices_530 : Finset (Fin 10) := literalFinset [1, 4, 9] (by decide +kernel)
noncomputable def vertices_194 : Finset (Fin 10) := literalFinset [1, 6, 7] (by decide +kernel)
noncomputable def vertices_322 : Finset (Fin 10) := literalFinset [1, 6, 8] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_100 : Finset (Fin 10) := literalFinset [2, 5, 6] (by decide +kernel)
noncomputable def vertices_164 : Finset (Fin 10) := literalFinset [2, 5, 7] (by decide +kernel)
noncomputable def vertices_196 : Finset (Fin 10) := literalFinset [2, 6, 7] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_56 : Finset (Fin 10) := literalFinset [3, 4, 5] (by decide +kernel)
noncomputable def vertices_280 : Finset (Fin 10) := literalFinset [3, 4, 8] (by decide +kernel)
noncomputable def vertices_536 : Finset (Fin 10) := literalFinset [3, 4, 9] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_648 : Finset (Fin 10) := literalFinset [3, 7, 9] (by decide +kernel)
noncomputable def vertices_776 : Finset (Fin 10) := literalFinset [3, 8, 9] (by decide +kernel)
noncomputable def vertices_112 : Finset (Fin 10) := literalFinset [4, 5, 6] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_208 : Finset (Fin 10) := literalFinset [4, 6, 7] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_224 : Finset (Fin 10) := literalFinset [5, 6, 7] (by decide +kernel)
noncomputable def vertices_352 : Finset (Fin 10) := literalFinset [5, 6, 8] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_583, vertices_173, vertices_653, vertices_357, vertices_313, vertices_841, vertices_662, vertices_198, vertices_794, vertices_370, vertices_210, vertices_834, vertices_228, vertices_696, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_141, vertices_37, vertices_69, vertices_517, vertices_41, vertices_265, vertices_521, vertices_289, vertices_321, vertices_577, vertices_70, vertices_134, vertices_518, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_770, vertices_100, vertices_164, vertices_196, vertices_644, vertices_56, vertices_280, vertices_536, vertices_168, vertices_648, vertices_776, vertices_112, vertices_176, vertices_304, vertices_208, vertices_656, vertices_224, vertices_352, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_583), (false, vertices_173), (false, vertices_653), (false, vertices_357), (false, vertices_313), (false, vertices_841), (true, vertices_134), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_194), (true, vertices_322), (true, vertices_770), (true, vertices_196), (true, vertices_536), (true, vertices_112), (true, vertices_176), (true, vertices_208), (true, vertices_656), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![15, 17, 21, 24, 25, 26, 27, 28, 29]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_583) then 16 else
  if p.val = (false, vertices_173) then 18 else
  if p.val = (false, vertices_653) then 19 else
  if p.val = (false, vertices_357) then 20 else
  if p.val = (false, vertices_313) then 22 else
  if p.val = (false, vertices_841) then 23 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_656) then 13 else
  if p.val = (true, vertices_224) then 14 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
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
  frame := ![0, 3, 4, 5]
  vertex := 7
  face := Sum.inl ⟨vertices_370, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_82, (by decide +kernel)⟩ ⟨vertices_370, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_794, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_274, (by decide +kernel)⟩ ⟨vertices_794, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
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

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![1, 5, 0, 2]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_662, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_134, (by decide +kernel)⟩ ⟨vertices_662, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_198, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 1, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_70, (by decide +kernel)⟩ ⟨vertices_198, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_794, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 2, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_274, (by decide +kernel)⟩ ⟨vertices_794, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_370, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![0, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_82, (by decide +kernel)⟩ ⟨vertices_370, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_210, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![0, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_82, (by decide +kernel)⟩ ⟨vertices_210, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_834, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![0, 5, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_322, (by decide +kernel)⟩ ⟨vertices_834, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_228, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![1, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_100, (by decide +kernel)⟩ ⟨vertices_228, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_696, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .oneRow ![2, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_696, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet8 : boundary.facets := ⟨vertices_240, by decide +kernel⟩
noncomputable def cover8 : FacetCoverage heightProof coverFacet8 :=
  .fundamental ![3, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_112, (by decide +kernel)⟩ ⟨vertices_240, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coveringFacets : Fin 9 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6, coverFacet7, coverFacet8]
noncomputable def coveringProof (j : Fin 9) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (Fin.cases cover7 (Fin.cases cover8 (fun i => Fin.elim0 i)))))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 9, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0296

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m15e10q1_0297.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0297

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_211 : Finset (Fin 10) := literalFinset [0, 1, 4, 6, 7] (by decide +kernel)
noncomputable def vertices_61 : Finset (Fin 10) := literalFinset [0, 2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_93 : Finset (Fin 10) := literalFinset [0, 2, 3, 4, 6] (by decide +kernel)
noncomputable def vertices_805 : Finset (Fin 10) := literalFinset [0, 2, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_709 : Finset (Fin 10) := literalFinset [0, 2, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_689 : Finset (Fin 10) := literalFinset [0, 4, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_838 : Finset (Fin 10) := literalFinset [1, 2, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_410 : Finset (Fin 10) := literalFinset [1, 3, 4, 7, 8] (by decide +kernel)
noncomputable def vertices_338 : Finset (Fin 10) := literalFinset [1, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_930 : Finset (Fin 10) := literalFinset [1, 5, 7, 8, 9] (by decide +kernel)
noncomputable def vertices_706 : Finset (Fin 10) := literalFinset [1, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_364 : Finset (Fin 10) := literalFinset [2, 3, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_184 : Finset (Fin 10) := literalFinset [3, 4, 5, 7] (by decide +kernel)
noncomputable def vertices_344 : Finset (Fin 10) := literalFinset [3, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_424 : Finset (Fin 10) := literalFinset [3, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_29 : Finset (Fin 10) := literalFinset [0, 2, 3, 4] (by decide +kernel)
noncomputable def vertices_37 : Finset (Fin 10) := literalFinset [0, 2, 5] (by decide +kernel)
noncomputable def vertices_69 : Finset (Fin 10) := literalFinset [0, 2, 6] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_145 : Finset (Fin 10) := literalFinset [0, 4, 7] (by decide +kernel)
noncomputable def vertices_545 : Finset (Fin 10) := literalFinset [0, 5, 9] (by decide +kernel)
noncomputable def vertices_193 : Finset (Fin 10) := literalFinset [0, 6, 7] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_82 : Finset (Fin 10) := literalFinset [1, 4, 6] (by decide +kernel)
noncomputable def vertices_146 : Finset (Fin 10) := literalFinset [1, 4, 7] (by decide +kernel)
noncomputable def vertices_274 : Finset (Fin 10) := literalFinset [1, 4, 8] (by decide +kernel)
noncomputable def vertices_194 : Finset (Fin 10) := literalFinset [1, 6, 7] (by decide +kernel)
noncomputable def vertices_322 : Finset (Fin 10) := literalFinset [1, 6, 8] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_76 : Finset (Fin 10) := literalFinset [2, 3, 6] (by decide +kernel)
noncomputable def vertices_292 : Finset (Fin 10) := literalFinset [2, 5, 8] (by decide +kernel)
noncomputable def vertices_324 : Finset (Fin 10) := literalFinset [2, 6, 8] (by decide +kernel)
noncomputable def vertices_580 : Finset (Fin 10) := literalFinset [2, 6, 9] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_56 : Finset (Fin 10) := literalFinset [3, 4, 5] (by decide +kernel)
noncomputable def vertices_88 : Finset (Fin 10) := literalFinset [3, 4, 6] (by decide +kernel)
noncomputable def vertices_152 : Finset (Fin 10) := literalFinset [3, 4, 7] (by decide +kernel)
noncomputable def vertices_280 : Finset (Fin 10) := literalFinset [3, 4, 8] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_328 : Finset (Fin 10) := literalFinset [3, 6, 8] (by decide +kernel)
noncomputable def vertices_392 : Finset (Fin 10) := literalFinset [3, 7, 8] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_211, vertices_61, vertices_93, vertices_805, vertices_709, vertices_689, vertices_838, vertices_410, vertices_338, vertices_930, vertices_706, vertices_364, vertices_184, vertices_344, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_29, vertices_37, vertices_69, vertices_517, vertices_49, vertices_81, vertices_145, vertices_545, vertices_193, vertices_641, vertices_82, vertices_146, vertices_274, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_44, vertices_76, vertices_292, vertices_324, vertices_580, vertices_772, vertices_56, vertices_88, vertices_152, vertices_280, vertices_168, vertices_296, vertices_328, vertices_392, vertices_176, vertices_336, vertices_416, vertices_672, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_211), (false, vertices_61), (false, vertices_93), (false, vertices_805), (false, vertices_709), (false, vertices_689), (true, vertices_274), (true, vertices_322), (true, vertices_578), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_324), (true, vertices_152), (true, vertices_280), (true, vertices_168), (true, vertices_296), (true, vertices_328), (true, vertices_392), (true, vertices_336), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![15, 20, 17, 23, 25, 26, 27, 28, 29]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_211) then 16 else
  if p.val = (false, vertices_61) then 18 else
  if p.val = (false, vertices_93) then 19 else
  if p.val = (false, vertices_805) then 21 else
  if p.val = (false, vertices_709) then 22 else
  if p.val = (false, vertices_689) then 24 else
  if p.val = (true, vertices_274) then 0 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_578) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_324) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_61), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
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
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_146, (by decide +kernel)⟩ ⟨vertices_410, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 4, 6, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_930, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_386, (by decide +kernel)⟩ ⟨vertices_930, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
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
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_322, (by decide +kernel)⟩ ⟨vertices_838, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
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

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_838, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_322, (by decide +kernel)⟩ ⟨vertices_838, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_410, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 2, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_146, (by decide +kernel)⟩ ⟨vertices_410, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_338, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_82, (by decide +kernel)⟩ ⟨vertices_338, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_930, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![0, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_386, (by decide +kernel)⟩ ⟨vertices_930, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_706, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![0, 5, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_194, (by decide +kernel)⟩ ⟨vertices_706, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_364, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![1, 2, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_364, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_184, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![2, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_56, (by decide +kernel)⟩ ⟨vertices_184, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_344, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![2, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_88, (by decide +kernel)⟩ ⟨vertices_344, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet8 : boundary.facets := ⟨vertices_424, by decide +kernel⟩
noncomputable def cover8 : FacetCoverage heightProof coverFacet8 :=
  .fundamental ![2, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_168, (by decide +kernel)⟩ ⟨vertices_424, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coveringFacets : Fin 9 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6, coverFacet7, coverFacet8]
noncomputable def coveringProof (j : Fin 9) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (Fin.cases cover7 (Fin.cases cover8 (fun i => Fin.elim0 i)))))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 9, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0297

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m15e10q1_0298.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0298

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_327 : Finset (Fin 10) := literalFinset [0, 1, 2, 6, 8] (by decide +kernel)
noncomputable def vertices_775 : Finset (Fin 10) := literalFinset [0, 1, 2, 8, 9] (by decide +kernel)
noncomputable def vertices_203 : Finset (Fin 10) := literalFinset [0, 1, 3, 6, 7] (by decide +kernel)
noncomputable def vertices_659 : Finset (Fin 10) := literalFinset [0, 1, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_681 : Finset (Fin 10) := literalFinset [0, 3, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_841 : Finset (Fin 10) := literalFinset [0, 3, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_566 : Finset (Fin 10) := literalFinset [1, 2, 4, 5, 9] (by decide +kernel)
noncomputable def vertices_86 : Finset (Fin 10) := literalFinset [1, 2, 4, 6] (by decide +kernel)
noncomputable def vertices_210 : Finset (Fin 10) := literalFinset [1, 4, 6, 7] (by decide +kernel)
noncomputable def vertices_812 : Finset (Fin 10) := literalFinset [2, 3, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_436 : Finset (Fin 10) := literalFinset [2, 4, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_340 : Finset (Fin 10) := literalFinset [2, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_472 : Finset (Fin 10) := literalFinset [3, 4, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_424 : Finset (Fin 10) := literalFinset [3, 5, 7, 8] (by decide +kernel)
noncomputable def vertices_688 : Finset (Fin 10) := literalFinset [4, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_263 : Finset (Fin 10) := literalFinset [0, 1, 2, 8] (by decide +kernel)
noncomputable def vertices_67 : Finset (Fin 10) := literalFinset [0, 1, 6] (by decide +kernel)
noncomputable def vertices_131 : Finset (Fin 10) := literalFinset [0, 1, 7] (by decide +kernel)
noncomputable def vertices_515 : Finset (Fin 10) := literalFinset [0, 1, 9] (by decide +kernel)
noncomputable def vertices_73 : Finset (Fin 10) := literalFinset [0, 3, 6] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_521 : Finset (Fin 10) := literalFinset [0, 3, 9] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_22 : Finset (Fin 10) := literalFinset [1, 2, 4] (by decide +kernel)
noncomputable def vertices_70 : Finset (Fin 10) := literalFinset [1, 2, 6] (by decide +kernel)
noncomputable def vertices_518 : Finset (Fin 10) := literalFinset [1, 2, 9] (by decide +kernel)
noncomputable def vertices_82 : Finset (Fin 10) := literalFinset [1, 4, 6] (by decide +kernel)
noncomputable def vertices_146 : Finset (Fin 10) := literalFinset [1, 4, 7] (by decide +kernel)
noncomputable def vertices_530 : Finset (Fin 10) := literalFinset [1, 4, 9] (by decide +kernel)
noncomputable def vertices_194 : Finset (Fin 10) := literalFinset [1, 6, 7] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_292 : Finset (Fin 10) := literalFinset [2, 5, 8] (by decide +kernel)
noncomputable def vertices_548 : Finset (Fin 10) := literalFinset [2, 5, 9] (by decide +kernel)
noncomputable def vertices_324 : Finset (Fin 10) := literalFinset [2, 6, 8] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_552 : Finset (Fin 10) := literalFinset [3, 5, 9] (by decide +kernel)
noncomputable def vertices_200 : Finset (Fin 10) := literalFinset [3, 6, 7] (by decide +kernel)
noncomputable def vertices_328 : Finset (Fin 10) := literalFinset [3, 6, 8] (by decide +kernel)
noncomputable def vertices_392 : Finset (Fin 10) := literalFinset [3, 7, 8] (by decide +kernel)
noncomputable def vertices_776 : Finset (Fin 10) := literalFinset [3, 8, 9] (by decide +kernel)
noncomputable def vertices_176 : Finset (Fin 10) := literalFinset [4, 5, 7] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_208 : Finset (Fin 10) := literalFinset [4, 6, 7] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_416 : Finset (Fin 10) := literalFinset [5, 7, 8] (by decide +kernel)
noncomputable def vertices_672 : Finset (Fin 10) := literalFinset [5, 7, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_775, vertices_203, vertices_659, vertices_681, vertices_841, vertices_566, vertices_86, vertices_210, vertices_812, vertices_436, vertices_340, vertices_472, vertices_424, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_263, vertices_67, vertices_131, vertices_515, vertices_73, vertices_137, vertices_521, vertices_321, vertices_641, vertices_769, vertices_22, vertices_70, vertices_518, vertices_82, vertices_146, vertices_530, vertices_194, vertices_52, vertices_84, vertices_276, vertices_292, vertices_548, vertices_324, vertices_772, vertices_168, vertices_296, vertices_552, vertices_200, vertices_328, vertices_392, vertices_776, vertices_176, vertices_560, vertices_208, vertices_336, vertices_400, vertices_656, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_775), (false, vertices_203), (false, vertices_659), (false, vertices_681), (false, vertices_841), (true, vertices_22), (true, vertices_82), (true, vertices_52), (true, vertices_84), (true, vertices_276), (true, vertices_292), (true, vertices_548), (true, vertices_296), (true, vertices_392), (true, vertices_176), (true, vertices_560), (true, vertices_208), (true, vertices_336), (true, vertices_400), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![18, 15, 21, 24, 25, 26, 27, 28, 29]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 16 else
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_203) then 19 else
  if p.val = (false, vertices_659) then 20 else
  if p.val = (false, vertices_681) then 22 else
  if p.val = (false, vertices_841) then 23 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_52) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_276) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_392) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 3, 4]
  vertex := 8
  face := Sum.inl ⟨vertices_566, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_566, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
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
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_292, (by decide +kernel)⟩ ⟨vertices_812, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
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
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_436, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
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
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_200, (by decide +kernel)⟩ ⟨vertices_472, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 8, 1, 2]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_566, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 3, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_566, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_86, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 1, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_86, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_210, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_82, (by decide +kernel)⟩ ⟨vertices_210, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_812, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 2, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_292, (by decide +kernel)⟩ ⟨vertices_812, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_436, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![1, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_436, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_340, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![1, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_340, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_472, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![2, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_200, (by decide +kernel)⟩ ⟨vertices_472, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_424, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![2, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_168, (by decide +kernel)⟩ ⟨vertices_424, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet8 : boundary.facets := ⟨vertices_688, by decide +kernel⟩
noncomputable def cover8 : FacetCoverage heightProof coverFacet8 :=
  .fundamental ![3, 4, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_176, (by decide +kernel)⟩ ⟨vertices_688, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coveringFacets : Fin 9 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6, coverFacet7, coverFacet8]
noncomputable def coveringProof (j : Fin 9) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (Fin.cases cover7 (Fin.cases cover8 (fun i => Fin.elim0 i)))))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 9, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0298

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m15e10q1_0299.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0299

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_651 : Finset (Fin 10) := literalFinset [0, 1, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_357 : Finset (Fin 10) := literalFinset [0, 2, 5, 6, 8] (by decide +kernel)
noncomputable def vertices_457 : Finset (Fin 10) := literalFinset [0, 3, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_777 : Finset (Fin 10) := literalFinset [0, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_817 : Finset (Fin 10) := literalFinset [0, 4, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_737 : Finset (Fin 10) := literalFinset [0, 5, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_158 : Finset (Fin 10) := literalFinset [1, 2, 3, 4, 7] (by decide +kernel)
noncomputable def vertices_566 : Finset (Fin 10) := literalFinset [1, 2, 4, 5, 9] (by decide +kernel)
noncomputable def vertices_614 : Finset (Fin 10) := literalFinset [1, 2, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_198 : Finset (Fin 10) := literalFinset [1, 2, 6, 7] (by decide +kernel)
noncomputable def vertices_794 : Finset (Fin 10) := literalFinset [1, 3, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_706 : Finset (Fin 10) := literalFinset [1, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_308 : Finset (Fin 10) := literalFinset [2, 4, 5, 8] (by decide +kernel)
noncomputable def vertices_468 : Finset (Fin 10) := literalFinset [2, 4, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_408 : Finset (Fin 10) := literalFinset [3, 4, 7, 8] (by decide +kernel)
noncomputable def vertices_137 : Finset (Fin 10) := literalFinset [0, 3, 7] (by decide +kernel)
noncomputable def vertices_265 : Finset (Fin 10) := literalFinset [0, 3, 8] (by decide +kernel)
noncomputable def vertices_521 : Finset (Fin 10) := literalFinset [0, 3, 9] (by decide +kernel)
noncomputable def vertices_97 : Finset (Fin 10) := literalFinset [0, 5, 6] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_545 : Finset (Fin 10) := literalFinset [0, 5, 9] (by decide +kernel)
noncomputable def vertices_193 : Finset (Fin 10) := literalFinset [0, 6, 7] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_22 : Finset (Fin 10) := literalFinset [1, 2, 4] (by decide +kernel)
noncomputable def vertices_550 : Finset (Fin 10) := literalFinset [1, 2, 5, 9] (by decide +kernel)
noncomputable def vertices_70 : Finset (Fin 10) := literalFinset [1, 2, 6] (by decide +kernel)
noncomputable def vertices_134 : Finset (Fin 10) := literalFinset [1, 2, 7] (by decide +kernel)
noncomputable def vertices_26 : Finset (Fin 10) := literalFinset [1, 3, 4] (by decide +kernel)
noncomputable def vertices_138 : Finset (Fin 10) := literalFinset [1, 3, 7] (by decide +kernel)
noncomputable def vertices_522 : Finset (Fin 10) := literalFinset [1, 3, 9] (by decide +kernel)
noncomputable def vertices_530 : Finset (Fin 10) := literalFinset [1, 4, 9] (by decide +kernel)
noncomputable def vertices_194 : Finset (Fin 10) := literalFinset [1, 6, 7] (by decide +kernel)
noncomputable def vertices_578 : Finset (Fin 10) := literalFinset [1, 6, 9] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_148 : Finset (Fin 10) := literalFinset [2, 4, 7] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_100 : Finset (Fin 10) := literalFinset [2, 5, 6] (by decide +kernel)
noncomputable def vertices_292 : Finset (Fin 10) := literalFinset [2, 5, 8] (by decide +kernel)
noncomputable def vertices_196 : Finset (Fin 10) := literalFinset [2, 6, 7] (by decide +kernel)
noncomputable def vertices_324 : Finset (Fin 10) := literalFinset [2, 6, 8] (by decide +kernel)
noncomputable def vertices_152 : Finset (Fin 10) := literalFinset [3, 4, 7] (by decide +kernel)
noncomputable def vertices_280 : Finset (Fin 10) := literalFinset [3, 4, 8] (by decide +kernel)
noncomputable def vertices_392 : Finset (Fin 10) := literalFinset [3, 7, 8] (by decide +kernel)
noncomputable def vertices_776 : Finset (Fin 10) := literalFinset [3, 8, 9] (by decide +kernel)
noncomputable def vertices_304 : Finset (Fin 10) := literalFinset [4, 5, 8] (by decide +kernel)
noncomputable def vertices_560 : Finset (Fin 10) := literalFinset [4, 5, 9] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_784 : Finset (Fin 10) := literalFinset [4, 8, 9] (by decide +kernel)
noncomputable def vertices_608 : Finset (Fin 10) := literalFinset [5, 6, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_357, vertices_457, vertices_777, vertices_817, vertices_737, vertices_158, vertices_566, vertices_614, vertices_198, vertices_794, vertices_706, vertices_308, vertices_468, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_97, vertices_289, vertices_545, vertices_193, vertices_321, vertices_641, vertices_769, vertices_22, vertices_550, vertices_70, vertices_134, vertices_26, vertices_138, vertices_522, vertices_530, vertices_194, vertices_578, vertices_642, vertices_52, vertices_148, vertices_276, vertices_100, vertices_292, vertices_196, vertices_324, vertices_152, vertices_280, vertices_392, vertices_776, vertices_304, vertices_560, vertices_400, vertices_784, vertices_608, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_357), (false, vertices_457), (false, vertices_777), (false, vertices_817), (false, vertices_737), (true, vertices_22), (true, vertices_550), (true, vertices_70), (true, vertices_134), (true, vertices_26), (true, vertices_530), (true, vertices_194), (true, vertices_578), (true, vertices_52), (true, vertices_148), (true, vertices_276), (true, vertices_196), (true, vertices_152), (true, vertices_280), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![15, 18, 20, 22, 24, 26, 27, 28, 29]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 16 else
  if p.val = (false, vertices_357) then 19 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (false, vertices_817) then 23 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_550) then 17 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_196) then 11 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_280) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_550), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 3
  frame := ![0, 1, 4]
  vertex := 8
  face := Sum.inr ⟨vertices_550, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_550, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 7]
  vertex := 8
  face := Sum.inl ⟨vertices_794, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_26, (by decide +kernel)⟩ ⟨vertices_794, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 2, 3]
  vertex := 6
  face := Sum.inl ⟨vertices_158, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_158, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 3, 5, 6]
  vertex := 7
  face := Sum.inl ⟨vertices_468, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_148, (by decide +kernel)⟩ ⟨vertices_468, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![4, 8, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_158, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 3] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_158, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_566, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 3, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_22, (by decide +kernel)⟩ ⟨vertices_566, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_614, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 1, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_550, (by decide +kernel)⟩ ⟨vertices_614, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_198, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 1, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_70, (by decide +kernel)⟩ ⟨vertices_198, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_794, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![0, 2, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_26, (by decide +kernel)⟩ ⟨vertices_794, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_706, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![0, 5, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_194, (by decide +kernel)⟩ ⟨vertices_706, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_308, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![1, 3, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_52, (by decide +kernel)⟩ ⟨vertices_308, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_468, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .oneRow ![1, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_148, (by decide +kernel)⟩ ⟨vertices_468, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet8 : boundary.facets := ⟨vertices_408, by decide +kernel⟩
noncomputable def cover8 : FacetCoverage heightProof coverFacet8 :=
  .fundamental ![2, 3, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_152, (by decide +kernel)⟩ ⟨vertices_408, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coveringFacets : Fin 9 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6, coverFacet7, coverFacet8]
noncomputable def coveringProof (j : Fin 9) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (Fin.cases cover7 (Fin.cases cover8 (fun i => Fin.elim0 i)))))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 9, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0299

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e10q1_0300.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0300

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_339 : Finset (Fin 10) := literalFinset [0, 1, 4, 6, 8] (by decide +kernel)
noncomputable def vertices_803 : Finset (Fin 10) := literalFinset [0, 1, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_707 : Finset (Fin 10) := literalFinset [0, 1, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_117 : Finset (Fin 10) := literalFinset [0, 2, 4, 5, 6] (by decide +kernel)
noncomputable def vertices_613 : Finset (Fin 10) := literalFinset [0, 2, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_313 : Finset (Fin 10) := literalFinset [0, 3, 4, 5, 8] (by decide +kernel)
noncomputable def vertices_654 : Finset (Fin 10) := literalFinset [1, 2, 3, 7, 9] (by decide +kernel)
noncomputable def vertices_394 : Finset (Fin 10) := literalFinset [1, 3, 7, 8] (by decide +kernel)
noncomputable def vertices_778 : Finset (Fin 10) := literalFinset [1, 3, 8, 9] (by decide +kernel)
noncomputable def vertices_450 : Finset (Fin 10) := literalFinset [1, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_60 : Finset (Fin 10) := literalFinset [2, 3, 4, 5] (by decide +kernel)
noncomputable def vertices_156 : Finset (Fin 10) := literalFinset [2, 3, 4, 7] (by decide +kernel)
noncomputable def vertices_812 : Finset (Fin 10) := literalFinset [2, 3, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_724 : Finset (Fin 10) := literalFinset [2, 4, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_472 : Finset (Fin 10) := literalFinset [3, 4, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_67 : Finset (Fin 10) := literalFinset [0, 1, 6] (by decide +kernel)
noncomputable def vertices_259 : Finset (Fin 10) := literalFinset [0, 1, 8] (by decide +kernel)
noncomputable def vertices_515 : Finset (Fin 10) := literalFinset [0, 1, 9] (by decide +kernel)
noncomputable def vertices_101 : Finset (Fin 10) := literalFinset [0, 2, 5, 6] (by decide +kernel)
noncomputable def vertices_49 : Finset (Fin 10) := literalFinset [0, 4, 5] (by decide +kernel)
noncomputable def vertices_81 : Finset (Fin 10) := literalFinset [0, 4, 6] (by decide +kernel)
noncomputable def vertices_273 : Finset (Fin 10) := literalFinset [0, 4, 8] (by decide +kernel)
noncomputable def vertices_289 : Finset (Fin 10) := literalFinset [0, 5, 8] (by decide +kernel)
noncomputable def vertices_545 : Finset (Fin 10) := literalFinset [0, 5, 9] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_138 : Finset (Fin 10) := literalFinset [1, 3, 7] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_522 : Finset (Fin 10) := literalFinset [1, 3, 9] (by decide +kernel)
noncomputable def vertices_194 : Finset (Fin 10) := literalFinset [1, 6, 7] (by decide +kernel)
noncomputable def vertices_322 : Finset (Fin 10) := literalFinset [1, 6, 8] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_28 : Finset (Fin 10) := literalFinset [2, 3, 4] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_140 : Finset (Fin 10) := literalFinset [2, 3, 7] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_52 : Finset (Fin 10) := literalFinset [2, 4, 5] (by decide +kernel)
noncomputable def vertices_84 : Finset (Fin 10) := literalFinset [2, 4, 6] (by decide +kernel)
noncomputable def vertices_148 : Finset (Fin 10) := literalFinset [2, 4, 7] (by decide +kernel)
noncomputable def vertices_548 : Finset (Fin 10) := literalFinset [2, 5, 9] (by decide +kernel)
noncomputable def vertices_580 : Finset (Fin 10) := literalFinset [2, 6, 9] (by decide +kernel)
noncomputable def vertices_644 : Finset (Fin 10) := literalFinset [2, 7, 9] (by decide +kernel)
noncomputable def vertices_56 : Finset (Fin 10) := literalFinset [3, 4, 5] (by decide +kernel)
noncomputable def vertices_152 : Finset (Fin 10) := literalFinset [3, 4, 7] (by decide +kernel)
noncomputable def vertices_280 : Finset (Fin 10) := literalFinset [3, 4, 8] (by decide +kernel)
noncomputable def vertices_296 : Finset (Fin 10) := literalFinset [3, 5, 8] (by decide +kernel)
noncomputable def vertices_392 : Finset (Fin 10) := literalFinset [3, 7, 8] (by decide +kernel)
noncomputable def vertices_776 : Finset (Fin 10) := literalFinset [3, 8, 9] (by decide +kernel)
noncomputable def vertices_208 : Finset (Fin 10) := literalFinset [4, 6, 7] (by decide +kernel)
noncomputable def vertices_336 : Finset (Fin 10) := literalFinset [4, 6, 8] (by decide +kernel)
noncomputable def vertices_800 : Finset (Fin 10) := literalFinset [5, 8, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_803, vertices_707, vertices_117, vertices_613, vertices_313, vertices_654, vertices_394, vertices_778, vertices_450, vertices_60, vertices_156, vertices_812, vertices_724, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_101, vertices_49, vertices_81, vertices_273, vertices_289, vertices_545, vertices_577, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_140, vertices_524, vertices_52, vertices_84, vertices_148, vertices_548, vertices_580, vertices_644, vertices_56, vertices_152, vertices_280, vertices_296, vertices_392, vertices_776, vertices_208, vertices_336, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_803), (false, vertices_707), (false, vertices_117), (false, vertices_613), (false, vertices_313), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_386), (true, vertices_28), (true, vertices_44), (true, vertices_140), (true, vertices_524), (true, vertices_148), (true, vertices_644), (true, vertices_152), (true, vertices_392), (true, vertices_776), (true, vertices_208), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![15, 19, 22, 24, 25, 26, 27, 28, 29]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 16 else
  if p.val = (false, vertices_803) then 17 else
  if p.val = (false, vertices_707) then 18 else
  if p.val = (false, vertices_117) then 20 else
  if p.val = (false, vertices_613) then 21 else
  if p.val = (false, vertices_313) then 23 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_44) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
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
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_138, (by decide +kernel)⟩ ⟨vertices_654, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
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
  frame := ![2, 3, 5, 6]
  vertex := 7
  face := Sum.inl ⟨vertices_472, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_152, (by decide +kernel)⟩ ⟨vertices_472, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 4, 1, 2]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_654, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_138, (by decide +kernel)⟩ ⟨vertices_654, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_394, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 2, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_138, (by decide +kernel)⟩ ⟨vertices_394, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_778, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 2, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_266, (by decide +kernel)⟩ ⟨vertices_778, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_450, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_194, (by decide +kernel)⟩ ⟨vertices_450, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_60, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![1, 2, 3, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_28, (by decide +kernel)⟩ ⟨vertices_60, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_156, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![1, 2, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_28, (by decide +kernel)⟩ ⟨vertices_156, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_812, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![1, 2, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_812, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_724, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .oneRow ![1, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_84, (by decide +kernel)⟩ ⟨vertices_724, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet8 : boundary.facets := ⟨vertices_472, by decide +kernel⟩
noncomputable def cover8 : FacetCoverage heightProof coverFacet8 :=
  .oneRow ![2, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_152, (by decide +kernel)⟩ ⟨vertices_472, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coveringFacets : Fin 9 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6, coverFacet7, coverFacet8]
noncomputable def coveringProof (j : Fin 9) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (Fin.cases cover7 (Fin.cases cover8 (fun i => Fin.elim0 i)))))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 9, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0300

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e10q1_0301.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0301

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_659 : Finset (Fin 10) := literalFinset [0, 1, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_333 : Finset (Fin 10) := literalFinset [0, 2, 3, 6, 8] (by decide +kernel)
noncomputable def vertices_789 : Finset (Fin 10) := literalFinset [0, 2, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_613 : Finset (Fin 10) := literalFinset [0, 2, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_465 : Finset (Fin 10) := literalFinset [0, 4, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_705 : Finset (Fin 10) := literalFinset [0, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_302 : Finset (Fin 10) := literalFinset [1, 2, 3, 5, 8] (by decide +kernel)
noncomputable def vertices_806 : Finset (Fin 10) := literalFinset [1, 2, 5, 8, 9] (by decide +kernel)
noncomputable def vertices_154 : Finset (Fin 10) := literalFinset [1, 3, 4, 7] (by decide +kernel)
noncomputable def vertices_794 : Finset (Fin 10) := literalFinset [1, 3, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_170 : Finset (Fin 10) := literalFinset [1, 3, 5, 7] (by decide +kernel)
noncomputable def vertices_738 : Finset (Fin 10) := literalFinset [1, 5, 6, 7, 9] (by decide +kernel)
noncomputable def vertices_236 : Finset (Fin 10) := literalFinset [2, 3, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_408 : Finset (Fin 10) := literalFinset [3, 4, 7, 8] (by decide +kernel)
noncomputable def vertices_456 : Finset (Fin 10) := literalFinset [3, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_69 : Finset (Fin 10) := literalFinset [0, 2, 6] (by decide +kernel)
noncomputable def vertices_261 : Finset (Fin 10) := literalFinset [0, 2, 8] (by decide +kernel)
noncomputable def vertices_517 : Finset (Fin 10) := literalFinset [0, 2, 9] (by decide +kernel)
noncomputable def vertices_145 : Finset (Fin 10) := literalFinset [0, 4, 7] (by decide +kernel)
noncomputable def vertices_273 : Finset (Fin 10) := literalFinset [0, 4, 8] (by decide +kernel)
noncomputable def vertices_529 : Finset (Fin 10) := literalFinset [0, 4, 9] (by decide +kernel)
noncomputable def vertices_193 : Finset (Fin 10) := literalFinset [0, 6, 7] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_577 : Finset (Fin 10) := literalFinset [0, 6, 9] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_294 : Finset (Fin 10) := literalFinset [1, 2, 5, 8] (by decide +kernel)
noncomputable def vertices_26 : Finset (Fin 10) := literalFinset [1, 3, 4] (by decide +kernel)
noncomputable def vertices_42 : Finset (Fin 10) := literalFinset [1, 3, 5] (by decide +kernel)
noncomputable def vertices_138 : Finset (Fin 10) := literalFinset [1, 3, 7] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_146 : Finset (Fin 10) := literalFinset [1, 4, 7] (by decide +kernel)
noncomputable def vertices_530 : Finset (Fin 10) := literalFinset [1, 4, 9] (by decide +kernel)
noncomputable def vertices_162 : Finset (Fin 10) := literalFinset [1, 5, 7] (by decide +kernel)
noncomputable def vertices_546 : Finset (Fin 10) := literalFinset [1, 5, 9] (by decide +kernel)
noncomputable def vertices_642 : Finset (Fin 10) := literalFinset [1, 7, 9] (by decide +kernel)
noncomputable def vertices_770 : Finset (Fin 10) := literalFinset [1, 8, 9] (by decide +kernel)
noncomputable def vertices_44 : Finset (Fin 10) := literalFinset [2, 3, 5] (by decide +kernel)
noncomputable def vertices_76 : Finset (Fin 10) := literalFinset [2, 3, 6] (by decide +kernel)
noncomputable def vertices_268 : Finset (Fin 10) := literalFinset [2, 3, 8] (by decide +kernel)
noncomputable def vertices_100 : Finset (Fin 10) := literalFinset [2, 5, 6] (by decide +kernel)
noncomputable def vertices_548 : Finset (Fin 10) := literalFinset [2, 5, 9] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_152 : Finset (Fin 10) := literalFinset [3, 4, 7] (by decide +kernel)
noncomputable def vertices_280 : Finset (Fin 10) := literalFinset [3, 4, 8] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_200 : Finset (Fin 10) := literalFinset [3, 6, 7] (by decide +kernel)
noncomputable def vertices_328 : Finset (Fin 10) := literalFinset [3, 6, 8] (by decide +kernel)
noncomputable def vertices_392 : Finset (Fin 10) := literalFinset [3, 7, 8] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_784 : Finset (Fin 10) := literalFinset [4, 8, 9] (by decide +kernel)
noncomputable def vertices_224 : Finset (Fin 10) := literalFinset [5, 6, 7] (by decide +kernel)
noncomputable def vertices_608 : Finset (Fin 10) := literalFinset [5, 6, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_704 : Finset (Fin 10) := literalFinset [6, 7, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_333, vertices_789, vertices_613, vertices_465, vertices_705, vertices_302, vertices_806, vertices_154, vertices_794, vertices_170, vertices_738, vertices_236, vertices_408, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_145, vertices_273, vertices_529, vertices_193, vertices_321, vertices_577, vertices_641, vertices_294, vertices_26, vertices_42, vertices_138, vertices_266, vertices_146, vertices_530, vertices_162, vertices_546, vertices_642, vertices_770, vertices_44, vertices_76, vertices_268, vertices_100, vertices_548, vertices_772, vertices_152, vertices_280, vertices_168, vertices_200, vertices_328, vertices_392, vertices_400, vertices_784, vertices_224, vertices_608, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_333), (false, vertices_789), (false, vertices_613), (false, vertices_465), (false, vertices_705), (true, vertices_294), (true, vertices_26), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_162), (true, vertices_546), (true, vertices_770), (true, vertices_44), (true, vertices_152), (true, vertices_280), (true, vertices_168), (true, vertices_200), (true, vertices_392), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![15, 18, 22, 23, 25, 26, 27, 28, 29]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 16 else
  if p.val = (false, vertices_333) then 19 else
  if p.val = (false, vertices_789) then 20 else
  if p.val = (false, vertices_613) then 21 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (false, vertices_705) then 0 else
  if p.val = (true, vertices_294) then 17 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_224) then 14 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_705), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_294), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
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
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_26, (by decide +kernel)⟩ ⟨vertices_794, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 3
  frame := ![0, 1, 4]
  vertex := 7
  face := Sum.inr ⟨vertices_294, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_294, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
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
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_162, (by decide +kernel)⟩ ⟨vertices_738, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 4, 5]
  vertex := 6
  face := Sum.inl ⟨vertices_236, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_236, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![3, 7, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_302, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_294, (by decide +kernel)⟩ ⟨vertices_302, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_806, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 4, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_294, (by decide +kernel)⟩ ⟨vertices_806, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_154, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 2, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_26, (by decide +kernel)⟩ ⟨vertices_154, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_794, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![0, 2, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_26, (by decide +kernel)⟩ ⟨vertices_794, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_170, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![0, 2, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_42, (by decide +kernel)⟩ ⟨vertices_170, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_738, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![0, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_162, (by decide +kernel)⟩ ⟨vertices_738, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_236, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![1, 2, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_44, (by decide +kernel)⟩ ⟨vertices_236, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_408, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![2, 3, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_152, (by decide +kernel)⟩ ⟨vertices_408, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet8 : boundary.facets := ⟨vertices_456, by decide +kernel⟩
noncomputable def cover8 : FacetCoverage heightProof coverFacet8 :=
  .fundamental ![2, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_200, (by decide +kernel)⟩ ⟨vertices_456, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coveringFacets : Fin 9 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6, coverFacet7, coverFacet8]
noncomputable def coveringProof (j : Fin 9) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (Fin.cases cover7 (Fin.cases cover8 (fun i => Fin.elim0 i)))))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 9, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0301

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e10q1_0302.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0302

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
noncomputable def vertices_227 : Finset (Fin 10) := literalFinset [0, 1, 5, 6, 7] (by decide +kernel)
noncomputable def vertices_789 : Finset (Fin 10) := literalFinset [0, 2, 4, 8, 9] (by decide +kernel)
noncomputable def vertices_681 : Finset (Fin 10) := literalFinset [0, 3, 5, 7, 9] (by decide +kernel)
noncomputable def vertices_465 : Finset (Fin 10) := literalFinset [0, 4, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_657 : Finset (Fin 10) := literalFinset [0, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_865 : Finset (Fin 10) := literalFinset [0, 5, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_286 : Finset (Fin 10) := literalFinset [1, 2, 3, 4, 8] (by decide +kernel)
noncomputable def vertices_110 : Finset (Fin 10) := literalFinset [1, 2, 3, 5, 6] (by decide +kernel)
noncomputable def vertices_838 : Finset (Fin 10) := literalFinset [1, 2, 6, 8, 9] (by decide +kernel)
noncomputable def vertices_170 : Finset (Fin 10) := literalFinset [1, 3, 5, 7] (by decide +kernel)
noncomputable def vertices_394 : Finset (Fin 10) := literalFinset [1, 3, 7, 8] (by decide +kernel)
noncomputable def vertices_450 : Finset (Fin 10) := literalFinset [1, 6, 7, 8] (by decide +kernel)
noncomputable def vertices_668 : Finset (Fin 10) := literalFinset [2, 3, 4, 7, 9] (by decide +kernel)
noncomputable def vertices_620 : Finset (Fin 10) := literalFinset [2, 3, 5, 6, 9] (by decide +kernel)
noncomputable def vertices_408 : Finset (Fin 10) := literalFinset [3, 4, 7, 8] (by decide +kernel)
noncomputable def vertices_145 : Finset (Fin 10) := literalFinset [0, 4, 7] (by decide +kernel)
noncomputable def vertices_273 : Finset (Fin 10) := literalFinset [0, 4, 8] (by decide +kernel)
noncomputable def vertices_529 : Finset (Fin 10) := literalFinset [0, 4, 9] (by decide +kernel)
noncomputable def vertices_97 : Finset (Fin 10) := literalFinset [0, 5, 6] (by decide +kernel)
noncomputable def vertices_161 : Finset (Fin 10) := literalFinset [0, 5, 7] (by decide +kernel)
noncomputable def vertices_545 : Finset (Fin 10) := literalFinset [0, 5, 9] (by decide +kernel)
noncomputable def vertices_193 : Finset (Fin 10) := literalFinset [0, 6, 7] (by decide +kernel)
noncomputable def vertices_321 : Finset (Fin 10) := literalFinset [0, 6, 8] (by decide +kernel)
noncomputable def vertices_641 : Finset (Fin 10) := literalFinset [0, 7, 9] (by decide +kernel)
noncomputable def vertices_769 : Finset (Fin 10) := literalFinset [0, 8, 9] (by decide +kernel)
noncomputable def vertices_14 : Finset (Fin 10) := literalFinset [1, 2, 3] (by decide +kernel)
noncomputable def vertices_70 : Finset (Fin 10) := literalFinset [1, 2, 6] (by decide +kernel)
noncomputable def vertices_262 : Finset (Fin 10) := literalFinset [1, 2, 8] (by decide +kernel)
noncomputable def vertices_42 : Finset (Fin 10) := literalFinset [1, 3, 5] (by decide +kernel)
noncomputable def vertices_138 : Finset (Fin 10) := literalFinset [1, 3, 7] (by decide +kernel)
noncomputable def vertices_266 : Finset (Fin 10) := literalFinset [1, 3, 8] (by decide +kernel)
noncomputable def vertices_98 : Finset (Fin 10) := literalFinset [1, 5, 6] (by decide +kernel)
noncomputable def vertices_162 : Finset (Fin 10) := literalFinset [1, 5, 7] (by decide +kernel)
noncomputable def vertices_194 : Finset (Fin 10) := literalFinset [1, 6, 7] (by decide +kernel)
noncomputable def vertices_322 : Finset (Fin 10) := literalFinset [1, 6, 8] (by decide +kernel)
noncomputable def vertices_386 : Finset (Fin 10) := literalFinset [1, 7, 8] (by decide +kernel)
noncomputable def vertices_28 : Finset (Fin 10) := literalFinset [2, 3, 4] (by decide +kernel)
noncomputable def vertices_108 : Finset (Fin 10) := literalFinset [2, 3, 5, 6] (by decide +kernel)
noncomputable def vertices_524 : Finset (Fin 10) := literalFinset [2, 3, 9] (by decide +kernel)
noncomputable def vertices_276 : Finset (Fin 10) := literalFinset [2, 4, 8] (by decide +kernel)
noncomputable def vertices_532 : Finset (Fin 10) := literalFinset [2, 4, 9] (by decide +kernel)
noncomputable def vertices_580 : Finset (Fin 10) := literalFinset [2, 6, 9] (by decide +kernel)
noncomputable def vertices_772 : Finset (Fin 10) := literalFinset [2, 8, 9] (by decide +kernel)
noncomputable def vertices_152 : Finset (Fin 10) := literalFinset [3, 4, 7] (by decide +kernel)
noncomputable def vertices_280 : Finset (Fin 10) := literalFinset [3, 4, 8] (by decide +kernel)
noncomputable def vertices_168 : Finset (Fin 10) := literalFinset [3, 5, 7] (by decide +kernel)
noncomputable def vertices_552 : Finset (Fin 10) := literalFinset [3, 5, 9] (by decide +kernel)
noncomputable def vertices_392 : Finset (Fin 10) := literalFinset [3, 7, 8] (by decide +kernel)
noncomputable def vertices_648 : Finset (Fin 10) := literalFinset [3, 7, 9] (by decide +kernel)
noncomputable def vertices_400 : Finset (Fin 10) := literalFinset [4, 7, 8] (by decide +kernel)
noncomputable def vertices_656 : Finset (Fin 10) := literalFinset [4, 7, 9] (by decide +kernel)
noncomputable def vertices_608 : Finset (Fin 10) := literalFinset [5, 6, 9] (by decide +kernel)
noncomputable def vertices_448 : Finset (Fin 10) := literalFinset [6, 7, 8] (by decide +kernel)
noncomputable def vertices_832 : Finset (Fin 10) := literalFinset [6, 8, 9] (by decide +kernel)

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_227, vertices_789, vertices_681, vertices_465, vertices_657, vertices_865, vertices_286, vertices_110, vertices_838, vertices_170, vertices_394, vertices_450, vertices_668, vertices_620, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_145, vertices_273, vertices_529, vertices_97, vertices_161, vertices_545, vertices_193, vertices_321, vertices_641, vertices_769, vertices_14, vertices_70, vertices_262, vertices_42, vertices_138, vertices_266, vertices_98, vertices_162, vertices_194, vertices_322, vertices_386, vertices_28, vertices_108, vertices_524, vertices_276, vertices_532, vertices_580, vertices_772, vertices_152, vertices_280, vertices_168, vertices_552, vertices_392, vertices_648, vertices_400, vertices_656, vertices_608, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_227), (false, vertices_789), (false, vertices_681), (false, vertices_465), (false, vertices_657), (false, vertices_865), (true, vertices_14), (true, vertices_70), (true, vertices_262), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_322), (true, vertices_386), (true, vertices_28), (true, vertices_108), (true, vertices_524), (true, vertices_580), (true, vertices_152), (true, vertices_280), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

noncomputable def pointPriority : Fin 9 → ℕ := ![15, 17, 20, 22, 24, 26, 27, 28, 29]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_227) then 16 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (false, vertices_657) then 0 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_108) then 19 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_280) then 13 else
  if p.val = (true, vertices_392) then 14 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_657), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_108), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

theorem priority_injective : Function.Injective priority :=
  Function.LeftInverse.injective (show Function.LeftInverse nodeAtPriority priority from by decide +kernel)

noncomputable def incidenceProof : IncidenceCertificate boundary :=
  incidenceCertificateOfChecks boundary priority priority_injective (by decide +kernel) (by decide +kernel)

noncomputable def row0 : HeightRow boundary where
  frameSize := 3
  frame := ![1, 2, 4]
  vertex := 5
  face := Sum.inr ⟨vertices_108, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) ⟨vertices_108, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel)
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
  frame := ![0, 1, 2, 3]
  vertex := 7
  face := Sum.inl ⟨vertices_286, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_286, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 3, 6]
  vertex := 8
  face := Sum.inl ⟨vertices_668, by decide +kernel⟩
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_28, (by decide +kernel)⟩ ⟨vertices_668, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![4, 5, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := ⟨vertices_286, by decide +kernel⟩
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 3] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_286, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := ⟨vertices_110, by decide +kernel⟩
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 2, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_14, (by decide +kernel)⟩ ⟨vertices_110, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := ⟨vertices_838, by decide +kernel⟩
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 1, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_70, (by decide +kernel)⟩ ⟨vertices_838, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := ⟨vertices_170, by decide +kernel⟩
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 2, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_42, (by decide +kernel)⟩ ⟨vertices_170, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := ⟨vertices_394, by decide +kernel⟩
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![0, 2, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_138, (by decide +kernel)⟩ ⟨vertices_394, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := ⟨vertices_450, by decide +kernel⟩
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![0, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_194, (by decide +kernel)⟩ ⟨vertices_450, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := ⟨vertices_668, by decide +kernel⟩
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![1, 2, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_28, (by decide +kernel)⟩ ⟨vertices_668, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := ⟨vertices_620, by decide +kernel⟩
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .oneRow ![1, 2, 4, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_108, (by decide +kernel)⟩ ⟨vertices_620, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet8 : boundary.facets := ⟨vertices_408, by decide +kernel⟩
noncomputable def cover8 : FacetCoverage heightProof coverFacet8 :=
  .fundamental ![2, 3, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) ⟨vertices_152, (by decide +kernel)⟩ ⟨vertices_408, (by decide +kernel)⟩ (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coveringFacets : Fin 9 → boundary.facets := ![coverFacet0, coverFacet1, coverFacet2, coverFacet3, coverFacet4, coverFacet5, coverFacet6, coverFacet7, coverFacet8]
noncomputable def coveringProof (j : Fin 9) : FacetCoverage heightProof (coveringFacets j) :=
  (Fin.cases (motive := fun j => FacetCoverage heightProof (coveringFacets j)) cover0 (Fin.cases cover1 (Fin.cases cover2 (Fin.cases cover3 (Fin.cases cover4 (Fin.cases cover5 (Fin.cases cover6 (Fin.cases cover7 (Fin.cases cover8 (fun i => Fin.elim0 i)))))))))) j

noncomputable def certificate : ReconstructionCertificate boundary 4 where
  incidence := incidenceProof
  heights := heightProof
  facet F := by
    have hall : ∀ F : {F : boundary.facets // 0 ∉ F.val}, ∃ j : Fin 9, coveringFacets j = F.val := by decide +kernel
    let j := (hall F).choose
    exact (hall F).choose_spec ▸ coveringProof j

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0302

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_2883 : Certifies 2883 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0273.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2884 : Certifies 2884 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0274.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2885 : Certifies 2885 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0275.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2886 : Certifies 2886 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0276.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2887 : Certifies 2887 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0277.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2888 : Certifies 2888 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0278.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2889 : Certifies 2889 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0279.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2890 : Certifies 2890 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0280.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2891 : Certifies 2891 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0281.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2892 : Certifies 2892 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0282.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2893 : Certifies 2893 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0283.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2894 : Certifies 2894 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0284.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2895 : Certifies 2895 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0285.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2896 : Certifies 2896 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0286.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2897 : Certifies 2897 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0287.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2898 : Certifies 2898 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0288.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2899 : Certifies 2899 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0289.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2900 : Certifies 2900 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0290.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2901 : Certifies 2901 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0291.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2902 : Certifies 2902 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0292.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2903 : Certifies 2903 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0293.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2904 : Certifies 2904 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0294.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2905 : Certifies 2905 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0295.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2906 : Certifies 2906 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0296.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2907 : Certifies 2907 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0297.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2908 : Certifies 2908 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0298.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2909 : Certifies 2909 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0299.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2910 : Certifies 2910 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0300.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2911 : Certifies 2911 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0301.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2912 : Certifies 2912 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0302.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B095 (j : Fin 30) :
    Certifies (2883 + j.val) := by
  fin_cases j
  · exact projection_2883
  · exact projection_2884
  · exact projection_2885
  · exact projection_2886
  · exact projection_2887
  · exact projection_2888
  · exact projection_2889
  · exact projection_2890
  · exact projection_2891
  · exact projection_2892
  · exact projection_2893
  · exact projection_2894
  · exact projection_2895
  · exact projection_2896
  · exact projection_2897
  · exact projection_2898
  · exact projection_2899
  · exact projection_2900
  · exact projection_2901
  · exact projection_2902
  · exact projection_2903
  · exact projection_2904
  · exact projection_2905
  · exact projection_2906
  · exact projection_2907
  · exact projection_2908
  · exact projection_2909
  · exact projection_2910
  · exact projection_2911
  · exact projection_2912

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
