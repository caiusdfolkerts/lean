module
public import SharedProjectionVertexSets
public import TerminalGeometry
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Papers.FiniteProjectionChecks

section
set_option debug.skipKernelTC false


section BundlePart0
/- Source: ProjectionCertificates/R_m14e10q1_0388.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0388
open _root_.Nonrational.SharedProjectionVertexSets

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_341, vertices_405, vertices_613, vertices_681, vertices_241, vertices_398, vertices_838, vertices_810, vertices_650, vertices_184, vertices_312, vertices_408, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_277, vertices_69, vertices_133, vertices_517, vertices_81, vertices_145, vertices_97, vertices_161, vertices_545, vertices_641, vertices_134, vertices_262, vertices_518, vertices_138, vertices_266, vertices_522, vertices_642, vertices_770, vertices_324, vertices_580, vertices_388, vertices_56, vertices_152, vertices_280, vertices_168, vertices_296, vertices_552, vertices_392, vertices_648, vertices_112, vertices_176, vertices_304, vertices_336, vertices_400, vertices_608, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_341), (false, vertices_405), (false, vertices_613), (false, vertices_681), (false, vertices_241), (true, vertices_262), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_770), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_296), (true, vertices_392), (true, vertices_304), (true, vertices_800), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

private noncomputable def indexedFacet (j : Fin 14) : boundary.facets := by
  let xs : List (Finset (Fin 10)) := [vertices_647, vertices_341, vertices_405, vertices_613, vertices_681, vertices_241, vertices_398, vertices_838, vertices_810, vertices_650, vertices_184, vertices_312, vertices_408, vertices_880]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

private noncomputable def indexedPolygon (j : Fin 37) : boundary.polygons := by
  let xs : List (Finset (Fin 10)) := [vertices_277, vertices_69, vertices_133, vertices_517, vertices_81, vertices_145, vertices_97, vertices_161, vertices_545, vertices_641, vertices_134, vertices_262, vertices_518, vertices_138, vertices_266, vertices_522, vertices_642, vertices_770, vertices_324, vertices_580, vertices_388, vertices_56, vertices_152, vertices_280, vertices_168, vertices_296, vertices_552, vertices_392, vertices_648, vertices_112, vertices_176, vertices_304, vertices_336, vertices_400, vertices_608, vertices_800, vertices_832]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 15, 19, 21, 23, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 14 else
  if p.val = (false, vertices_341) then 16 else
  if p.val = (false, vertices_405) then 17 else
  if p.val = (false, vertices_613) then 18 else
  if p.val = (false, vertices_681) then 20 else
  if p.val = (false, vertices_241) then 22 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_56) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_800) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
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
  vertex := 7
  face := Sum.inl (indexedFacet 6)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 10) (indexedFacet 6) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 5, 7]
  vertex := 8
  face := Sum.inl (indexedFacet 7)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 11) (indexedFacet 7) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 4, 7]
  vertex := 8
  face := Sum.inl (indexedFacet 8)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 14) (indexedFacet 8) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![3, 4, 5, 7]
  vertex := 8
  face := Sum.inl (indexedFacet 13)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 29) (indexedFacet 13) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![6, 1, 0, 3]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := (indexedFacet 6)
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 10) (indexedFacet 6) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := (indexedFacet 7)
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 11) (indexedFacet 7) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := (indexedFacet 8)
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 2, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 14) (indexedFacet 8) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := (indexedFacet 9)
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 2, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 13) (indexedFacet 9) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := (indexedFacet 10)
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![2, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 21) (indexedFacet 10) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := (indexedFacet 11)
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![2, 3, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 21) (indexedFacet 11) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := (indexedFacet 12)
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![2, 3, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 22) (indexedFacet 12) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := (indexedFacet 13)
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .oneRow ![3, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 29) (indexedFacet 13) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0388

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m14e10q1_0392.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0392
open _root_.Nonrational.SharedProjectionVertexSets

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_775, vertices_661, vertices_229, vertices_793, vertices_465, vertices_582, vertices_810, vertices_482, vertices_610, vertices_684, vertices_612, vertices_440, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_263, vertices_69, vertices_133, vertices_517, vertices_145, vertices_273, vertices_529, vertices_193, vertices_321, vertices_769, vertices_70, vertices_518, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_100, vertices_164, vertices_548, vertices_580, vertices_644, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_552, vertices_648, vertices_776, vertices_400, vertices_656, vertices_224, vertices_608, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_775), (false, vertices_661), (false, vertices_229), (false, vertices_793), (false, vertices_465), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_578), (true, vertices_548), (true, vertices_580), (true, vertices_152), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_648), (true, vertices_608), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

private noncomputable def indexedFacet (j : Fin 14) : boundary.facets := by
  let xs : List (Finset (Fin 10)) := [vertices_327, vertices_775, vertices_661, vertices_229, vertices_793, vertices_465, vertices_582, vertices_810, vertices_482, vertices_610, vertices_684, vertices_612, vertices_440, vertices_664]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

private noncomputable def indexedPolygon (j : Fin 37) : boundary.polygons := by
  let xs : List (Finset (Fin 10)) := [vertices_263, vertices_69, vertices_133, vertices_517, vertices_145, vertices_273, vertices_529, vertices_193, vertices_321, vertices_769, vertices_70, vertices_518, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_100, vertices_164, vertices_548, vertices_580, vertices_644, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_552, vertices_648, vertices_776, vertices_400, vertices_656, vertices_224, vertices_608, vertices_416, vertices_448]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 16, 19, 21, 23, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 14 else
  if p.val = (false, vertices_775) then 15 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_229) then 18 else
  if p.val = (false, vertices_793) then 20 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (true, vertices_98) then 0 else
  if p.val = (true, vertices_290) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_580) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_608) then 11 else
  if p.val = (true, vertices_416) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
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
  frame := ![0, 4, 5, 6]
  vertex := 7
  face := Sum.inl (indexedFacet 8)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 12) (indexedFacet 8) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 4, 7]
  vertex := 8
  face := Sum.inl (indexedFacet 7)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 13) (indexedFacet 7) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 4, 6]
  vertex := 8
  face := Sum.inl (indexedFacet 10)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 19) (indexedFacet 10) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![2, 3, 4, 6]
  vertex := 7
  face := Sum.inl (indexedFacet 12)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 23) (indexedFacet 12) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![5, 0, 1, 2]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := (indexedFacet 6)
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .fundamental ![0, 1, 5, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 10) (indexedFacet 6) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := (indexedFacet 7)
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 2, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 13) (indexedFacet 7) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := (indexedFacet 8)
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 12) (indexedFacet 8) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := (indexedFacet 9)
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 4, 5, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 12) (indexedFacet 9) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := (indexedFacet 10)
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![1, 2, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 19) (indexedFacet 10) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := (indexedFacet 11)
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![1, 4, 5, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 18) (indexedFacet 11) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := (indexedFacet 12)
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![2, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 23) (indexedFacet 12) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := (indexedFacet 13)
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![2, 3, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 23) (indexedFacet 13) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0392

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m14e10q1_0394.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0394
open _root_.Nonrational.SharedProjectionVertexSets

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_301, vertices_557, vertices_601, vertices_457, vertices_369, vertices_678, vertices_714, vertices_178, vertices_210, vertices_594, vertices_908, vertices_436, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_45, vertices_73, vertices_265, vertices_521, vertices_49, vertices_81, vertices_529, vertices_289, vertices_545, vertices_321, vertices_50, vertices_82, vertices_146, vertices_530, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_268, vertices_524, vertices_164, vertices_292, vertices_548, vertices_388, vertices_644, vertices_200, vertices_584, vertices_392, vertices_648, vertices_176, vertices_304, vertices_208, vertices_336, vertices_592, vertices_400, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_301), (false, vertices_557), (false, vertices_601), (false, vertices_457), (false, vertices_369), (true, vertices_82), (true, vertices_146), (true, vertices_162), (true, vertices_194), (true, vertices_578), (true, vertices_642), (true, vertices_164), (true, vertices_388), (true, vertices_644), (true, vertices_648), (true, vertices_176), (true, vertices_208), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

private noncomputable def indexedFacet (j : Fin 14) : boundary.facets := by
  let xs : List (Finset (Fin 10)) := [vertices_563, vertices_301, vertices_557, vertices_601, vertices_457, vertices_369, vertices_678, vertices_714, vertices_178, vertices_210, vertices_594, vertices_908, vertices_436, vertices_464]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

private noncomputable def indexedPolygon (j : Fin 37) : boundary.polygons := by
  let xs : List (Finset (Fin 10)) := [vertices_45, vertices_73, vertices_265, vertices_521, vertices_49, vertices_81, vertices_529, vertices_289, vertices_545, vertices_321, vertices_50, vertices_82, vertices_146, vertices_530, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_268, vertices_524, vertices_164, vertices_292, vertices_548, vertices_388, vertices_644, vertices_200, vertices_584, vertices_392, vertices_648, vertices_176, vertices_304, vertices_208, vertices_336, vertices_592, vertices_400, vertices_448]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 15, 18, 21, 23, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 14 else
  if p.val = (false, vertices_301) then 16 else
  if p.val = (false, vertices_557) then 17 else
  if p.val = (false, vertices_601) then 19 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (false, vertices_369) then 22 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_648) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_400) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
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
  frame := ![0, 2, 5, 6]
  vertex := 8
  face := Sum.inl (indexedFacet 7)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 16) (indexedFacet 7) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 4, 6]
  vertex := 8
  face := Sum.inl (indexedFacet 6)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 14) (indexedFacet 6) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 6, 7]
  vertex := 8
  face := Sum.inl (indexedFacet 11)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 19) (indexedFacet 11) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 3, 4, 6]
  vertex := 7
  face := Sum.inl (indexedFacet 12)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 21) (indexedFacet 12) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![5, 0, 2, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := (indexedFacet 6)
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 14) (indexedFacet 6) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := (indexedFacet 7)
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 2, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 16) (indexedFacet 7) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := (indexedFacet 8)
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 10) (indexedFacet 8) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := (indexedFacet 9)
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 11) (indexedFacet 9) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := (indexedFacet 10)
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![0, 3, 5, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 11) (indexedFacet 10) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := (indexedFacet 11)
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![1, 2, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 19) (indexedFacet 11) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := (indexedFacet 12)
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![1, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 21) (indexedFacet 12) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := (indexedFacet 13)
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![3, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 32) (indexedFacet 13) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0394

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m14e10q1_0395.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0395
open _root_.Nonrational.SharedProjectionVertexSets

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_107, vertices_299, vertices_403, vertices_707, vertices_901, vertices_841, vertices_310, vertices_114, vertices_210, vertices_812, vertices_692, vertices_404, vertices_632, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_43, vertices_67, vertices_131, vertices_259, vertices_73, vertices_265, vertices_577, vertices_385, vertices_641, vertices_769, vertices_50, vertices_82, vertices_146, vertices_274, vertices_98, vertices_290, vertices_194, vertices_52, vertices_148, vertices_276, vertices_292, vertices_548, vertices_388, vertices_644, vertices_772, vertices_104, vertices_296, vertices_552, vertices_584, vertices_776, vertices_112, vertices_560, vertices_208, vertices_592, vertices_400, vertices_656, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_107), (false, vertices_299), (false, vertices_403), (false, vertices_707), (false, vertices_901), (false, vertices_841), (true, vertices_50), (true, vertices_82), (true, vertices_52), (true, vertices_148), (true, vertices_276), (true, vertices_292), (true, vertices_548), (true, vertices_552), (true, vertices_112), (true, vertices_560), (true, vertices_208), (true, vertices_592), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

private noncomputable def indexedFacet (j : Fin 14) : boundary.facets := by
  let xs : List (Finset (Fin 10)) := [vertices_107, vertices_299, vertices_403, vertices_707, vertices_901, vertices_841, vertices_310, vertices_114, vertices_210, vertices_812, vertices_692, vertices_404, vertices_632, vertices_720]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

private noncomputable def indexedPolygon (j : Fin 37) : boundary.polygons := by
  let xs : List (Finset (Fin 10)) := [vertices_43, vertices_67, vertices_131, vertices_259, vertices_73, vertices_265, vertices_577, vertices_385, vertices_641, vertices_769, vertices_50, vertices_82, vertices_146, vertices_274, vertices_98, vertices_290, vertices_194, vertices_52, vertices_148, vertices_276, vertices_292, vertices_548, vertices_388, vertices_644, vertices_772, vertices_104, vertices_296, vertices_552, vertices_584, vertices_776, vertices_112, vertices_560, vertices_208, vertices_592, vertices_400, vertices_656, vertices_704]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

noncomputable def pointPriority : Fin 9 → ℕ := ![19, 13, 15, 22, 23, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_107) then 16 else
  if p.val = (false, vertices_299) then 17 else
  if p.val = (false, vertices_403) then 20 else
  if p.val = (false, vertices_707) then 21 else
  if p.val = (false, vertices_901) then 14 else
  if p.val = (false, vertices_841) then 18 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_52) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_276) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_656) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_107), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
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
  frame := ![0, 1, 3, 4]
  vertex := 7
  face := Sum.inl (indexedFacet 6)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 10) (indexedFacet 6) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 4, 7]
  vertex := 8
  face := Sum.inl (indexedFacet 9)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 20) (indexedFacet 9) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 3, 4, 6]
  vertex := 8
  face := Sum.inl (indexedFacet 10)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 17) (indexedFacet 10) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![2, 3, 4, 5]
  vertex := 8
  face := Sum.inl (indexedFacet 12)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 25) (indexedFacet 12) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 7, 1, 2]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := (indexedFacet 6)
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 3, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 10) (indexedFacet 6) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := (indexedFacet 7)
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 10) (indexedFacet 7) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := (indexedFacet 8)
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 11) (indexedFacet 8) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := (indexedFacet 9)
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 2, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 20) (indexedFacet 9) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := (indexedFacet 10)
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![1, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 17) (indexedFacet 10) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := (indexedFacet 11)
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![1, 3, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 18) (indexedFacet 11) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := (indexedFacet 12)
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![2, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 25) (indexedFacet 12) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := (indexedFacet 13)
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![3, 5, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 32) (indexedFacet 13) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0395

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m14e10q1_0396.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0396
open _root_.Nonrational.SharedProjectionVertexSets

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_405, vertices_677, vertices_293, vertices_713, vertices_625, vertices_209, vertices_806, vertices_218, vertices_410, vertices_842, vertices_562, vertices_594, vertices_908] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_49, vertices_81, vertices_145, vertices_273, vertices_289, vertices_545, vertices_193, vertices_577, vertices_641, vertices_154, vertices_74, vertices_266, vertices_50, vertices_82, vertices_274, vertices_530, vertices_290, vertices_546, vertices_578, vertices_770, vertices_292, vertices_548, vertices_388, vertices_644, vertices_772, vertices_200, vertices_584, vertices_392, vertices_648, vertices_776, vertices_560, vertices_208, vertices_592, vertices_400] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_405), (false, vertices_677), (false, vertices_293), (false, vertices_713), (false, vertices_625), (false, vertices_209), (true, vertices_154), (true, vertices_74), (true, vertices_266), (true, vertices_82), (true, vertices_530), (true, vertices_546), (true, vertices_578), (true, vertices_770), (true, vertices_772), (true, vertices_392), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

private noncomputable def indexedFacet (j : Fin 14) : boundary.facets := by
  let xs : List (Finset (Fin 10)) := [vertices_307, vertices_405, vertices_677, vertices_293, vertices_713, vertices_625, vertices_209, vertices_806, vertices_218, vertices_410, vertices_842, vertices_562, vertices_594, vertices_908]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

private noncomputable def indexedPolygon (j : Fin 37) : boundary.polygons := by
  let xs : List (Finset (Fin 10)) := [vertices_37, vertices_133, vertices_261, vertices_49, vertices_81, vertices_145, vertices_273, vertices_289, vertices_545, vertices_193, vertices_577, vertices_641, vertices_154, vertices_74, vertices_266, vertices_50, vertices_82, vertices_274, vertices_530, vertices_290, vertices_546, vertices_578, vertices_770, vertices_292, vertices_548, vertices_388, vertices_644, vertices_772, vertices_200, vertices_584, vertices_392, vertices_648, vertices_776, vertices_560, vertices_208, vertices_592, vertices_400]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

noncomputable def pointPriority : Fin 9 → ℕ := ![12, 15, 18, 20, 22, 23, 24, 25, 26]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 13 else
  if p.val = (false, vertices_405) then 16 else
  if p.val = (false, vertices_677) then 17 else
  if p.val = (false, vertices_293) then 0 else
  if p.val = (false, vertices_713) then 19 else
  if p.val = (false, vertices_625) then 21 else
  if p.val = (false, vertices_209) then 1 else
  if p.val = (true, vertices_154) then 14 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_776) then 11 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_209), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_154), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
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
  frame := ![0, 2, 3]
  vertex := 6
  face := Sum.inr (indexedPolygon 12)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) (indexedPolygon 12) (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 4, 7]
  vertex := 8
  face := Sum.inl (indexedFacet 7)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 19) (indexedFacet 7) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 5, 7]
  vertex := 8
  face := Sum.inl (indexedFacet 10)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 13) (indexedFacet 10) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 6, 7]
  vertex := 8
  face := Sum.inl (indexedFacet 13)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 25) (indexedFacet 13) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![3, 4, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := (indexedFacet 7)
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 19) (indexedFacet 7) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := (indexedFacet 8)
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 12) (indexedFacet 8) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := (indexedFacet 9)
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 2, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 12) (indexedFacet 9) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := (indexedFacet 10)
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![0, 2, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 13) (indexedFacet 10) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := (indexedFacet 11)
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![0, 3, 4, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 15) (indexedFacet 11) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := (indexedFacet 12)
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![0, 3, 5, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 16) (indexedFacet 12) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := (indexedFacet 13)
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![1, 2, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 25) (indexedFacet 13) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0396

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m14e10q1_0397.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0397
open _root_.Nonrational.SharedProjectionVertexSets

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_357, vertices_165, vertices_709, vertices_809, vertices_689, vertices_94, vertices_334, vertices_570, vertices_778, vertices_722, vertices_316, vertices_180, vertices_212] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_133, vertices_161, vertices_289, vertices_545, vertices_321, vertices_577, vertices_641, vertices_769, vertices_78, vertices_26, vertices_266, vertices_522, vertices_82, vertices_530, vertices_322, vertices_578, vertices_770, vertices_28, vertices_268, vertices_52, vertices_84, vertices_148, vertices_164, vertices_292, vertices_196, vertices_324, vertices_56, vertices_296, vertices_552, vertices_776, vertices_176, vertices_560, vertices_208, vertices_656, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_357), (false, vertices_165), (false, vertices_709), (false, vertices_809), (false, vertices_689), (true, vertices_78), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_82), (true, vertices_530), (true, vertices_28), (true, vertices_268), (true, vertices_52), (true, vertices_84), (true, vertices_148), (true, vertices_56), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

private noncomputable def indexedFacet (j : Fin 14) : boundary.facets := by
  let xs : List (Finset (Fin 10)) := [vertices_835, vertices_357, vertices_165, vertices_709, vertices_809, vertices_689, vertices_94, vertices_334, vertices_570, vertices_778, vertices_722, vertices_316, vertices_180, vertices_212]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

private noncomputable def indexedPolygon (j : Fin 37) : boundary.polygons := by
  let xs : List (Finset (Fin 10)) := [vertices_37, vertices_69, vertices_133, vertices_161, vertices_289, vertices_545, vertices_321, vertices_577, vertices_641, vertices_769, vertices_78, vertices_26, vertices_266, vertices_522, vertices_82, vertices_530, vertices_322, vertices_578, vertices_770, vertices_28, vertices_268, vertices_52, vertices_84, vertices_148, vertices_164, vertices_292, vertices_196, vertices_324, vertices_56, vertices_296, vertices_552, vertices_776, vertices_176, vertices_560, vertices_208, vertices_656, vertices_704]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 16, 19, 21, 23, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 14 else
  if p.val = (false, vertices_357) then 17 else
  if p.val = (false, vertices_165) then 0 else
  if p.val = (false, vertices_709) then 18 else
  if p.val = (false, vertices_809) then 20 else
  if p.val = (false, vertices_689) then 22 else
  if p.val = (true, vertices_78) then 15 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_208) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_165), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_78), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
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
  frame := ![0, 3, 5, 6]
  vertex := 8
  face := Sum.inl (indexedFacet 10)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 14) (indexedFacet 10) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 3
  frame := ![0, 1, 2]
  vertex := 5
  face := Sum.inr (indexedPolygon 10)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) (indexedPolygon 10) (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 4]
  vertex := 8
  face := Sum.inl (indexedFacet 8)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 11) (indexedFacet 8) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 3, 4]
  vertex := 7
  face := Sum.inl (indexedFacet 11)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 19) (indexedFacet 11) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![6, 5, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := (indexedFacet 6)
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 3] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 10) (indexedFacet 6) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := (indexedFacet 7)
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 2, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 10) (indexedFacet 7) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := (indexedFacet 8)
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 2, 3, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 11) (indexedFacet 8) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := (indexedFacet 9)
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 2, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 12) (indexedFacet 9) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := (indexedFacet 10)
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![0, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 14) (indexedFacet 10) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := (indexedFacet 11)
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![1, 2, 3, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 19) (indexedFacet 11) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := (indexedFacet 12)
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![1, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 21) (indexedFacet 12) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := (indexedFacet 13)
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![1, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 22) (indexedFacet 13) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0397

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m14e10q1_0398.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0398
open _root_.Nonrational.SharedProjectionVertexSets

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_213, vertices_793, vertices_713, vertices_625, vertices_401, vertices_422, vertices_234, vertices_618, vertices_778, vertices_818, vertices_372, vertices_404, vertices_228] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_81, vertices_145, vertices_273, vertices_529, vertices_193, vertices_577, vertices_385, vertices_106, vertices_138, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_386, vertices_770, vertices_84, vertices_148, vertices_276, vertices_100, vertices_164, vertices_292, vertices_196, vertices_388, vertices_200, vertices_584, vertices_776, vertices_112, vertices_304, vertices_560, vertices_400, vertices_784, vertices_224, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_213), (false, vertices_793), (false, vertices_713), (false, vertices_625), (false, vertices_401), (true, vertices_106), (true, vertices_522), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_276), (true, vertices_100), (true, vertices_164), (true, vertices_292), (true, vertices_388), (true, vertices_304), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

private noncomputable def indexedFacet (j : Fin 14) : boundary.facets := by
  let xs : List (Finset (Fin 10)) := [vertices_395, vertices_213, vertices_793, vertices_713, vertices_625, vertices_401, vertices_422, vertices_234, vertices_618, vertices_778, vertices_818, vertices_372, vertices_404, vertices_228]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

private noncomputable def indexedPolygon (j : Fin 37) : boundary.polygons := by
  let xs : List (Finset (Fin 10)) := [vertices_137, vertices_265, vertices_521, vertices_81, vertices_145, vertices_273, vertices_529, vertices_193, vertices_577, vertices_385, vertices_106, vertices_138, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_386, vertices_770, vertices_84, vertices_148, vertices_276, vertices_100, vertices_164, vertices_292, vertices_196, vertices_388, vertices_200, vertices_584, vertices_776, vertices_112, vertices_304, vertices_560, vertices_400, vertices_784, vertices_224, vertices_608]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 16, 18, 21, 23, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 14 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_793) then 19 else
  if p.val = (false, vertices_713) then 20 else
  if p.val = (false, vertices_625) then 22 else
  if p.val = (false, vertices_401) then 0 else
  if p.val = (true, vertices_106) then 15 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_224) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_401), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_106), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
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
  frameSize := 3
  frame := ![0, 2, 4]
  vertex := 5
  face := Sum.inr (indexedPolygon 10)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) (indexedPolygon 10) (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 4, 6]
  vertex := 7
  face := Sum.inl (indexedFacet 6)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 14) (indexedFacet 6) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 3, 4, 7]
  vertex := 8
  face := Sum.inl (indexedFacet 10)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 15) (indexedFacet 10) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 3, 4, 5]
  vertex := 7
  face := Sum.inl (indexedFacet 11)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 19) (indexedFacet 11) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![2, 6, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := (indexedFacet 6)
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 14) (indexedFacet 6) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := (indexedFacet 7)
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 2, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 10) (indexedFacet 7) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := (indexedFacet 8)
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 2, 4, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 10) (indexedFacet 8) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := (indexedFacet 9)
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 2, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 12) (indexedFacet 9) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := (indexedFacet 10)
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![0, 3, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 15) (indexedFacet 10) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := (indexedFacet 11)
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![1, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 19) (indexedFacet 11) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := (indexedFacet 12)
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![1, 3, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 20) (indexedFacet 12) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := (indexedFacet 13)
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![1, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 22) (indexedFacet 13) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0398

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m14e10q1_0427.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0427
open _root_.Nonrational.SharedProjectionVertexSets

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_109, vertices_677, vertices_453, vertices_361, vertices_913, vertices_558, vertices_602, vertices_282, vertices_298, vertices_786, vertices_588, vertices_724, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_133, vertices_105, vertices_289, vertices_545, vertices_321, vertices_385, vertices_641, vertices_769, vertices_26, vertices_42, vertices_266, vertices_522, vertices_274, vertices_530, vertices_290, vertices_546, vertices_770, vertices_44, vertices_76, vertices_524, vertices_548, vertices_196, vertices_580, vertices_644, vertices_88, vertices_280, vertices_296, vertices_328, vertices_584, vertices_208, vertices_592, vertices_400, vertices_656, vertices_784, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_109), (false, vertices_677), (false, vertices_453), (false, vertices_361), (false, vertices_913), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_530), (true, vertices_524), (true, vertices_580), (true, vertices_88), (true, vertices_280), (true, vertices_584), (true, vertices_208), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

private noncomputable def indexedFacet (j : Fin 14) : boundary.facets := by
  let xs : List (Finset (Fin 10)) := [vertices_803, vertices_109, vertices_677, vertices_453, vertices_361, vertices_913, vertices_558, vertices_602, vertices_282, vertices_298, vertices_786, vertices_588, vertices_724, vertices_472]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

private noncomputable def indexedPolygon (j : Fin 37) : boundary.polygons := by
  let xs : List (Finset (Fin 10)) := [vertices_37, vertices_69, vertices_133, vertices_105, vertices_289, vertices_545, vertices_321, vertices_385, vertices_641, vertices_769, vertices_26, vertices_42, vertices_266, vertices_522, vertices_274, vertices_530, vertices_290, vertices_546, vertices_770, vertices_44, vertices_76, vertices_524, vertices_548, vertices_196, vertices_580, vertices_644, vertices_88, vertices_280, vertices_296, vertices_328, vertices_584, vertices_208, vertices_592, vertices_400, vertices_656, vertices_784, vertices_448]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 15, 18, 21, 23, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 14 else
  if p.val = (false, vertices_109) then 19 else
  if p.val = (false, vertices_677) then 16 else
  if p.val = (false, vertices_453) then 17 else
  if p.val = (false, vertices_361) then 20 else
  if p.val = (false, vertices_913) then 22 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_592) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
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
  frame := ![0, 1, 2, 4]
  vertex := 8
  face := Sum.inl (indexedFacet 6)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 11) (indexedFacet 6) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 5]
  vertex := 8
  face := Sum.inl (indexedFacet 7)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 10) (indexedFacet 7) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 3, 5, 6]
  vertex := 8
  face := Sum.inl (indexedFacet 12)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 23) (indexedFacet 12) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![2, 3, 5, 6]
  vertex := 7
  face := Sum.inl (indexedFacet 13)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 26) (indexedFacet 13) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![4, 0, 1, 2]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := (indexedFacet 6)
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 11) (indexedFacet 6) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := (indexedFacet 7)
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 10) (indexedFacet 7) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := (indexedFacet 8)
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 2, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 10) (indexedFacet 8) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := (indexedFacet 9)
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 2, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 11) (indexedFacet 9) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := (indexedFacet 10)
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![0, 3, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 14) (indexedFacet 10) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := (indexedFacet 11)
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![1, 2, 5, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 20) (indexedFacet 11) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := (indexedFacet 12)
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![1, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 23) (indexedFacet 12) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := (indexedFacet 13)
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .oneRow ![2, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 26) (indexedFacet 13) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0427

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m14e10q1_0428.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0428
open _root_.Nonrational.SharedProjectionVertexSets

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_213, vertices_665, vertices_809, vertices_457, vertices_593, vertices_598, vertices_166, vertices_806, vertices_198, vertices_426, vertices_450, vertices_188, vertices_572] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_81, vertices_145, vertices_529, vertices_193, vertices_321, vertices_577, vertices_769, vertices_38, vertices_70, vertices_134, vertices_518, vertices_162, vertices_290, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_60, vertices_84, vertices_148, vertices_532, vertices_164, vertices_548, vertices_196, vertices_152, vertices_536, vertices_168, vertices_296, vertices_552, vertices_392, vertices_592, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_213), (false, vertices_665), (false, vertices_809), (false, vertices_457), (false, vertices_593), (true, vertices_38), (true, vertices_70), (true, vertices_134), (true, vertices_518), (true, vertices_162), (true, vertices_290), (true, vertices_194), (true, vertices_386), (true, vertices_60), (true, vertices_532), (true, vertices_164), (true, vertices_548), (true, vertices_168)] (by decide +kernel)
  planeCache_correct := by decide +kernel

private noncomputable def indexedFacet (j : Fin 14) : boundary.facets := by
  let xs : List (Finset (Fin 10)) := [vertices_835, vertices_213, vertices_665, vertices_809, vertices_457, vertices_593, vertices_598, vertices_166, vertices_806, vertices_198, vertices_426, vertices_450, vertices_188, vertices_572]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

private noncomputable def indexedPolygon (j : Fin 37) : boundary.polygons := by
  let xs : List (Finset (Fin 10)) := [vertices_137, vertices_265, vertices_521, vertices_81, vertices_145, vertices_529, vertices_193, vertices_321, vertices_577, vertices_769, vertices_38, vertices_70, vertices_134, vertices_518, vertices_162, vertices_290, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_60, vertices_84, vertices_148, vertices_532, vertices_164, vertices_548, vertices_196, vertices_152, vertices_536, vertices_168, vertices_296, vertices_552, vertices_392, vertices_592, vertices_800, vertices_448]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 15, 18, 22, 23, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 14 else
  if p.val = (false, vertices_213) then 16 else
  if p.val = (false, vertices_665) then 19 else
  if p.val = (false, vertices_809) then 20 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_593) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_60) then 17 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_164) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_168) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_593), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_60), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
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
  frameSize := 4
  frame := ![0, 1, 3, 5]
  vertex := 8
  face := Sum.inl (indexedFacet 6)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 11) (indexedFacet 6) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 3
  frame := ![1, 2, 3]
  vertex := 4
  face := Sum.inr (indexedPolygon 21)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) (indexedPolygon 21) (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 4, 7]
  vertex := 8
  face := Sum.inl (indexedFacet 8)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 10) (indexedFacet 8) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 4, 6]
  vertex := 7
  face := Sum.inl (indexedFacet 10)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 14) (indexedFacet 10) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![5, 3, 1, 0]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := (indexedFacet 6)
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 11) (indexedFacet 6) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := (indexedFacet 7)
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 1, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 10) (indexedFacet 7) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := (indexedFacet 8)
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 1, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 10) (indexedFacet 8) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := (indexedFacet 9)
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 1, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 11) (indexedFacet 9) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := (indexedFacet 10)
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![0, 2, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 14) (indexedFacet 10) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := (indexedFacet 11)
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![0, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 16) (indexedFacet 11) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := (indexedFacet 12)
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![1, 2, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 21) (indexedFacet 12) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := (indexedFacet 13)
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .oneRow ![1, 2, 3, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 21) (indexedFacet 13) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0428

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m14e10q1_0433.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0433
open _root_.Nonrational.SharedProjectionVertexSets

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_453, vertices_569, vertices_241, vertices_401, vertices_865, vertices_174, vertices_558, vertices_406, vertices_838, vertices_154, vertices_538, vertices_740, vertices_184] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_145, vertices_273, vertices_529, vertices_97, vertices_545, vertices_193, vertices_321, vertices_385, vertices_769, vertices_46, vertices_134, vertices_262, vertices_518, vertices_26, vertices_138, vertices_522, vertices_146, vertices_274, vertices_530, vertices_770, vertices_164, vertices_548, vertices_196, vertices_324, vertices_580, vertices_388, vertices_56, vertices_152, vertices_536, vertices_168, vertices_552, vertices_176, vertices_400, vertices_224, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_453), (false, vertices_569), (false, vertices_241), (false, vertices_401), (false, vertices_865), (true, vertices_46), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_138), (true, vertices_522), (true, vertices_146), (true, vertices_164), (true, vertices_548), (true, vertices_580), (true, vertices_152), (true, vertices_168)] (by decide +kernel)
  planeCache_correct := by decide +kernel

private noncomputable def indexedFacet (j : Fin 14) : boundary.facets := by
  let xs : List (Finset (Fin 10)) := [vertices_787, vertices_453, vertices_569, vertices_241, vertices_401, vertices_865, vertices_174, vertices_558, vertices_406, vertices_838, vertices_154, vertices_538, vertices_740, vertices_184]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

private noncomputable def indexedPolygon (j : Fin 37) : boundary.polygons := by
  let xs : List (Finset (Fin 10)) := [vertices_49, vertices_145, vertices_273, vertices_529, vertices_97, vertices_545, vertices_193, vertices_321, vertices_385, vertices_769, vertices_46, vertices_134, vertices_262, vertices_518, vertices_26, vertices_138, vertices_522, vertices_146, vertices_274, vertices_530, vertices_770, vertices_164, vertices_548, vertices_196, vertices_324, vertices_580, vertices_388, vertices_56, vertices_152, vertices_536, vertices_168, vertices_552, vertices_176, vertices_400, vertices_224, vertices_608, vertices_832]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 16, 18, 20, 22, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_453) then 17 else
  if p.val = (false, vertices_569) then 19 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (false, vertices_401) then 0 else
  if p.val = (false, vertices_865) then 23 else
  if p.val = (true, vertices_46) then 15 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_146) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_168) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_401), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_46), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
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
  frameSize := 3
  frame := ![0, 1, 2]
  vertex := 4
  face := Sum.inr (indexedPolygon 10)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) (indexedPolygon 10) (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 3, 6]
  vertex := 7
  face := Sum.inl (indexedFacet 8)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 11) (indexedFacet 8) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 5, 7]
  vertex := 8
  face := Sum.inl (indexedFacet 9)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 12) (indexedFacet 9) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 4, 5, 6]
  vertex := 8
  face := Sum.inl (indexedFacet 12)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 21) (indexedFacet 12) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![2, 3, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := (indexedFacet 6)
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 10) (indexedFacet 6) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := (indexedFacet 7)
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 2, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 10) (indexedFacet 7) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := (indexedFacet 8)
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 1, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 11) (indexedFacet 8) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := (indexedFacet 9)
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![0, 1, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 12) (indexedFacet 9) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := (indexedFacet 10)
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![0, 2, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 14) (indexedFacet 10) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := (indexedFacet 11)
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![0, 2, 3, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 14) (indexedFacet 11) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := (indexedFacet 12)
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![1, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 21) (indexedFacet 12) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := (indexedFacet 13)
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![2, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 27) (indexedFacet 13) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0433

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m14e10q1_0434.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0434
open _root_.Nonrational.SharedProjectionVertexSets

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_333, vertices_233, vertices_553, vertices_689, vertices_961, vertices_110, vertices_270, vertices_118, vertices_278, vertices_570, vertices_914, vertices_340, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_265, vertices_521, vertices_161, vertices_545, vertices_193, vertices_321, vertices_641, vertices_769, vertices_14, vertices_22, vertices_102, vertices_262, vertices_42, vertices_266, vertices_522, vertices_50, vertices_274, vertices_530, vertices_770, vertices_76, vertices_268, vertices_84, vertices_276, vertices_324, vertices_104, vertices_552, vertices_112, vertices_176, vertices_560, vertices_336, vertices_400, vertices_656, vertices_224, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_333), (false, vertices_233), (false, vertices_553), (false, vertices_689), (false, vertices_961), (true, vertices_14), (true, vertices_22), (true, vertices_102), (true, vertices_262), (true, vertices_42), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_84), (true, vertices_276), (true, vertices_112), (true, vertices_336), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

private noncomputable def indexedFacet (j : Fin 14) : boundary.facets := by
  let xs : List (Finset (Fin 10)) := [vertices_779, vertices_333, vertices_233, vertices_553, vertices_689, vertices_961, vertices_110, vertices_270, vertices_118, vertices_278, vertices_570, vertices_914, vertices_340, vertices_496]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

private noncomputable def indexedPolygon (j : Fin 37) : boundary.polygons := by
  let xs : List (Finset (Fin 10)) := [vertices_41, vertices_73, vertices_265, vertices_521, vertices_161, vertices_545, vertices_193, vertices_321, vertices_641, vertices_769, vertices_14, vertices_22, vertices_102, vertices_262, vertices_42, vertices_266, vertices_522, vertices_50, vertices_274, vertices_530, vertices_770, vertices_76, vertices_268, vertices_84, vertices_276, vertices_324, vertices_104, vertices_552, vertices_112, vertices_176, vertices_560, vertices_336, vertices_400, vertices_656, vertices_224, vertices_448, vertices_896]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 16, 18, 20, 22, 23, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_333) then 17 else
  if p.val = (false, vertices_233) then 19 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_102) then 15 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_400) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_102), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
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
  frameSize := 3
  frame := ![0, 1, 4]
  vertex := 5
  face := Sum.inr (indexedPolygon 12)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) (indexedPolygon 12) (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 4]
  vertex := 8
  face := Sum.inl (indexedFacet 10)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 14) (indexedFacet 10) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 3, 6, 7]
  vertex := 8
  face := Sum.inl (indexedFacet 11)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 18) (indexedFacet 11) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![3, 4, 5, 6]
  vertex := 7
  face := Sum.inl (indexedFacet 13)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 28) (indexedFacet 13) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![1, 2, 0, 3]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := (indexedFacet 6)
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 10) (indexedFacet 6) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := (indexedFacet 7)
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 1, 2, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 10) (indexedFacet 7) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := (indexedFacet 8)
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 1, 3, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 11) (indexedFacet 8) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := (indexedFacet 9)
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 1, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 11) (indexedFacet 9) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := (indexedFacet 10)
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![0, 2, 3, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 14) (indexedFacet 10) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := (indexedFacet 11)
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![0, 3, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 18) (indexedFacet 11) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := (indexedFacet 12)
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![1, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 23) (indexedFacet 12) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := (indexedFacet 13)
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .oneRow ![3, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 28) (indexedFacet 13) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0434

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m14e10q1_0435.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0435
open _root_.Nonrational.SharedProjectionVertexSets

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_595, vertices_309, vertices_425, vertices_689, vertices_961, vertices_590, vertices_566, vertices_278, vertices_326, vertices_300, vertices_556, vertices_460, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_83, vertices_49, vertices_273, vertices_529, vertices_161, vertices_289, vertices_321, vertices_577, vertices_385, vertices_641, vertices_22, vertices_70, vertices_262, vertices_518, vertices_274, vertices_530, vertices_322, vertices_578, vertices_44, vertices_76, vertices_268, vertices_524, vertices_52, vertices_276, vertices_292, vertices_548, vertices_324, vertices_168, vertices_296, vertices_552, vertices_200, vertices_584, vertices_392, vertices_560, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_595), (false, vertices_309), (false, vertices_425), (false, vertices_689), (false, vertices_961), (true, vertices_22), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_44), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_548), (true, vertices_324), (true, vertices_552), (true, vertices_200), (true, vertices_584)] (by decide +kernel)
  planeCache_correct := by decide +kernel

private noncomputable def indexedFacet (j : Fin 14) : boundary.facets := by
  let xs : List (Finset (Fin 10)) := [vertices_339, vertices_595, vertices_309, vertices_425, vertices_689, vertices_961, vertices_590, vertices_566, vertices_278, vertices_326, vertices_300, vertices_556, vertices_460, vertices_744]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

private noncomputable def indexedPolygon (j : Fin 37) : boundary.polygons := by
  let xs : List (Finset (Fin 10)) := [vertices_83, vertices_49, vertices_273, vertices_529, vertices_161, vertices_289, vertices_321, vertices_577, vertices_385, vertices_641, vertices_22, vertices_70, vertices_262, vertices_518, vertices_274, vertices_530, vertices_322, vertices_578, vertices_44, vertices_76, vertices_268, vertices_524, vertices_52, vertices_276, vertices_292, vertices_548, vertices_324, vertices_168, vertices_296, vertices_552, vertices_200, vertices_584, vertices_392, vertices_560, vertices_672, vertices_448, vertices_704]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 16, 18, 20, 22, 23, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 14 else
  if p.val = (false, vertices_595) then 15 else
  if p.val = (false, vertices_309) then 17 else
  if p.val = (false, vertices_425) then 19 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_584) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
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
  frame := ![0, 1, 3, 4]
  vertex := 8
  face := Sum.inl (indexedFacet 7)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 10) (indexedFacet 7) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 2, 5]
  vertex := 8
  face := Sum.inl (indexedFacet 6)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 11) (indexedFacet 6) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 5, 6]
  vertex := 7
  face := Sum.inl (indexedFacet 12)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 19) (indexedFacet 12) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![2, 4, 5, 6]
  vertex := 8
  face := Sum.inl (indexedFacet 13)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 27) (indexedFacet 13) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![3, 0, 1, 2]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := (indexedFacet 6)
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 11) (indexedFacet 6) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := (indexedFacet 7)
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 3, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 10) (indexedFacet 7) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := (indexedFacet 8)
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 1, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 10) (indexedFacet 8) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := (indexedFacet 9)
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 1, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 11) (indexedFacet 9) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := (indexedFacet 10)
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![1, 2, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 18) (indexedFacet 10) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := (indexedFacet 11)
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![1, 2, 4, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 18) (indexedFacet 11) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := (indexedFacet 12)
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![1, 2, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 19) (indexedFacet 12) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := (indexedFacet 13)
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .oneRow ![2, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 27) (indexedFacet 13) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0435

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m14e10q1_0436.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0436
open _root_.Nonrational.SharedProjectionVertexSets

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_539, vertices_141, vertices_525, vertices_421, vertices_837, vertices_185, vertices_817, vertices_590, vertices_218, vertices_242, vertices_562, vertices_610, vertices_460, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_261, vertices_517, vertices_25, vertices_137, vertices_521, vertices_49, vertices_529, vertices_161, vertices_289, vertices_769, vertices_26, vertices_74, vertices_522, vertices_50, vertices_210, vertices_530, vertices_98, vertices_546, vertices_578, vertices_76, vertices_140, vertices_524, vertices_324, vertices_580, vertices_388, vertices_152, vertices_200, vertices_176, vertices_560, vertices_224, vertices_608, vertices_416, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_539), (false, vertices_141), (false, vertices_525), (false, vertices_421), (false, vertices_837), (false, vertices_185), (false, vertices_817), (true, vertices_74), (true, vertices_50), (true, vertices_210), (true, vertices_98), (true, vertices_546), (true, vertices_578), (true, vertices_76), (true, vertices_200), (true, vertices_224), (true, vertices_608), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

private noncomputable def indexedFacet (j : Fin 14) : boundary.facets := by
  let xs : List (Finset (Fin 10)) := [vertices_539, vertices_141, vertices_525, vertices_421, vertices_837, vertices_185, vertices_817, vertices_590, vertices_218, vertices_242, vertices_562, vertices_610, vertices_460, vertices_992]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

private noncomputable def indexedPolygon (j : Fin 37) : boundary.polygons := by
  let xs : List (Finset (Fin 10)) := [vertices_13, vertices_133, vertices_261, vertices_517, vertices_25, vertices_137, vertices_521, vertices_49, vertices_529, vertices_161, vertices_289, vertices_769, vertices_26, vertices_74, vertices_522, vertices_50, vertices_210, vertices_530, vertices_98, vertices_546, vertices_578, vertices_76, vertices_140, vertices_524, vertices_324, vertices_580, vertices_388, vertices_152, vertices_200, vertices_176, vertices_560, vertices_224, vertices_608, vertices_416, vertices_800, vertices_448, vertices_832]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

noncomputable def pointPriority : Fin 9 → ℕ := ![12, 15, 18, 20, 22, 23, 24, 25, 26]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_539) then 13 else
  if p.val = (false, vertices_141) then 0 else
  if p.val = (false, vertices_525) then 1 else
  if p.val = (false, vertices_421) then 16 else
  if p.val = (false, vertices_837) then 17 else
  if p.val = (false, vertices_185) then 19 else
  if p.val = (false, vertices_817) then 21 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_210) then 14 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_448) then 11 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_141), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_210), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
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
  frameSize := 3
  frame := ![0, 3, 5]
  vertex := 6
  face := Sum.inr (indexedPolygon 16)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) (indexedPolygon 16) (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 2, 5]
  vertex := 8
  face := Sum.inl (indexedFacet 7)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 13) (indexedFacet 7) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 5, 6]
  vertex := 7
  face := Sum.inl (indexedFacet 12)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 21) (indexedFacet 12) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![4, 5, 6, 7]
  vertex := 8
  face := Sum.inl (indexedFacet 13)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 31) (indexedFacet 13) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![3, 0, 1, 4]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := (indexedFacet 7)
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 13) (indexedFacet 7) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := (indexedFacet 8)
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 12) (indexedFacet 8) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := (indexedFacet 9)
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 15) (indexedFacet 9) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := (indexedFacet 10)
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 3, 4, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 15) (indexedFacet 10) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := (indexedFacet 11)
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![0, 4, 5, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 18) (indexedFacet 11) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := (indexedFacet 12)
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![1, 2, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 21) (indexedFacet 12) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := (indexedFacet 13)
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![4, 5, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 31) (indexedFacet 13) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0436

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m14e10q1_0448.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0448
open _root_.Nonrational.SharedProjectionVertexSets

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_357, vertices_677, vertices_457, vertices_721, vertices_609, vertices_302, vertices_558, vertices_662, vertices_602, vertices_154, vertices_394, vertices_216, vertices_872] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_97, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_641, vertices_46, vertices_134, vertices_262, vertices_518, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_530, vertices_386, vertices_292, vertices_548, vertices_644, vertices_88, vertices_152, vertices_296, vertices_552, vertices_200, vertices_328, vertices_584, vertices_392, vertices_208, vertices_592, vertices_656, vertices_352, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_357), (false, vertices_677), (false, vertices_457), (false, vertices_721), (false, vertices_609), (true, vertices_46), (true, vertices_518), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_530), (true, vertices_88), (true, vertices_152), (true, vertices_296), (true, vertices_552), (true, vertices_584)] (by decide +kernel)
  planeCache_correct := by decide +kernel

private noncomputable def indexedFacet (j : Fin 14) : boundary.facets := by
  let xs : List (Finset (Fin 10)) := [vertices_391, vertices_357, vertices_677, vertices_457, vertices_721, vertices_609, vertices_302, vertices_558, vertices_662, vertices_602, vertices_154, vertices_394, vertices_216, vertices_872]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

private noncomputable def indexedPolygon (j : Fin 37) : boundary.polygons := by
  let xs : List (Finset (Fin 10)) := [vertices_37, vertices_133, vertices_261, vertices_97, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_641, vertices_46, vertices_134, vertices_262, vertices_518, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_530, vertices_386, vertices_292, vertices_548, vertices_644, vertices_88, vertices_152, vertices_296, vertices_552, vertices_200, vertices_328, vertices_584, vertices_392, vertices_208, vertices_592, vertices_656, vertices_352, vertices_608]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 16, 19, 21, 23, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_357) then 17 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (false, vertices_721) then 22 else
  if p.val = (false, vertices_609) then 0 else
  if p.val = (true, vertices_46) then 15 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_584) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_609), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_46), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
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
  frame := ![0, 1, 3, 6]
  vertex := 8
  face := Sum.inl (indexedFacet 8)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 11) (indexedFacet 8) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 3
  frame := ![0, 1, 2]
  vertex := 4
  face := Sum.inr (indexedPolygon 10)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) (indexedPolygon 10) (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 5]
  vertex := 8
  face := Sum.inl (indexedFacet 9)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 14) (indexedFacet 9) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![2, 4, 5, 7]
  vertex := 8
  face := Sum.inl (indexedFacet 13)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 26) (indexedFacet 13) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![6, 1, 0, 2]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := (indexedFacet 6)
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 10) (indexedFacet 6) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := (indexedFacet 7)
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 2, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 10) (indexedFacet 7) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := (indexedFacet 8)
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 1, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 11) (indexedFacet 8) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := (indexedFacet 9)
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![0, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 14) (indexedFacet 9) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := (indexedFacet 10)
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![0, 2, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 14) (indexedFacet 10) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := (indexedFacet 11)
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![0, 2, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 15) (indexedFacet 11) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := (indexedFacet 12)
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![2, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 24) (indexedFacet 12) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := (indexedFacet 13)
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .oneRow ![2, 4, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 26) (indexedFacet 13) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0448

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m14e10q1_0449.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0449
open _root_.Nonrational.SharedProjectionVertexSets

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_781, vertices_105, vertices_713, vertices_913, vertices_481, vertices_110, vertices_270, vertices_118, vertices_278, vertices_434, vertices_604, vertices_788, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_265, vertices_521, vertices_97, vertices_289, vertices_193, vertices_385, vertices_641, vertices_769, vertices_14, vertices_22, vertices_102, vertices_262, vertices_42, vertices_266, vertices_50, vertices_274, vertices_290, vertices_76, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_772, vertices_104, vertices_584, vertices_112, vertices_176, vertices_592, vertices_400, vertices_656, vertices_784, vertices_224, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_781), (false, vertices_105), (false, vertices_713), (false, vertices_913), (false, vertices_481), (true, vertices_14), (true, vertices_22), (true, vertices_102), (true, vertices_262), (true, vertices_50), (true, vertices_274), (true, vertices_76), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_112), (true, vertices_176), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

private noncomputable def indexedFacet (j : Fin 14) : boundary.facets := by
  let xs : List (Finset (Fin 10)) := [vertices_299, vertices_781, vertices_105, vertices_713, vertices_913, vertices_481, vertices_110, vertices_270, vertices_118, vertices_278, vertices_434, vertices_604, vertices_788, vertices_752]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

private noncomputable def indexedPolygon (j : Fin 37) : boundary.polygons := by
  let xs : List (Finset (Fin 10)) := [vertices_41, vertices_73, vertices_265, vertices_521, vertices_97, vertices_289, vertices_193, vertices_385, vertices_641, vertices_769, vertices_14, vertices_22, vertices_102, vertices_262, vertices_42, vertices_266, vertices_50, vertices_274, vertices_290, vertices_76, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_772, vertices_104, vertices_584, vertices_112, vertices_176, vertices_592, vertices_400, vertices_656, vertices_784, vertices_224, vertices_416, vertices_704]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 16, 18, 20, 22, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 14 else
  if p.val = (false, vertices_781) then 17 else
  if p.val = (false, vertices_105) then 0 else
  if p.val = (false, vertices_713) then 19 else
  if p.val = (false, vertices_913) then 21 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_102) then 15 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_592) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_105), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_102), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
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
  frame := ![0, 3, 4, 6]
  vertex := 7
  face := Sum.inl (indexedFacet 10)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 16) (indexedFacet 10) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 3
  frame := ![0, 1, 4]
  vertex := 5
  face := Sum.inr (indexedPolygon 12)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) (indexedPolygon 12) (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 3, 5]
  vertex := 8
  face := Sum.inl (indexedFacet 11)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 19) (indexedFacet 11) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![3, 4, 5, 6]
  vertex := 8
  face := Sum.inl (indexedFacet 13)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 28) (indexedFacet 13) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![7, 0, 1, 3]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := (indexedFacet 6)
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 10) (indexedFacet 6) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := (indexedFacet 7)
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 1, 2, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 10) (indexedFacet 7) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := (indexedFacet 8)
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 1, 3, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 11) (indexedFacet 8) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := (indexedFacet 9)
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 1, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 11) (indexedFacet 9) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := (indexedFacet 10)
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![0, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 16) (indexedFacet 10) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := (indexedFacet 11)
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![1, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 19) (indexedFacet 11) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := (indexedFacet 12)
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![1, 3, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 23) (indexedFacet 12) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := (indexedFacet 13)
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .oneRow ![3, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 28) (indexedFacet 13) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0449

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m14e10q1_0450.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0450
open _root_.Nonrational.SharedProjectionVertexSets

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_333, vertices_233, vertices_553, vertices_465, vertices_929, vertices_110, vertices_270, vertices_118, vertices_278, vertices_570, vertices_914, vertices_340, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_265, vertices_521, vertices_161, vertices_545, vertices_193, vertices_321, vertices_385, vertices_769, vertices_14, vertices_22, vertices_102, vertices_262, vertices_42, vertices_266, vertices_522, vertices_50, vertices_274, vertices_530, vertices_770, vertices_76, vertices_268, vertices_84, vertices_276, vertices_324, vertices_104, vertices_552, vertices_112, vertices_560, vertices_208, vertices_336, vertices_400, vertices_656, vertices_224, vertices_672, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_333), (false, vertices_233), (false, vertices_553), (false, vertices_465), (false, vertices_929), (true, vertices_14), (true, vertices_22), (true, vertices_102), (true, vertices_262), (true, vertices_42), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_84), (true, vertices_276), (true, vertices_112), (true, vertices_560), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

private noncomputable def indexedFacet (j : Fin 14) : boundary.facets := by
  let xs : List (Finset (Fin 10)) := [vertices_779, vertices_333, vertices_233, vertices_553, vertices_465, vertices_929, vertices_110, vertices_270, vertices_118, vertices_278, vertices_570, vertices_914, vertices_340, vertices_752]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

private noncomputable def indexedPolygon (j : Fin 37) : boundary.polygons := by
  let xs : List (Finset (Fin 10)) := [vertices_41, vertices_73, vertices_265, vertices_521, vertices_161, vertices_545, vertices_193, vertices_321, vertices_385, vertices_769, vertices_14, vertices_22, vertices_102, vertices_262, vertices_42, vertices_266, vertices_522, vertices_50, vertices_274, vertices_530, vertices_770, vertices_76, vertices_268, vertices_84, vertices_276, vertices_324, vertices_104, vertices_552, vertices_112, vertices_560, vertices_208, vertices_336, vertices_400, vertices_656, vertices_224, vertices_672, vertices_896]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 16, 18, 20, 22, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_333) then 17 else
  if p.val = (false, vertices_233) then 19 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_465) then 21 else
  if p.val = (false, vertices_929) then 23 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_102) then 15 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_656) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_102), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
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
  frameSize := 3
  frame := ![0, 1, 4]
  vertex := 5
  face := Sum.inr (indexedPolygon 12)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) (indexedPolygon 12) (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 4]
  vertex := 8
  face := Sum.inl (indexedFacet 10)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 14) (indexedFacet 10) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 3, 6, 7]
  vertex := 8
  face := Sum.inl (indexedFacet 11)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 18) (indexedFacet 11) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![3, 4, 5, 6]
  vertex := 8
  face := Sum.inl (indexedFacet 13)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 28) (indexedFacet 13) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![1, 2, 0, 3]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := (indexedFacet 6)
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 10) (indexedFacet 6) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := (indexedFacet 7)
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 1, 2, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 10) (indexedFacet 7) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := (indexedFacet 8)
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 1, 3, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 11) (indexedFacet 8) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := (indexedFacet 9)
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 1, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 11) (indexedFacet 9) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := (indexedFacet 10)
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![0, 2, 3, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 14) (indexedFacet 10) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := (indexedFacet 11)
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![0, 3, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 18) (indexedFacet 11) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := (indexedFacet 12)
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![1, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 23) (indexedFacet 12) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := (indexedFacet 13)
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .oneRow ![3, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 28) (indexedFacet 13) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0450

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m14e10q1_0455.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0455
open _root_.Nonrational.SharedProjectionVertexSets

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_227, vertices_781, vertices_661, vertices_389, vertices_617, vertices_457, vertices_673, vertices_790, vertices_362, vertices_810, vertices_690, vertices_210, vertices_338, vertices_468] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_265, vertices_521, vertices_97, vertices_161, vertices_545, vertices_193, vertices_385, vertices_641, vertices_298, vertices_82, vertices_146, vertices_274, vertices_530, vertices_98, vertices_162, vertices_546, vertices_194, vertices_322, vertices_770, vertices_148, vertices_276, vertices_532, vertices_388, vertices_772, vertices_104, vertices_552, vertices_328, vertices_776, vertices_208, vertices_336, vertices_656, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_227), (false, vertices_781), (false, vertices_661), (false, vertices_389), (false, vertices_617), (false, vertices_457), (false, vertices_673), (true, vertices_298), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_546), (true, vertices_322), (true, vertices_770), (true, vertices_276), (true, vertices_208), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

private noncomputable def indexedFacet (j : Fin 14) : boundary.facets := by
  let xs : List (Finset (Fin 10)) := [vertices_227, vertices_781, vertices_661, vertices_389, vertices_617, vertices_457, vertices_673, vertices_790, vertices_362, vertices_810, vertices_690, vertices_210, vertices_338, vertices_468]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

private noncomputable def indexedPolygon (j : Fin 37) : boundary.polygons := by
  let xs : List (Finset (Fin 10)) := [vertices_133, vertices_261, vertices_517, vertices_73, vertices_265, vertices_521, vertices_97, vertices_161, vertices_545, vertices_193, vertices_385, vertices_641, vertices_298, vertices_82, vertices_146, vertices_274, vertices_530, vertices_98, vertices_162, vertices_546, vertices_194, vertices_322, vertices_770, vertices_148, vertices_276, vertices_532, vertices_388, vertices_772, vertices_104, vertices_552, vertices_328, vertices_776, vertices_208, vertices_336, vertices_656, vertices_672, vertices_448]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

noncomputable def pointPriority : Fin 9 → ℕ := ![12, 15, 18, 21, 22, 23, 24, 25, 26]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_227) then 13 else
  if p.val = (false, vertices_781) then 16 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_389) then 0 else
  if p.val = (false, vertices_617) then 19 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (false, vertices_673) then 1 else
  if p.val = (true, vertices_298) then 14 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_336) then 11 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_673), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_298), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
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
  frameSize := 3
  frame := ![0, 2, 4]
  vertex := 7
  face := Sum.inr (indexedPolygon 12)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) (indexedPolygon 12) (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 3, 4, 6]
  vertex := 8
  face := Sum.inl (indexedFacet 10)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 14) (indexedFacet 10) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 3, 7]
  vertex := 8
  face := Sum.inl (indexedFacet 7)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 15) (indexedFacet 7) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 3, 5, 6]
  vertex := 7
  face := Sum.inl (indexedFacet 13)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 23) (indexedFacet 13) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![2, 4, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := (indexedFacet 7)
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 15) (indexedFacet 7) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := (indexedFacet 8)
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 2, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 12) (indexedFacet 8) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := (indexedFacet 9)
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 2, 4, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 12) (indexedFacet 9) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := (indexedFacet 10)
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![0, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 14) (indexedFacet 10) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := (indexedFacet 11)
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![0, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 13) (indexedFacet 11) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := (indexedFacet 12)
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![0, 3, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 13) (indexedFacet 12) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := (indexedFacet 13)
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![1, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 23) (indexedFacet 13) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0455

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m14e10q1_0457.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0457
open _root_.Nonrational.SharedProjectionVertexSets

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_117, vertices_181, vertices_709, vertices_425, vertices_865, vertices_662, vertices_154, vertices_538, vertices_842, vertices_394, vertices_604, vertices_376, vertices_184] (by decide +kernel)
  polygons := literalFinset [vertices_53, vertices_69, vertices_133, vertices_97, vertices_161, vertices_289, vertices_577, vertices_385, vertices_641, vertices_769, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_530, vertices_386, vertices_642, vertices_770, vertices_84, vertices_148, vertices_532, vertices_580, vertices_644, vertices_56, vertices_88, vertices_152, vertices_536, vertices_168, vertices_296, vertices_328, vertices_584, vertices_392, vertices_112, vertices_176, vertices_352, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_117), (false, vertices_181), (false, vertices_709), (false, vertices_425), (false, vertices_865), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_530), (true, vertices_532), (true, vertices_56), (true, vertices_88), (true, vertices_152), (true, vertices_536), (true, vertices_328), (true, vertices_584)] (by decide +kernel)
  planeCache_correct := by decide +kernel

private noncomputable def indexedFacet (j : Fin 14) : boundary.facets := by
  let xs : List (Finset (Fin 10)) := [vertices_899, vertices_117, vertices_181, vertices_709, vertices_425, vertices_865, vertices_662, vertices_154, vertices_538, vertices_842, vertices_394, vertices_604, vertices_376, vertices_184]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

private noncomputable def indexedPolygon (j : Fin 37) : boundary.polygons := by
  let xs : List (Finset (Fin 10)) := [vertices_53, vertices_69, vertices_133, vertices_97, vertices_161, vertices_289, vertices_577, vertices_385, vertices_641, vertices_769, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_530, vertices_386, vertices_642, vertices_770, vertices_84, vertices_148, vertices_532, vertices_580, vertices_644, vertices_56, vertices_88, vertices_152, vertices_536, vertices_168, vertices_296, vertices_328, vertices_584, vertices_392, vertices_112, vertices_176, vertices_352, vertices_832]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 15, 19, 21, 22, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 14 else
  if p.val = (false, vertices_117) then 16 else
  if p.val = (false, vertices_181) then 17 else
  if p.val = (false, vertices_709) then 18 else
  if p.val = (false, vertices_425) then 20 else
  if p.val = (false, vertices_865) then 23 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_584) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
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
  face := Sum.inl (indexedFacet 6)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 14) (indexedFacet 6) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 5, 7]
  vertex := 8
  face := Sum.inl (indexedFacet 9)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 12) (indexedFacet 9) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 3, 5]
  vertex := 8
  face := Sum.inl (indexedFacet 11)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 19) (indexedFacet 11) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![2, 3, 4, 5]
  vertex := 7
  face := Sum.inl (indexedFacet 12)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 24) (indexedFacet 12) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![6, 0, 1, 2]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := (indexedFacet 6)
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 14) (indexedFacet 6) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := (indexedFacet 7)
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 2, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 10) (indexedFacet 7) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := (indexedFacet 8)
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 2, 3, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 10) (indexedFacet 8) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := (indexedFacet 9)
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![0, 2, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 12) (indexedFacet 9) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := (indexedFacet 10)
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![0, 2, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 11) (indexedFacet 10) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := (indexedFacet 11)
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![1, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 19) (indexedFacet 11) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := (indexedFacet 12)
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![2, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 24) (indexedFacet 12) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := (indexedFacet 13)
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![2, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 24) (indexedFacet 13) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0457

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m14e10q1_0460.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0460
open _root_.Nonrational.SharedProjectionVertexSets

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_787, vertices_675, vertices_565, vertices_241, vertices_401, vertices_782, vertices_714, vertices_220, vertices_412, vertices_620, vertices_116, vertices_788, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_49, vertices_145, vertices_273, vertices_529, vertices_161, vertices_545, vertices_385, vertices_138, vertices_266, vertices_522, vertices_642, vertices_770, vertices_156, vertices_76, vertices_268, vertices_524, vertices_52, vertices_84, vertices_276, vertices_532, vertices_100, vertices_548, vertices_772, vertices_200, vertices_584, vertices_392, vertices_112, vertices_208, vertices_400, vertices_784, vertices_224, vertices_608, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_787), (false, vertices_675), (false, vertices_565), (false, vertices_241), (false, vertices_401), (true, vertices_522), (true, vertices_156), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_84), (true, vertices_276), (true, vertices_100), (true, vertices_772), (true, vertices_200), (true, vertices_584), (true, vertices_608), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

private noncomputable def indexedFacet (j : Fin 14) : boundary.facets := by
  let xs : List (Finset (Fin 10)) := [vertices_395, vertices_787, vertices_675, vertices_565, vertices_241, vertices_401, vertices_782, vertices_714, vertices_220, vertices_412, vertices_620, vertices_116, vertices_788, vertices_736]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

private noncomputable def indexedPolygon (j : Fin 37) : boundary.polygons := by
  let xs : List (Finset (Fin 10)) := [vertices_131, vertices_259, vertices_515, vertices_49, vertices_145, vertices_273, vertices_529, vertices_161, vertices_545, vertices_385, vertices_138, vertices_266, vertices_522, vertices_642, vertices_770, vertices_156, vertices_76, vertices_268, vertices_524, vertices_52, vertices_84, vertices_276, vertices_532, vertices_100, vertices_548, vertices_772, vertices_200, vertices_584, vertices_392, vertices_112, vertices_208, vertices_400, vertices_784, vertices_224, vertices_608, vertices_672, vertices_704]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 17, 20, 21, 23, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 14 else
  if p.val = (false, vertices_787) then 15 else
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_565) then 18 else
  if p.val = (false, vertices_241) then 22 else
  if p.val = (false, vertices_401) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_156) then 19 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_608) then 11 else
  if p.val = (true, vertices_704) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_401), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_156), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
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
  vertex := 6
  face := Sum.inr (indexedPolygon 15)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) (indexedPolygon 15) (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 2, 7]
  vertex := 8
  face := Sum.inl (indexedFacet 6)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 11) (indexedFacet 6) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 5, 6]
  vertex := 8
  face := Sum.inl (indexedFacet 7)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 10) (indexedFacet 7) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 4, 5]
  vertex := 8
  face := Sum.inl (indexedFacet 10)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 16) (indexedFacet 10) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![3, 7, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := (indexedFacet 6)
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 11) (indexedFacet 6) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := (indexedFacet 7)
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 2, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 10) (indexedFacet 7) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := (indexedFacet 8)
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![1, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 15) (indexedFacet 8) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := (indexedFacet 9)
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 2, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 15) (indexedFacet 9) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := (indexedFacet 10)
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![1, 2, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 16) (indexedFacet 10) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := (indexedFacet 11)
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![1, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 19) (indexedFacet 11) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := (indexedFacet 12)
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![1, 3, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 21) (indexedFacet 12) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := (indexedFacet 13)
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![4, 5, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 33) (indexedFacet 13) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0460

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m14e10q1_0461.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0461
open _root_.Nonrational.SharedProjectionVertexSets

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_781, vertices_425, vertices_713, vertices_817, vertices_590, vertices_566, vertices_86, vertices_434, vertices_210, vertices_706, vertices_220, vertices_412, vertices_788] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_161, vertices_289, vertices_545, vertices_641, vertices_769, vertices_22, vertices_70, vertices_518, vertices_50, vertices_82, vertices_146, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_156, vertices_76, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_772, vertices_200, vertices_584, vertices_392, vertices_304, vertices_560, vertices_208, vertices_400, vertices_784, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_781), (false, vertices_425), (false, vertices_713), (false, vertices_817), (true, vertices_22), (true, vertices_70), (true, vertices_518), (true, vertices_50), (true, vertices_82), (true, vertices_146), (true, vertices_194), (true, vertices_578), (true, vertices_156), (true, vertices_76), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_208), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

private noncomputable def indexedFacet (j : Fin 14) : boundary.facets := by
  let xs : List (Finset (Fin 10)) := [vertices_675, vertices_781, vertices_425, vertices_713, vertices_817, vertices_590, vertices_566, vertices_86, vertices_434, vertices_210, vertices_706, vertices_220, vertices_412, vertices_788]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

private noncomputable def indexedPolygon (j : Fin 37) : boundary.polygons := by
  let xs : List (Finset (Fin 10)) := [vertices_137, vertices_265, vertices_521, vertices_161, vertices_289, vertices_545, vertices_641, vertices_769, vertices_22, vertices_70, vertices_518, vertices_50, vertices_82, vertices_146, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_156, vertices_76, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_772, vertices_200, vertices_584, vertices_392, vertices_304, vertices_560, vertices_208, vertices_400, vertices_784, vertices_416, vertices_704]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

noncomputable def pointPriority : Fin 9 → ℕ := ![14, 16, 19, 22, 24, 25, 26, 27, 28]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 15 else
  if p.val = (false, vertices_781) then 17 else
  if p.val = (false, vertices_425) then 20 else
  if p.val = (false, vertices_713) then 21 else
  if p.val = (false, vertices_817) then 23 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_156) then 18 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_400) then 13 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_156), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
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
  frame := ![0, 1, 2, 5]
  vertex := 8
  face := Sum.inl (indexedFacet 5)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 9) (indexedFacet 5) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 3
  frame := ![1, 2, 3]
  vertex := 6
  face := Sum.inr (indexedPolygon 19)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) (indexedPolygon 19) (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 3, 4]
  vertex := 8
  face := Sum.inl (indexedFacet 6)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 8) (indexedFacet 6) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 3, 4, 6]
  vertex := 7
  face := Sum.inl (indexedFacet 8)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 11) (indexedFacet 8) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![5, 2, 1, 0]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := (indexedFacet 5)
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 9) (indexedFacet 5) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := (indexedFacet 6)
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 3, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 8) (indexedFacet 6) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := (indexedFacet 7)
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 1, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 8) (indexedFacet 7) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := (indexedFacet 8)
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![0, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 11) (indexedFacet 8) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := (indexedFacet 9)
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![0, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 12) (indexedFacet 9) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := (indexedFacet 10)
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![0, 5, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 16) (indexedFacet 10) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := (indexedFacet 11)
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![1, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 19) (indexedFacet 11) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := (indexedFacet 12)
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .oneRow ![1, 2, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 19) (indexedFacet 12) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet8 : boundary.facets := (indexedFacet 13)
noncomputable def cover8 : FacetCoverage heightProof coverFacet8 :=
  .fundamental ![1, 3, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 24) (indexedFacet 13) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0461

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m14e10q1_0462.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0462
open _root_.Nonrational.SharedProjectionVertexSets

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_781, vertices_613, vertices_453, vertices_721, vertices_558, vertices_58, vertices_282, vertices_778, vertices_690, vertices_466, vertices_124, vertices_348, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_193, vertices_577, vertices_385, vertices_641, vertices_769, vertices_26, vertices_42, vertices_266, vertices_522, vertices_50, vertices_146, vertices_274, vertices_546, vertices_386, vertices_642, vertices_770, vertices_92, vertices_44, vertices_268, vertices_524, vertices_100, vertices_548, vertices_324, vertices_56, vertices_280, vertices_776, vertices_112, vertices_560, vertices_208, vertices_336, vertices_592, vertices_656, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_781), (false, vertices_613), (false, vertices_453), (false, vertices_721), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_546), (true, vertices_92), (true, vertices_44), (true, vertices_56), (true, vertices_280), (true, vertices_112), (true, vertices_560), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

private noncomputable def indexedFacet (j : Fin 14) : boundary.facets := by
  let xs : List (Finset (Fin 10)) := [vertices_899, vertices_781, vertices_613, vertices_453, vertices_721, vertices_558, vertices_58, vertices_282, vertices_778, vertices_690, vertices_466, vertices_124, vertices_348, vertices_624]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

private noncomputable def indexedPolygon (j : Fin 37) : boundary.polygons := by
  let xs : List (Finset (Fin 10)) := [vertices_69, vertices_261, vertices_517, vertices_193, vertices_577, vertices_385, vertices_641, vertices_769, vertices_26, vertices_42, vertices_266, vertices_522, vertices_50, vertices_146, vertices_274, vertices_546, vertices_386, vertices_642, vertices_770, vertices_92, vertices_44, vertices_268, vertices_524, vertices_100, vertices_548, vertices_324, vertices_56, vertices_280, vertices_776, vertices_112, vertices_560, vertices_208, vertices_336, vertices_592, vertices_656, vertices_608, vertices_448]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

noncomputable def pointPriority : Fin 9 → ℕ := ![14, 19, 16, 22, 24, 25, 26, 27, 28]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 15 else
  if p.val = (false, vertices_781) then 17 else
  if p.val = (false, vertices_613) then 20 else
  if p.val = (false, vertices_453) then 21 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_92) then 18 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_336) then 13 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_92), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
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
  frame := ![0, 3, 5, 6]
  vertex := 7
  face := Sum.inl (indexedFacet 10)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 13) (indexedFacet 10) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 3
  frame := ![1, 2, 3]
  vertex := 5
  face := Sum.inr (indexedPolygon 19)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) (indexedPolygon 19) (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 2, 4]
  vertex := 8
  face := Sum.inl (indexedFacet 5)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 9) (indexedFacet 5) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 3, 4, 6]
  vertex := 8
  face := Sum.inl (indexedFacet 9)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 12) (indexedFacet 9) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![7, 5, 1, 0]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := (indexedFacet 5)
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 9) (indexedFacet 5) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := (indexedFacet 6)
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 2, 3, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 8) (indexedFacet 6) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := (indexedFacet 7)
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 2, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 8) (indexedFacet 7) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := (indexedFacet 8)
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 2, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 10) (indexedFacet 8) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := (indexedFacet 9)
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![0, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 12) (indexedFacet 9) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := (indexedFacet 10)
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![0, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 13) (indexedFacet 10) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := (indexedFacet 11)
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![1, 2, 3, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 19) (indexedFacet 11) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := (indexedFacet 12)
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .oneRow ![1, 2, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 19) (indexedFacet 12) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet8 : boundary.facets := (indexedFacet 13)
noncomputable def cover8 : FacetCoverage heightProof coverFacet8 :=
  .fundamental ![3, 4, 5, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 29) (indexedFacet 13) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0462

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m14e10q1_0472.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0472
open _root_.Nonrational.SharedProjectionVertexSets

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_677, vertices_665, vertices_433, vertices_865, vertices_94, vertices_542, vertices_614, vertices_466, vertices_834, vertices_204, vertices_652, vertices_484, vertices_216] (by decide +kernel)
  polygons := literalFinset [vertices_145, vertices_273, vertices_529, vertices_161, vertices_289, vertices_545, vertices_641, vertices_769, vertices_30, vertices_70, vertices_518, vertices_82, vertices_274, vertices_530, vertices_322, vertices_578, vertices_770, vertices_76, vertices_140, vertices_524, vertices_100, vertices_164, vertices_548, vertices_196, vertices_644, vertices_88, vertices_152, vertices_536, vertices_200, vertices_648, vertices_208, vertices_400, vertices_352, vertices_608, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_677), (false, vertices_665), (false, vertices_433), (false, vertices_865), (true, vertices_30), (true, vertices_70), (true, vertices_518), (true, vertices_82), (true, vertices_322), (true, vertices_578), (true, vertices_76), (true, vertices_140), (true, vertices_524), (true, vertices_100), (true, vertices_196), (true, vertices_88), (true, vertices_200), (true, vertices_208), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

private noncomputable def indexedFacet (j : Fin 14) : boundary.facets := by
  let xs : List (Finset (Fin 10)) := [vertices_787, vertices_677, vertices_665, vertices_433, vertices_865, vertices_94, vertices_542, vertices_614, vertices_466, vertices_834, vertices_204, vertices_652, vertices_484, vertices_216]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

private noncomputable def indexedPolygon (j : Fin 37) : boundary.polygons := by
  let xs : List (Finset (Fin 10)) := [vertices_145, vertices_273, vertices_529, vertices_161, vertices_289, vertices_545, vertices_641, vertices_769, vertices_30, vertices_70, vertices_518, vertices_82, vertices_274, vertices_530, vertices_322, vertices_578, vertices_770, vertices_76, vertices_140, vertices_524, vertices_100, vertices_164, vertices_548, vertices_196, vertices_644, vertices_88, vertices_152, vertices_536, vertices_200, vertices_648, vertices_208, vertices_400, vertices_352, vertices_608, vertices_416, vertices_448, vertices_832]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

noncomputable def pointPriority : Fin 9 → ℕ := ![14, 17, 19, 21, 23, 25, 26, 27, 28]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 15 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_665) then 20 else
  if p.val = (false, vertices_433) then 22 else
  if p.val = (false, vertices_865) then 24 else
  if p.val = (true, vertices_30) then 16 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_448) then 13 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_30), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
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
  frameSize := 3
  frame := ![0, 1, 2]
  vertex := 3
  face := Sum.inr (indexedPolygon 8)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) (indexedPolygon 8) (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 4, 5]
  vertex := 8
  face := Sum.inl (indexedFacet 7)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 9) (indexedFacet 7) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 3, 5, 6]
  vertex := 7
  face := Sum.inl (indexedFacet 8)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 11) (indexedFacet 8) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 4, 5, 6]
  vertex := 7
  face := Sum.inl (indexedFacet 12)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 20) (indexedFacet 12) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![2, 8, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := (indexedFacet 5)
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 8) (indexedFacet 5) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := (indexedFacet 6)
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 1, 2, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 8) (indexedFacet 6) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := (indexedFacet 7)
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 1, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 9) (indexedFacet 7) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := (indexedFacet 8)
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![0, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 11) (indexedFacet 8) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := (indexedFacet 9)
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![0, 5, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 14) (indexedFacet 9) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := (indexedFacet 10)
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![1, 2, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 17) (indexedFacet 10) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := (indexedFacet 11)
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![1, 2, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 18) (indexedFacet 11) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := (indexedFacet 12)
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .oneRow ![1, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 20) (indexedFacet 12) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet8 : boundary.facets := (indexedFacet 13)
noncomputable def cover8 : FacetCoverage heightProof coverFacet8 :=
  .fundamental ![2, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 25) (indexedFacet 13) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0472

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m14e10q1_0478.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0478
open _root_.Nonrational.SharedProjectionVertexSets

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_565, vertices_229, vertices_837, vertices_457, vertices_673, vertices_542, vertices_154, vertices_842, vertices_394, vertices_690, vertices_124, vertices_588, vertices_248] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_517, vertices_161, vertices_545, vertices_193, vertices_321, vertices_385, vertices_641, vertices_769, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_530, vertices_386, vertices_642, vertices_770, vertices_28, vertices_76, vertices_524, vertices_52, vertices_532, vertices_100, vertices_580, vertices_120, vertices_152, vertices_200, vertices_328, vertices_584, vertices_392, vertices_176, vertices_560, vertices_224, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_565), (false, vertices_229), (false, vertices_837), (false, vertices_457), (false, vertices_673), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_530), (true, vertices_28), (true, vertices_76), (true, vertices_524), (true, vertices_120), (true, vertices_152), (true, vertices_584), (true, vertices_176)] (by decide +kernel)
  planeCache_correct := by decide +kernel

private noncomputable def indexedFacet (j : Fin 14) : boundary.facets := by
  let xs : List (Finset (Fin 10)) := [vertices_899, vertices_565, vertices_229, vertices_837, vertices_457, vertices_673, vertices_542, vertices_154, vertices_842, vertices_394, vertices_690, vertices_124, vertices_588, vertices_248]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

private noncomputable def indexedPolygon (j : Fin 37) : boundary.polygons := by
  let xs : List (Finset (Fin 10)) := [vertices_37, vertices_69, vertices_517, vertices_161, vertices_545, vertices_193, vertices_321, vertices_385, vertices_641, vertices_769, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_530, vertices_386, vertices_642, vertices_770, vertices_28, vertices_76, vertices_524, vertices_52, vertices_532, vertices_100, vertices_580, vertices_120, vertices_152, vertices_200, vertices_328, vertices_584, vertices_392, vertices_176, vertices_560, vertices_224, vertices_672, vertices_832]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 15, 19, 22, 23, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 14 else
  if p.val = (false, vertices_565) then 16 else
  if p.val = (false, vertices_229) then 17 else
  if p.val = (false, vertices_837) then 18 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (false, vertices_673) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_120) then 21 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_176) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_673), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_120), by decide +kernel⟩
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
  frame := ![0, 1, 2, 3]
  vertex := 8
  face := Sum.inl (indexedFacet 6)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 10) (indexedFacet 6) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 5, 7]
  vertex := 8
  face := Sum.inl (indexedFacet 8)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 12) (indexedFacet 8) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 3
  frame := ![2, 3, 4]
  vertex := 5
  face := Sum.inr (indexedPolygon 26)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) (indexedPolygon 26) (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 3, 4, 6]
  vertex := 8
  face := Sum.inl (indexedFacet 10)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 14) (indexedFacet 10) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![1, 7, 2, 0]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := (indexedFacet 6)
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 3] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 10) (indexedFacet 6) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := (indexedFacet 7)
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 2, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 10) (indexedFacet 7) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := (indexedFacet 8)
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 2, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 12) (indexedFacet 8) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := (indexedFacet 9)
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 2, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 11) (indexedFacet 9) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := (indexedFacet 10)
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![0, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 14) (indexedFacet 10) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := (indexedFacet 11)
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![1, 2, 3, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 19) (indexedFacet 11) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := (indexedFacet 12)
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .fundamental ![1, 2, 5, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 20) (indexedFacet 12) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := (indexedFacet 13)
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .oneRow ![2, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 26) (indexedFacet 13) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0478

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m14e10q1_0486.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0486
open _root_.Nonrational.SharedProjectionVertexSets

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_597, vertices_805, vertices_453, vertices_713, vertices_566, vertices_314, vertices_538, vertices_458, vertices_650, vertices_802, vertices_124, vertices_364, vertices_600] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_193, vertices_577, vertices_385, vertices_641, vertices_769, vertices_26, vertices_138, vertices_266, vertices_522, vertices_50, vertices_530, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_108, vertices_52, vertices_84, vertices_532, vertices_292, vertices_548, vertices_324, vertices_56, vertices_88, vertices_536, vertices_296, vertices_200, vertices_328, vertices_584, vertices_648, vertices_592, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_597), (false, vertices_805), (false, vertices_453), (false, vertices_713), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_530), (true, vertices_290), (true, vertices_546), (true, vertices_108), (true, vertices_52), (true, vertices_56), (true, vertices_88), (true, vertices_536), (true, vertices_296), (true, vertices_328)] (by decide +kernel)
  planeCache_correct := by decide +kernel

private noncomputable def indexedFacet (j : Fin 14) : boundary.facets := by
  let xs : List (Finset (Fin 10)) := [vertices_899, vertices_597, vertices_805, vertices_453, vertices_713, vertices_566, vertices_314, vertices_538, vertices_458, vertices_650, vertices_802, vertices_124, vertices_364, vertices_600]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

private noncomputable def indexedPolygon (j : Fin 37) : boundary.polygons := by
  let xs : List (Finset (Fin 10)) := [vertices_69, vertices_261, vertices_517, vertices_193, vertices_577, vertices_385, vertices_641, vertices_769, vertices_26, vertices_138, vertices_266, vertices_522, vertices_50, vertices_530, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_108, vertices_52, vertices_84, vertices_532, vertices_292, vertices_548, vertices_324, vertices_56, vertices_88, vertices_536, vertices_296, vertices_200, vertices_328, vertices_584, vertices_648, vertices_592, vertices_800, vertices_448]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

noncomputable def pointPriority : Fin 9 → ℕ := ![14, 19, 16, 23, 24, 25, 26, 27, 28]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 15 else
  if p.val = (false, vertices_597) then 20 else
  if p.val = (false, vertices_805) then 21 else
  if p.val = (false, vertices_453) then 22 else
  if p.val = (false, vertices_713) then 17 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_108) then 18 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_328) then 13 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_108), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 23 => Sum.inl 3
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
  frame := ![0, 1, 3, 4]
  vertex := 8
  face := Sum.inl (indexedFacet 5)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 12) (indexedFacet 5) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 3
  frame := ![1, 2, 4]
  vertex := 5
  face := Sum.inr (indexedPolygon 19)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) (indexedPolygon 19) (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 3, 4]
  vertex := 7
  face := Sum.inl (indexedFacet 6)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 8) (indexedFacet 6) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 5, 6]
  vertex := 7
  face := Sum.inl (indexedFacet 8)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 9) (indexedFacet 8) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![8, 1, 3, 0]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := (indexedFacet 5)
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 3, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 12) (indexedFacet 5) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := (indexedFacet 6)
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 2, 3, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 8) (indexedFacet 6) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := (indexedFacet 7)
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 2, 3, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 8) (indexedFacet 7) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := (indexedFacet 8)
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![0, 2, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 9) (indexedFacet 8) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := (indexedFacet 9)
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![0, 2, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 9) (indexedFacet 9) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := (indexedFacet 10)
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![0, 4, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 14) (indexedFacet 10) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := (indexedFacet 11)
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![1, 2, 3, 4] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 19) (indexedFacet 11) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := (indexedFacet 12)
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .oneRow ![1, 2, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 19) (indexedFacet 12) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet8 : boundary.facets := (indexedFacet 13)
noncomputable def cover8 : FacetCoverage heightProof coverFacet8 :=
  .fundamental ![2, 3, 5, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 27) (indexedFacet 13) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0486

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m14e10q1_0487.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0487
open _root_.Nonrational.SharedProjectionVertexSets

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_837, vertices_793, vertices_465, vertices_737, vertices_62, vertices_526, vertices_614, vertices_538, vertices_434, vertices_674, vertices_316, vertices_780, vertices_484] (by decide +kernel)
  polygons := literalFinset [vertices_145, vertices_273, vertices_529, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_14, vertices_38, vertices_518, vertices_26, vertices_522, vertices_50, vertices_146, vertices_530, vertices_162, vertices_546, vertices_642, vertices_60, vertices_268, vertices_524, vertices_100, vertices_292, vertices_324, vertices_580, vertices_772, vertices_280, vertices_536, vertices_776, vertices_304, vertices_400, vertices_224, vertices_608, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_837), (false, vertices_793), (false, vertices_465), (false, vertices_737), (true, vertices_14), (true, vertices_38), (true, vertices_518), (true, vertices_26), (true, vertices_522), (true, vertices_50), (true, vertices_162), (true, vertices_546), (true, vertices_60), (true, vertices_268), (true, vertices_524), (true, vertices_100), (true, vertices_292), (true, vertices_304), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

private noncomputable def indexedFacet (j : Fin 14) : boundary.facets := by
  let xs : List (Finset (Fin 10)) := [vertices_659, vertices_837, vertices_793, vertices_465, vertices_737, vertices_62, vertices_526, vertices_614, vertices_538, vertices_434, vertices_674, vertices_316, vertices_780, vertices_484]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

private noncomputable def indexedPolygon (j : Fin 37) : boundary.polygons := by
  let xs : List (Finset (Fin 10)) := [vertices_145, vertices_273, vertices_529, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_14, vertices_38, vertices_518, vertices_26, vertices_522, vertices_50, vertices_146, vertices_530, vertices_162, vertices_546, vertices_642, vertices_60, vertices_268, vertices_524, vertices_100, vertices_292, vertices_324, vertices_580, vertices_772, vertices_280, vertices_536, vertices_776, vertices_304, vertices_400, vertices_224, vertices_608, vertices_416, vertices_672, vertices_448]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

noncomputable def pointPriority : Fin 9 → ℕ := ![14, 16, 19, 21, 23, 25, 26, 27, 28]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 15 else
  if p.val = (false, vertices_837) then 17 else
  if p.val = (false, vertices_793) then 20 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (false, vertices_737) then 24 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_60) then 18 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_100) then 10 else
  if p.val = (true, vertices_292) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_60), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
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
  frameSize := 3
  frame := ![1, 2, 3]
  vertex := 4
  face := Sum.inr (indexedPolygon 19)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) (indexedPolygon 19) (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 4, 5]
  vertex := 8
  face := Sum.inl (indexedFacet 7)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 9) (indexedFacet 7) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 3, 4, 6]
  vertex := 7
  face := Sum.inl (indexedFacet 9)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 13) (indexedFacet 9) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 4, 5, 6]
  vertex := 7
  face := Sum.inl (indexedFacet 13)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 22) (indexedFacet 13) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![2, 8, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := (indexedFacet 5)
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 2, 3] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 8) (indexedFacet 5) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := (indexedFacet 6)
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 1, 2, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 8) (indexedFacet 6) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := (indexedFacet 7)
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![0, 1, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 9) (indexedFacet 7) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := (indexedFacet 8)
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 2, 3, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 11) (indexedFacet 8) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := (indexedFacet 9)
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![0, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 13) (indexedFacet 9) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := (indexedFacet 10)
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![0, 4, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 16) (indexedFacet 10) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := (indexedFacet 11)
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![1, 2, 3, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 19) (indexedFacet 11) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := (indexedFacet 12)
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![1, 2, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 20) (indexedFacet 12) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet8 : boundary.facets := (indexedFacet 13)
noncomputable def cover8 : FacetCoverage heightProof coverFacet8 :=
  .oneRow ![1, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 22) (indexedFacet 13) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0487

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m14e10q1_0488.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0488
open _root_.Nonrational.SharedProjectionVertexSets

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_203, vertices_653, vertices_405, vertices_805, vertices_841, vertices_465, vertices_678, vertices_810, vertices_330, vertices_650, vertices_370, vertices_226, vertices_244, vertices_308] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_521, vertices_401, vertices_193, vertices_321, vertices_769, vertices_74, vertices_138, vertices_266, vertices_522, vertices_98, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_642, vertices_52, vertices_148, vertices_276, vertices_164, vertices_292, vertices_548, vertices_644, vertices_328, vertices_648, vertices_776, vertices_112, vertices_304, vertices_208, vertices_336, vertices_224, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_203), (false, vertices_653), (false, vertices_405), (false, vertices_805), (false, vertices_841), (false, vertices_465), (true, vertices_266), (true, vertices_522), (true, vertices_98), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_322), (true, vertices_642), (true, vertices_52), (true, vertices_164), (true, vertices_112), (true, vertices_304), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

private noncomputable def indexedFacet (j : Fin 14) : boundary.facets := by
  let xs : List (Finset (Fin 10)) := [vertices_203, vertices_653, vertices_405, vertices_805, vertices_841, vertices_465, vertices_678, vertices_810, vertices_330, vertices_650, vertices_370, vertices_226, vertices_244, vertices_308]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

private noncomputable def indexedPolygon (j : Fin 37) : boundary.polygons := by
  let xs : List (Finset (Fin 10)) := [vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_521, vertices_401, vertices_193, vertices_321, vertices_769, vertices_74, vertices_138, vertices_266, vertices_522, vertices_98, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_642, vertices_52, vertices_148, vertices_276, vertices_164, vertices_292, vertices_548, vertices_644, vertices_328, vertices_648, vertices_776, vertices_112, vertices_304, vertices_208, vertices_336, vertices_224, vertices_800]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

noncomputable def pointPriority : Fin 9 → ℕ := ![13, 15, 18, 20, 23, 24, 25, 26, 27]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_405) then 21 else
  if p.val = (false, vertices_805) then 17 else
  if p.val = (false, vertices_841) then 19 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_224) then 12 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
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
  frame := ![0, 2, 4, 7]
  vertex := 8
  face := Sum.inl (indexedFacet 7)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 12) (indexedFacet 7) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 1, 4, 6]
  vertex := 8
  face := Sum.inl (indexedFacet 6)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 15) (indexedFacet 6) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 3, 4, 5]
  vertex := 7
  face := Sum.inl (indexedFacet 10)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 14) (indexedFacet 10) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 3, 4, 5]
  vertex := 6
  face := Sum.inl (indexedFacet 12)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 21) (indexedFacet 12) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![2, 8, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := (indexedFacet 6)
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 15) (indexedFacet 6) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := (indexedFacet 7)
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 2, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 12) (indexedFacet 7) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := (indexedFacet 8)
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 2, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 10) (indexedFacet 8) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := (indexedFacet 9)
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 2, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 11) (indexedFacet 9) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := (indexedFacet 10)
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![0, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 14) (indexedFacet 10) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := (indexedFacet 11)
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![0, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 14) (indexedFacet 11) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := (indexedFacet 12)
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![1, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 21) (indexedFacet 12) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet7 : boundary.facets := (indexedFacet 13)
noncomputable def cover7 : FacetCoverage heightProof coverFacet7 :=
  .fundamental ![1, 3, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 21) (indexedFacet 13) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0488

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m14e10q1_0489.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0489
open _root_.Nonrational.SharedProjectionVertexSets

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_163, vertices_707, vertices_771, vertices_781, vertices_617, vertices_241, vertices_902, vertices_418, vertices_348, vertices_716, vertices_436, vertices_212, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_41, vertices_265, vertices_521, vertices_97, vertices_161, vertices_193, vertices_577, vertices_769, vertices_162, vertices_290, vertices_386, vertices_642, vertices_770, vertices_76, vertices_268, vertices_524, vertices_84, vertices_148, vertices_276, vertices_196, vertices_388, vertices_644, vertices_772, vertices_344, vertices_104, vertices_296, vertices_584, vertices_112, vertices_176, vertices_304, vertices_208, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_163), (false, vertices_707), (false, vertices_771), (false, vertices_781), (false, vertices_617), (false, vertices_241), (true, vertices_386), (true, vertices_76), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_196), (true, vertices_388), (true, vertices_644), (true, vertices_344), (true, vertices_304), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

private noncomputable def indexedFacet (j : Fin 14) : boundary.facets := by
  let xs : List (Finset (Fin 10)) := [vertices_299, vertices_163, vertices_707, vertices_771, vertices_781, vertices_617, vertices_241, vertices_902, vertices_418, vertices_348, vertices_716, vertices_436, vertices_212, vertices_376]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

private noncomputable def indexedPolygon (j : Fin 37) : boundary.polygons := by
  let xs : List (Finset (Fin 10)) := [vertices_35, vertices_131, vertices_259, vertices_515, vertices_41, vertices_265, vertices_521, vertices_97, vertices_161, vertices_193, vertices_577, vertices_769, vertices_162, vertices_290, vertices_386, vertices_642, vertices_770, vertices_76, vertices_268, vertices_524, vertices_84, vertices_148, vertices_276, vertices_196, vertices_388, vertices_644, vertices_772, vertices_344, vertices_104, vertices_296, vertices_584, vertices_112, vertices_176, vertices_304, vertices_208, vertices_416, vertices_704]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

noncomputable def pointPriority : Fin 9 → ℕ := ![12, 15, 17, 20, 22, 23, 24, 25, 26]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 13 else
  if p.val = (false, vertices_163) then 0 else
  if p.val = (false, vertices_707) then 14 else
  if p.val = (false, vertices_771) then 1 else
  if p.val = (false, vertices_781) then 16 else
  if p.val = (false, vertices_617) then 18 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_344) then 19 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_416) then 11 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_163), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_344), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
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
  frame := ![0, 1, 6, 7]
  vertex := 8
  face := Sum.inl (indexedFacet 7)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 14) (indexedFacet 7) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 5, 6]
  vertex := 8
  face := Sum.inl (indexedFacet 10)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 17) (indexedFacet 10) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 3
  frame := ![2, 3, 5]
  vertex := 7
  face := Sum.inr (indexedPolygon 27)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) (indexedPolygon 27) (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 3, 4, 6]
  vertex := 7
  face := Sum.inl (indexedFacet 11)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 21) (indexedFacet 11) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 8, 2, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := (indexedFacet 7)
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 1, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 14) (indexedFacet 7) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := (indexedFacet 8)
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 12) (indexedFacet 8) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := (indexedFacet 9)
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .oneRow ![1, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 17) (indexedFacet 9) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := (indexedFacet 10)
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 2, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 17) (indexedFacet 10) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := (indexedFacet 11)
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![1, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 21) (indexedFacet 11) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := (indexedFacet 12)
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .fundamental ![1, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 20) (indexedFacet 12) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := (indexedFacet 13)
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![2, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 27) (indexedFacet 13) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0489

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m14e10q1_0497.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0497
open _root_.Nonrational.SharedProjectionVertexSets

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_675, vertices_291, vertices_653, vertices_309, vertices_149, vertices_241, vertices_370, vertices_610, vertices_834, vertices_412, vertices_844, vertices_472, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_259, vertices_515, vertices_21, vertices_133, vertices_261, vertices_517, vertices_49, vertices_145, vertices_161, vertices_289, vertices_641, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_140, vertices_268, vertices_524, vertices_148, vertices_276, vertices_772, vertices_408, vertices_200, vertices_328, vertices_584, vertices_648, vertices_112, vertices_304, vertices_208, vertices_336, vertices_224, vertices_608, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_675), (false, vertices_291), (false, vertices_653), (false, vertices_309), (false, vertices_149), (false, vertices_241), (true, vertices_98), (true, vertices_322), (true, vertices_578), (true, vertices_268), (true, vertices_408), (true, vertices_200), (true, vertices_328), (true, vertices_584), (true, vertices_336), (true, vertices_608), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

private noncomputable def indexedFacet (j : Fin 14) : boundary.facets := by
  let xs : List (Finset (Fin 10)) := [vertices_775, vertices_675, vertices_291, vertices_653, vertices_309, vertices_149, vertices_241, vertices_370, vertices_610, vertices_834, vertices_412, vertices_844, vertices_472, vertices_744]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

private noncomputable def indexedPolygon (j : Fin 37) : boundary.polygons := by
  let xs : List (Finset (Fin 10)) := [vertices_35, vertices_259, vertices_515, vertices_21, vertices_133, vertices_261, vertices_517, vertices_49, vertices_145, vertices_161, vertices_289, vertices_641, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_140, vertices_268, vertices_524, vertices_148, vertices_276, vertices_772, vertices_408, vertices_200, vertices_328, vertices_584, vertices_648, vertices_112, vertices_304, vertices_208, vertices_336, vertices_224, vertices_608, vertices_672, vertices_832]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

noncomputable def pointPriority : Fin 9 → ℕ := ![12, 15, 18, 20, 22, 23, 24, 25, 26]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 13 else
  if p.val = (false, vertices_675) then 14 else
  if p.val = (false, vertices_291) then 0 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_309) then 17 else
  if p.val = (false, vertices_149) then 1 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_408) then 19 else
  if p.val = (true, vertices_200) then 6 else
  if p.val = (true, vertices_328) then 7 else
  if p.val = (true, vertices_584) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_291), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
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
  frame := ![0, 3, 4, 5]
  vertex := 7
  face := Sum.inl (indexedFacet 7)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 12) (indexedFacet 7) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 3
  frame := ![2, 3, 6]
  vertex := 7
  face := Sum.inr (indexedPolygon 24)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) (indexedPolygon 24) (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 5, 7]
  vertex := 8
  face := Sum.inl (indexedFacet 11)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 19) (indexedFacet 11) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![2, 4, 5, 6]
  vertex := 8
  face := Sum.inl (indexedFacet 13)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 25) (indexedFacet 13) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 3, 1, 2]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := (indexedFacet 7)
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 12) (indexedFacet 7) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := (indexedFacet 8)
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .fundamental ![0, 4, 5, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 12) (indexedFacet 8) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := (indexedFacet 9)
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 5, 7, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 15) (indexedFacet 9) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := (indexedFacet 10)
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 2, 3, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 18) (indexedFacet 10) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := (indexedFacet 11)
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![1, 2, 5, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 19) (indexedFacet 11) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := (indexedFacet 12)
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![2, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 24) (indexedFacet 12) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := (indexedFacet 13)
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![2, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 25) (indexedFacet 13) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0497

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m14e10q1_0498.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0498
open _root_.Nonrational.SharedProjectionVertexSets

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_147, vertices_787, vertices_781, vertices_213, vertices_325, vertices_369, vertices_810, vertices_242, vertices_306, vertices_674, vertices_684, vertices_460, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_515, vertices_69, vertices_133, vertices_261, vertices_517, vertices_81, vertices_145, vertices_273, vertices_321, vertices_769, vertices_50, vertices_146, vertices_274, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_140, vertices_268, vertices_524, vertices_196, vertices_324, vertices_644, vertices_168, vertices_296, vertices_552, vertices_456, vertices_776, vertices_112, vertices_304, vertices_208, vertices_224, vertices_352, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_147), (false, vertices_787), (false, vertices_781), (false, vertices_213), (false, vertices_325), (false, vertices_369), (true, vertices_50), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_140), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_456), (true, vertices_224), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

private noncomputable def indexedFacet (j : Fin 14) : boundary.facets := by
  let xs : List (Finset (Fin 10)) := [vertices_647, vertices_147, vertices_787, vertices_781, vertices_213, vertices_325, vertices_369, vertices_810, vertices_242, vertices_306, vertices_674, vertices_684, vertices_460, vertices_488]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

private noncomputable def indexedPolygon (j : Fin 37) : boundary.polygons := by
  let xs : List (Finset (Fin 10)) := [vertices_19, vertices_131, vertices_515, vertices_69, vertices_133, vertices_261, vertices_517, vertices_81, vertices_145, vertices_273, vertices_321, vertices_769, vertices_50, vertices_146, vertices_274, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_140, vertices_268, vertices_524, vertices_196, vertices_324, vertices_644, vertices_168, vertices_296, vertices_552, vertices_456, vertices_776, vertices_112, vertices_304, vertices_208, vertices_224, vertices_352, vertices_672]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

noncomputable def pointPriority : Fin 9 → ℕ := ![12, 15, 18, 20, 22, 23, 24, 25, 26]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 13 else
  if p.val = (false, vertices_147) then 0 else
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_781) then 16 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_325) then 1 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_456) then 19 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_672) then 11 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_147), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_325), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(true, vertices_456), by decide +kernel⟩
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
  frame := ![0, 3, 4, 5]
  vertex := 6
  face := Sum.inl (indexedFacet 8)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 12) (indexedFacet 8) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 3
  frame := ![2, 5, 6]
  vertex := 7
  face := Sum.inr (indexedPolygon 29)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) (indexedPolygon 29) (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![0, 2, 4, 7]
  vertex := 8
  face := Sum.inl (indexedFacet 7)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 16) (indexedFacet 7) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 2, 4, 6]
  vertex := 8
  face := Sum.inl (indexedFacet 11)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 20) (indexedFacet 11) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![3, 5, 0, 1]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := (indexedFacet 7)
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 2, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 16) (indexedFacet 7) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := (indexedFacet 8)
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 3, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 12) (indexedFacet 8) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := (indexedFacet 9)
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 3, 4, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 12) (indexedFacet 9) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := (indexedFacet 10)
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .fundamental ![0, 4, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 15) (indexedFacet 10) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := (indexedFacet 11)
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .oneRow ![1, 2, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 20) (indexedFacet 11) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := (indexedFacet 12)
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![1, 2, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 20) (indexedFacet 12) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := (indexedFacet 13)
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![2, 4, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 26) (indexedFacet 13) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0498

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m14e10q1_0502.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0502
open _root_.Nonrational.SharedProjectionVertexSets

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_87, vertices_539, vertices_99, vertices_803, vertices_533, vertices_837, vertices_481, vertices_218, vertices_234, vertices_554, vertices_468, vertices_660, vertices_932, vertices_696] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_67, vertices_515, vertices_21, vertices_69, vertices_517, vertices_529, vertices_97, vertices_289, vertices_321, vertices_769, vertices_26, vertices_42, vertices_202, vertices_522, vertices_82, vertices_98, vertices_546, vertices_84, vertices_148, vertices_532, vertices_324, vertices_388, vertices_644, vertices_772, vertices_152, vertices_536, vertices_168, vertices_552, vertices_208, vertices_656, vertices_224, vertices_416, vertices_672, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_87), (false, vertices_539), (false, vertices_99), (false, vertices_803), (false, vertices_533), (false, vertices_837), (false, vertices_481), (true, vertices_42), (true, vertices_202), (true, vertices_148), (true, vertices_388), (true, vertices_644), (true, vertices_152), (true, vertices_168), (true, vertices_552), (true, vertices_208), (true, vertices_656), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

private noncomputable def indexedFacet (j : Fin 14) : boundary.facets := by
  let xs : List (Finset (Fin 10)) := [vertices_87, vertices_539, vertices_99, vertices_803, vertices_533, vertices_837, vertices_481, vertices_218, vertices_234, vertices_554, vertices_468, vertices_660, vertices_932, vertices_696]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

private noncomputable def indexedPolygon (j : Fin 37) : boundary.polygons := by
  let xs : List (Finset (Fin 10)) := [vertices_19, vertices_35, vertices_67, vertices_515, vertices_21, vertices_69, vertices_517, vertices_529, vertices_97, vertices_289, vertices_321, vertices_769, vertices_26, vertices_42, vertices_202, vertices_522, vertices_82, vertices_98, vertices_546, vertices_84, vertices_148, vertices_532, vertices_324, vertices_388, vertices_644, vertices_772, vertices_152, vertices_536, vertices_168, vertices_552, vertices_208, vertices_656, vertices_224, vertices_416, vertices_672, vertices_800, vertices_448]
  have hj : j.val < xs.length := j.isLt
  refine ⟨xs[j.val]'hj, ?_⟩
  change xs[j.val]'hj ∈ xs
  exact List.getElem_mem hj

noncomputable def pointPriority : Fin 9 → ℕ := ![15, 12, 19, 20, 21, 23, 24, 25, 26]
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_87) then 13 else
  if p.val = (false, vertices_539) then 16 else
  if p.val = (false, vertices_99) then 0 else
  if p.val = (false, vertices_803) then 17 else
  if p.val = (false, vertices_533) then 1 else
  if p.val = (false, vertices_837) then 14 else
  if p.val = (false, vertices_481) then 22 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_202) then 18 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_672) then 11 else
  0
noncomputable def priority : Node boundary → ℕ := Sum.elim pointPriority planePriority

noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_99), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_87), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
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
  face := Sum.inr (indexedPolygon 14)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.polygon (by decide +kernel) (by decide +kernel) (indexedPolygon 14) (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row1 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 3, 5, 6]
  vertex := 7
  face := Sum.inl (indexedFacet 10)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 19) (indexedFacet 10) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row2 : HeightRow boundary where
  frameSize := 4
  frame := ![1, 4, 6, 7]
  vertex := 8
  face := Sum.inl (indexedFacet 12)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 23) (indexedFacet 12) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def row3 : HeightRow boundary where
  frameSize := 4
  frame := ![2, 3, 4, 6]
  vertex := 8
  face := Sum.inl (indexedFacet 13)
  avoids := by decide +kernel
  frame_mem := by decide +kernel
  vertex_mem := by decide +kernel
  vertex_outside_frame := by decide +kernel
  frame_certificate := FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 26) (indexedFacet 13) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)
  spanning_certificate := by decide +kernel

noncomputable def rows : Fin 4 → HeightRow boundary := ![row0, row1, row2, row3]
noncomputable def pivot : Fin 4 → Fin 9 := ![0, 5, 1, 2]
noncomputable def heightProof : HeightCertificate boundary 4 :=
  heightCertificateOfChecks boundary rows pivot (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet0 : boundary.facets := (indexedFacet 7)
noncomputable def cover0 : FacetCoverage heightProof coverFacet0 :=
  .oneRow ![0, 2, 3, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 12) (indexedFacet 7) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet1 : boundary.facets := (indexedFacet 8)
noncomputable def cover1 : FacetCoverage heightProof coverFacet1 :=
  .oneRow ![0, 2, 4, 5] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 13) (indexedFacet 8) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 0 (by decide +kernel)

noncomputable def coverFacet2 : boundary.facets := (indexedFacet 9)
noncomputable def cover2 : FacetCoverage heightProof coverFacet2 :=
  .fundamental ![0, 2, 4, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 13) (indexedFacet 9) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet3 : boundary.facets := (indexedFacet 10)
noncomputable def cover3 : FacetCoverage heightProof coverFacet3 :=
  .oneRow ![1, 3, 5, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 19) (indexedFacet 10) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel)

noncomputable def coverFacet4 : boundary.facets := (indexedFacet 11)
noncomputable def cover4 : FacetCoverage heightProof coverFacet4 :=
  .fundamental ![1, 3, 6, 8] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 20) (indexedFacet 11) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

noncomputable def coverFacet5 : boundary.facets := (indexedFacet 12)
noncomputable def cover5 : FacetCoverage heightProof coverFacet5 :=
  .oneRow ![1, 4, 6, 7] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 23) (indexedFacet 12) (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

noncomputable def coverFacet6 : boundary.facets := (indexedFacet 13)
noncomputable def cover6 : FacetCoverage heightProof coverFacet6 :=
  .oneRow ![2, 3, 4, 6] (FrameCertificate.facial (by decide +kernel) (by decide +kernel) (indexedPolygon 26) (indexedFacet 13) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel) 3 (by decide +kernel)

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

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0502

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_2373 : Certifies 2373 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0388.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2374 : Certifies 2374 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0392.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2375 : Certifies 2375 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0394.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2376 : Certifies 2376 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0395.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2377 : Certifies 2377 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0396.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2378 : Certifies 2378 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0397.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2379 : Certifies 2379 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0398.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2380 : Certifies 2380 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0427.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2381 : Certifies 2381 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0428.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2382 : Certifies 2382 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0433.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2383 : Certifies 2383 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0434.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2384 : Certifies 2384 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0435.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2385 : Certifies 2385 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0436.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2386 : Certifies 2386 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0448.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2387 : Certifies 2387 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0449.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2388 : Certifies 2388 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0450.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2389 : Certifies 2389 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0455.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2390 : Certifies 2390 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0457.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2391 : Certifies 2391 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0460.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2392 : Certifies 2392 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0461.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2393 : Certifies 2393 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0462.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2394 : Certifies 2394 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0472.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2395 : Certifies 2395 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0478.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2396 : Certifies 2396 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0486.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2397 : Certifies 2397 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0487.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2398 : Certifies 2398 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0488.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2399 : Certifies 2399 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0489.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2400 : Certifies 2400 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0497.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2401 : Certifies 2401 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0498.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2402 : Certifies 2402 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0502.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B078 (j : Fin 30) :
    Certifies (2373 + j.val) := by
  fin_cases j
  · exact projection_2373
  · exact projection_2374
  · exact projection_2375
  · exact projection_2376
  · exact projection_2377
  · exact projection_2378
  · exact projection_2379
  · exact projection_2380
  · exact projection_2381
  · exact projection_2382
  · exact projection_2383
  · exact projection_2384
  · exact projection_2385
  · exact projection_2386
  · exact projection_2387
  · exact projection_2388
  · exact projection_2389
  · exact projection_2390
  · exact projection_2391
  · exact projection_2392
  · exact projection_2393
  · exact projection_2394
  · exact projection_2395
  · exact projection_2396
  · exact projection_2397
  · exact projection_2398
  · exact projection_2399
  · exact projection_2400
  · exact projection_2401
  · exact projection_2402

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
