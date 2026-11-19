module
public meta import LowerSchemas.Batches
public meta import ProjectionVertexSets
public import TerminalGeometry
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Papers.FiniteProjectionChecks

section
set_option debug.skipKernelTC false

section BundlePart0
/- Source: ProjectionCertificates/R_multi_six_0014.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0014

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 587, 725, 809, 689, 398, 454, 842, 156, 440, 992, 7, 11, 67, 21, 69, 41, 521, 49, 657, 545, 577, 14, 70, 390, 586, 266, 322, 28, 140, 148, 196, 56, 152, 296, 392, 776, 176, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_587, vertices_725, vertices_809, vertices_689, vertices_398, vertices_454, vertices_842, vertices_156, vertices_440, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_41, vertices_521, vertices_49, vertices_657, vertices_545, vertices_577, vertices_14, vertices_70, vertices_390, vertices_586, vertices_266, vertices_322, vertices_28, vertices_140, vertices_148, vertices_196, vertices_56, vertices_152, vertices_296, vertices_392, vertices_776, vertices_176, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_587), (false, vertices_725), (false, vertices_809), (false, vertices_689), (true, vertices_390), (true, vertices_266), (true, vertices_322), (true, vertices_140), (true, vertices_152), (true, vertices_392), (true, vertices_416), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 14 16 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_587) then 10 else
  if p.val = (false, vertices_725) then 17 else
  if p.val = (false, vertices_809) then 15 else
  if p.val = (false, vertices_689) then 18 else
  if p.val = (true, vertices_390) then 11 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_152) then 4 else
  if p.val = (true, vertices_392) then 5 else
  if p.val = (true, vertices_416) then 6 else
  if p.val = (true, vertices_448) then 7 else
  if p.val = (true, vertices_832) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_725), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 7 390
cert_row_2 1 0 2 5 8 586
cert_row_4 2 2 3 4 6 7 440 56 3
cert_row_4 3 4 5 6 7 8 992 416 1
cert_rows
cert_pivot_2 1 0 2 4
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 842
cert_cover_5 2 1 0 2 5 7 586 842 3
cert_coverFacet 3 156
cert_cover_2 3 2 1 3 6 28 156 3
cert_coverFacet 4 440
cert_cover_5 4 2 2 3 4 6 56 440 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 416 992 1
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0014

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_multi_six_0015.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0015

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 843, 597, 809, 689, 398, 454, 156, 724, 440, 992, 7, 11, 67, 21, 69, 41, 777, 49, 529, 545, 577, 14, 70, 390, 266, 322, 28, 140, 596, 148, 196, 56, 152, 296, 392, 176, 656, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_843, vertices_597, vertices_809, vertices_689, vertices_398, vertices_454, vertices_156, vertices_724, vertices_440, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_41, vertices_777, vertices_49, vertices_529, vertices_545, vertices_577, vertices_14, vertices_70, vertices_390, vertices_266, vertices_322, vertices_28, vertices_140, vertices_596, vertices_148, vertices_196, vertices_56, vertices_152, vertices_296, vertices_392, vertices_176, vertices_656, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_843), (false, vertices_597), (false, vertices_809), (false, vertices_689), (true, vertices_390), (true, vertices_140), (true, vertices_148), (true, vertices_196), (true, vertices_152), (true, vertices_392), (true, vertices_416), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 11 14 17 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_843) then 15 else
  if p.val = (false, vertices_597) then 13 else
  if p.val = (false, vertices_809) then 16 else
  if p.val = (false, vertices_689) then 18 else
  if p.val = (true, vertices_390) then 10 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_148) then 2 else
  if p.val = (true, vertices_196) then 3 else
  if p.val = (true, vertices_152) then 4 else
  if p.val = (true, vertices_392) then 5 else
  if p.val = (true, vertices_416) then 6 else
  if p.val = (true, vertices_448) then 7 else
  if p.val = (true, vertices_704) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_843), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 7 390
cert_row_2 1 1 3 5 8 596
cert_row_4 2 2 3 4 6 7 440 56 3
cert_row_4 3 4 5 6 7 8 992 416 1
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 156
cert_cover_2 2 2 1 3 6 28 156 3
cert_coverFacet 3 724
cert_cover_5 3 1 1 3 5 6 596 724 3
cert_coverFacet 4 440
cert_cover_5 4 2 2 3 4 6 56 440 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 416 992 1
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0015

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_multi_six_0016.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0016

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 395, 963, 205, 598, 794, 428, 244, 824, 752, 928, 7, 11, 67, 387, 13, 69, 137, 193, 22, 70, 26, 266, 530, 578, 770, 44, 140, 52, 84, 164, 196, 56, 792, 296, 392, 240, 560, 592, 416, 672, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_395, vertices_963, vertices_205, vertices_598, vertices_794, vertices_428, vertices_244, vertices_824, vertices_752, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_387, vertices_13, vertices_69, vertices_137, vertices_193, vertices_22, vertices_70, vertices_26, vertices_266, vertices_530, vertices_578, vertices_770, vertices_44, vertices_140, vertices_52, vertices_84, vertices_164, vertices_196, vertices_56, vertices_792, vertices_296, vertices_392, vertices_240, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_395), (false, vertices_963), (false, vertices_205), (true, vertices_530), (true, vertices_84), (true, vertices_164), (true, vertices_792), (true, vertices_296), (true, vertices_240), (true, vertices_560), (true, vertices_592), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 15 17 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_395) then 11 else
  if p.val = (false, vertices_963) then 21 else
  if p.val = (false, vertices_205) then 14 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_792) then 16 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_240) then 18 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_592) then 6 else
  if p.val = (true, vertices_416) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_800) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(true, vertices_792), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_963), by decide +kernel⟩
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 8 598 22 3
cert_row_2 1 3 4 5 6 240
cert_row_2 2 2 3 7 8 792
cert_row_4 3 1 2 4 6 7 428 44 3
cert_rows
cert_pivot_2 0 5 3 1
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 22 598 3
cert_coverFacet 1 794
cert_cover_5 1 2 0 2 3 7 26 794 3
cert_coverFacet 2 428
cert_cover_5 2 3 1 2 4 6 44 428 3
cert_coverFacet 3 244
cert_cover_5 3 1 1 3 4 5 52 244 3
cert_coverFacet 4 824
cert_cover_5 4 2 2 3 4 7 56 824 3
cert_coverFacet 5 752
cert_cover_5 5 1 3 4 5 8 240 752 3
cert_coverFacet 6 928
cert_cover_2 6 6 4 7 8 416 928 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0016

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_multi_six_0017.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0017

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 587, 405, 617, 241, 782, 838, 284, 452, 952, 992, 7, 11, 67, 21, 133, 41, 585, 49, 145, 97, 193, 14, 70, 774, 522, 578, 28, 268, 276, 196, 324, 388, 56, 280, 552, 776, 176, 400, 224, 608, 928, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_587, vertices_405, vertices_617, vertices_241, vertices_782, vertices_838, vertices_284, vertices_452, vertices_952, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_133, vertices_41, vertices_585, vertices_49, vertices_145, vertices_97, vertices_193, vertices_14, vertices_70, vertices_774, vertices_522, vertices_578, vertices_28, vertices_268, vertices_276, vertices_196, vertices_324, vertices_388, vertices_56, vertices_280, vertices_552, vertices_776, vertices_176, vertices_400, vertices_224, vertices_608, vertices_928, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_587), (false, vertices_405), (false, vertices_617), (false, vertices_241), (true, vertices_774), (true, vertices_268), (true, vertices_324), (true, vertices_280), (true, vertices_776), (true, vertices_928), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 6 9 17 19 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 10 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_587) then 7 else
  if p.val = (false, vertices_405) then 11 else
  if p.val = (false, vertices_617) then 8 else
  if p.val = (false, vertices_241) then 12 else
  if p.val = (true, vertices_774) then 15 else
  if p.val = (true, vertices_268) then 0 else
  if p.val = (true, vertices_324) then 1 else
  if p.val = (true, vertices_280) then 2 else
  if p.val = (true, vertices_776) then 3 else
  if p.val = (true, vertices_928) then 18 else
  if p.val = (true, vertices_448) then 4 else
  if p.val = (true, vertices_832) then 5 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 6 => Sum.inl 2
  | 7 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 8 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 9 => Sum.inl 3
  | 10 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
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

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 7 8 774
cert_row_4 1 2 3 4 6 7 952 56 3
cert_row_4 2 2 3 4 6 8 952 56 3
cert_rows_3
cert_pivot_3 7 0 2
cert_heightProof 3
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 838
cert_cover_5 1 0 0 1 5 7 70 838 3
cert_coverFacet 2 284
cert_cover_2 2 2 1 3 7 28 284 3
cert_coverFacet 3 452
cert_cover_2 3 5 1 6 7 196 452 3
cert_coverFacet 4 952
cert_cover_2 4 3 2 4 6 56 952 3
cert_coverFacet 5 992
cert_cover 5 6 3 4 5 3 2 7 4 224 992 928 56 952 6
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0017

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_multi_six_0018.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0018

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 397, 961, 598, 794, 834, 428, 756, 824, 928, 7, 11, 67, 13, 133, 265, 193, 321, 385, 22, 70, 26, 266, 530, 322, 578, 770, 44, 396, 52, 596, 164, 196, 56, 792, 296, 560, 416, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_397, vertices_961, vertices_598, vertices_794, vertices_834, vertices_428, vertices_756, vertices_824, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_266, vertices_530, vertices_322, vertices_578, vertices_770, vertices_44, vertices_396, vertices_52, vertices_596, vertices_164, vertices_196, vertices_56, vertices_792, vertices_296, vertices_560, vertices_416, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_397), (false, vertices_961), (true, vertices_530), (true, vertices_578), (true, vertices_770), (true, vertices_596), (true, vertices_164), (true, vertices_792), (true, vertices_296), (true, vertices_560), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 16 18 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_199) then 10 else
  if p.val = (false, vertices_331) then 11 else
  if p.val = (false, vertices_397) then 14 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_530) then 0 else
  if p.val = (true, vertices_578) then 1 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_596) then 15 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_792) then 17 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_416) then 6 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_800) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_596), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(true, vertices_792), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 4 6 5 756 52 3
cert_row_4 1 1 3 4 6 8 756 52 3
cert_row_2 2 1 2 6 7 396
cert_row_2 3 2 3 7 8 792
cert_rows
cert_pivot_2 5 4 1 2
cert_heightProof 4
cert_coverFacet 0 598
cert_cover 0 3 3 0 1 3 1 5 4 22 598 596 52 756 6
cert_coverFacet 1 794
cert_cover_5 1 3 0 2 3 7 26 794 3
cert_coverFacet 2 834
cert_cover_2 2 5 0 7 8 322 834 3
cert_coverFacet 3 428
cert_cover_5 3 2 1 2 4 6 44 428 3
cert_coverFacet 4 756
cert_cover_2 4 3 1 4 6 52 756 3
cert_coverFacet 5 824
cert_cover_5 5 3 2 3 4 7 56 824 3
cert_coverFacet 6 928
cert_cover_2 6 6 4 7 8 416 928 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0018

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_multi_six_0019.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0019

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 597, 425, 753, 334, 962, 540, 844, 824, 928, 7, 11, 131, 21, 69, 41, 393, 49, 593, 161, 193, 14, 70, 266, 194, 322, 386, 28, 332, 524, 532, 580, 56, 536, 296, 776, 560, 416, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_597, vertices_425, vertices_753, vertices_334, vertices_962, vertices_540, vertices_844, vertices_824, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_69, vertices_41, vertices_393, vertices_49, vertices_593, vertices_161, vertices_193, vertices_14, vertices_70, vertices_266, vertices_194, vertices_322, vertices_386, vertices_28, vertices_332, vertices_524, vertices_532, vertices_580, vertices_56, vertices_536, vertices_296, vertices_776, vertices_560, vertices_416, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_597), (false, vertices_425), (false, vertices_753), (true, vertices_322), (true, vertices_332), (true, vertices_524), (true, vertices_536), (true, vertices_776), (true, vertices_800), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 7 9 12 15 17 19 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 10 else
  if p.val = (false, vertices_199) then 8 else
  if p.val = (false, vertices_395) then 13 else
  if p.val = (false, vertices_597) then 16 else
  if p.val = (false, vertices_425) then 14 else
  if p.val = (false, vertices_753) then 18 else
  if p.val = (true, vertices_322) then 0 else
  if p.val = (true, vertices_332) then 11 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_536) then 2 else
  if p.val = (true, vertices_776) then 3 else
  if p.val = (true, vertices_800) then 4 else
  if p.val = (true, vertices_832) then 5 else
  if p.val = (true, vertices_896) then 6 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 7 => Sum.inl 0
  | 8 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_332), by decide +kernel⟩
  | 12 => Sum.inl 2
  | 13 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 17 => Sum.inl 4
  | 18 => Sum.inr ⟨(false, vertices_753), by decide +kernel⟩
  | 19 => Sum.inl 5
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 5 7 332
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 2 3 4 7 8 824 56 3
cert_rows_3
cert_pivot_3 0 1 2
cert_heightProof 3
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 5 14 334 3
cert_coverFacet 1 962
cert_cover_5 1 1 0 5 6 7 194 962 3
cert_coverFacet 2 540
cert_cover_2 2 2 1 3 8 28 540 3
cert_coverFacet 3 844
cert_cover_5 3 0 1 2 5 8 332 844 3
cert_coverFacet 4 824
cert_cover_5 4 2 2 3 4 7 56 824 3
cert_coverFacet 5 928
cert_cover_2 5 6 4 7 8 416 928 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0019

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_multi_six_0020.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0020

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 651, 85, 681, 497, 782, 838, 706, 348, 824, 992, 7, 11, 131, 21, 69, 41, 649, 49, 81, 161, 193, 14, 70, 774, 522, 194, 578, 642, 28, 268, 84, 324, 56, 280, 552, 776, 304, 336, 480, 672, 800, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_651, vertices_85, vertices_681, vertices_497, vertices_782, vertices_838, vertices_706, vertices_348, vertices_824, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_69, vertices_41, vertices_649, vertices_49, vertices_81, vertices_161, vertices_193, vertices_14, vertices_70, vertices_774, vertices_522, vertices_194, vertices_578, vertices_642, vertices_28, vertices_268, vertices_84, vertices_324, vertices_56, vertices_280, vertices_552, vertices_776, vertices_304, vertices_336, vertices_480, vertices_672, vertices_800, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_651), (false, vertices_85), (false, vertices_681), (false, vertices_497), (true, vertices_774), (true, vertices_578), (true, vertices_268), (true, vertices_324), (true, vertices_280), (true, vertices_776), (true, vertices_800), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 9 12 18 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_199) then 15 else
  if p.val = (false, vertices_651) then 10 else
  if p.val = (false, vertices_85) then 0 else
  if p.val = (false, vertices_681) then 11 else
  if p.val = (false, vertices_497) then 19 else
  if p.val = (true, vertices_774) then 16 else
  if p.val = (true, vertices_578) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_324) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_800) then 6 else
  if p.val = (true, vertices_704) then 7 else
  if p.val = (true, vertices_832) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_85), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 9 => Sum.inl 2
  | 10 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 12 => Sum.inl 3
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inl 4
  | 19 => Sum.inr ⟨(false, vertices_497), by decide +kernel⟩
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 4 5 6 7 480
cert_row_2 1 0 1 7 8 774
cert_row_4 2 1 2 3 5 7 348 28 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 6 0 1 2
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 14 782 3
cert_coverFacet 1 838
cert_cover_5 1 1 0 1 5 7 70 838 3
cert_coverFacet 2 706
cert_cover_2 2 5 0 6 8 194 706 3
cert_coverFacet 3 348
cert_cover_5 3 2 1 2 3 5 28 348 3
cert_coverFacet 4 824
cert_cover_5 4 3 2 3 4 7 56 824 3
cert_coverFacet 5 992
cert_cover_5 5 0 4 5 6 8 480 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0020

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_multi_six_0021.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0021

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 331, 661, 361, 817, 78, 454, 220, 900, 760, 992, 7, 11, 259, 21, 517, 41, 329, 49, 529, 289, 769, 14, 70, 262, 74, 322, 28, 76, 148, 196, 388, 644, 772, 56, 216, 104, 560, 656, 736, 352, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_331, vertices_661, vertices_361, vertices_817, vertices_78, vertices_454, vertices_220, vertices_900, vertices_760, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_517, vertices_41, vertices_329, vertices_49, vertices_529, vertices_289, vertices_769, vertices_14, vertices_70, vertices_262, vertices_74, vertices_322, vertices_28, vertices_76, vertices_148, vertices_196, vertices_388, vertices_644, vertices_772, vertices_56, vertices_216, vertices_104, vertices_560, vertices_656, vertices_736, vertices_352, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_331), (false, vertices_661), (false, vertices_361), (false, vertices_817), (true, vertices_70), (true, vertices_76), (true, vertices_196), (true, vertices_388), (true, vertices_216), (true, vertices_736), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 6 8 14 11 17 19 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 9 else
  if p.val = (false, vertices_775) then 7 else
  if p.val = (false, vertices_331) then 15 else
  if p.val = (false, vertices_661) then 10 else
  if p.val = (false, vertices_361) then 16 else
  if p.val = (false, vertices_817) then 12 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_76) then 1 else
  if p.val = (true, vertices_196) then 2 else
  if p.val = (true, vertices_388) then 3 else
  if p.val = (true, vertices_216) then 13 else
  if p.val = (true, vertices_736) then 18 else
  if p.val = (true, vertices_448) then 4 else
  if p.val = (true, vertices_896) then 5 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 6 => Sum.inl 0
  | 7 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 8 => Sum.inl 1
  | 9 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 11 => Sum.inl 3
  | 12 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 17 => Sum.inl 4
  | 18 => Sum.inr ⟨(true, vertices_736), by decide +kernel⟩
  | 19 => Sum.inl 5
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 70 3
cert_row_4 1 2 3 4 5 6 760 56 3
cert_row_4 2 2 3 4 5 8 760 56 3
cert_rows_3
cert_pivot_3 6 0 2
cert_heightProof 3
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 220
cert_cover 2 3 3 1 2 3 2 5 4 28 220 216 56 760 5
cert_coverFacet 3 900
cert_cover_2 3 6 1 7 8 388 900 3
cert_coverFacet 4 760
cert_cover_2 4 3 2 4 5 56 760 3
cert_coverFacet 5 992
cert_cover 5 6 3 4 5 3 2 7 4 736 992 736 56 760 5
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0021

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_multi_six_0022.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0022

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 331, 533, 873, 689, 78, 454, 220, 916, 248, 992, 7, 11, 259, 21, 517, 41, 329, 49, 529, 545, 769, 14, 70, 262, 74, 322, 28, 76, 148, 532, 196, 388, 772, 56, 216, 104, 176, 656, 224, 864, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_331, vertices_533, vertices_873, vertices_689, vertices_78, vertices_454, vertices_220, vertices_916, vertices_248, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_517, vertices_41, vertices_329, vertices_49, vertices_529, vertices_545, vertices_769, vertices_14, vertices_70, vertices_262, vertices_74, vertices_322, vertices_28, vertices_76, vertices_148, vertices_532, vertices_196, vertices_388, vertices_772, vertices_56, vertices_216, vertices_104, vertices_176, vertices_656, vertices_224, vertices_864, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_331), (false, vertices_533), (false, vertices_873), (false, vertices_689), (true, vertices_70), (true, vertices_76), (true, vertices_148), (true, vertices_196), (true, vertices_388), (true, vertices_216), (true, vertices_224), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 11 16 13 18 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_775) then 10 else
  if p.val = (false, vertices_331) then 17 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_873) then 19 else
  if p.val = (false, vertices_689) then 14 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_388) then 5 else
  if p.val = (true, vertices_216) then 15 else
  if p.val = (true, vertices_224) then 6 else
  if p.val = (true, vertices_448) then 7 else
  if p.val = (true, vertices_896) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inl 3
  | 14 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inr ⟨(false, vertices_873), by decide +kernel⟩
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 5 6 216
cert_row_2 1 4 5 7 8 864
cert_row_4 2 0 1 5 6 7 454 70 3
cert_row_4 3 1 3 6 7 8 916 148 3
cert_rows
cert_pivot_2 2 4 0 1
cert_heightProof 4
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 454
cert_cover_5 1 2 0 1 5 6 70 454 3
cert_coverFacet 2 220
cert_cover_5 2 0 1 2 3 5 28 220 3
cert_coverFacet 3 916
cert_cover_5 3 3 1 3 6 7 148 916 3
cert_coverFacet 4 248
cert_cover_5 4 0 2 3 4 5 56 248 3
cert_coverFacet 5 992
cert_cover_5 5 1 4 5 6 7 224 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0022

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_multi_six_0023.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0023

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 587, 213, 809, 753, 782, 454, 834, 412, 440, 992, 7, 11, 67, 21, 69, 41, 521, 49, 209, 545, 577, 14, 70, 262, 522, 322, 578, 770, 28, 268, 148, 196, 388, 56, 408, 296, 776, 176, 736, 416, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_587, vertices_213, vertices_809, vertices_753, vertices_782, vertices_454, vertices_834, vertices_412, vertices_440, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_41, vertices_521, vertices_49, vertices_209, vertices_545, vertices_577, vertices_14, vertices_70, vertices_262, vertices_522, vertices_322, vertices_578, vertices_770, vertices_28, vertices_268, vertices_148, vertices_196, vertices_388, vertices_56, vertices_408, vertices_296, vertices_776, vertices_176, vertices_736, vertices_416, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_587), (false, vertices_213), (false, vertices_809), (false, vertices_753), (true, vertices_262), (true, vertices_322), (true, vertices_770), (true, vertices_268), (true, vertices_388), (true, vertices_408), (true, vertices_416), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 11 13 16 18 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_587) then 10 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_809) then 14 else
  if p.val = (false, vertices_753) then 19 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_388) then 5 else
  if p.val = (true, vertices_408) then 15 else
  if p.val = (true, vertices_416) then 6 else
  if p.val = (true, vertices_448) then 7 else
  if p.val = (true, vertices_832) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inr ⟨(false, vertices_753), by decide +kernel⟩
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 4 5 6 8 736
cert_row_2 1 2 3 6 7 408
cert_row_4 2 0 1 2 7 8 782 14 3
cert_row_4 3 0 1 5 6 7 454 70 3
cert_rows
cert_pivot_2 4 3 2 0
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 2 0 1 2 7 14 782 3
cert_coverFacet 1 454
cert_cover_5 1 3 0 1 5 6 70 454 3
cert_coverFacet 2 834
cert_cover_2 2 5 0 7 8 322 834 3
cert_coverFacet 3 412
cert_cover_5 3 1 1 2 3 6 28 412 3
cert_coverFacet 4 440
cert_cover_5 4 1 2 3 4 6 56 440 3
cert_coverFacet 5 992
cert_cover_5 5 0 4 5 6 7 736 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0023

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_multi_six_0024.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0024

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 523, 835, 213, 617, 241, 782, 454, 412, 952, 992, 7, 11, 67, 515, 21, 69, 41, 521, 49, 209, 97, 577, 14, 70, 262, 522, 322, 770, 28, 268, 148, 196, 388, 56, 408, 552, 776, 176, 224, 608, 928, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_523, vertices_835, vertices_213, vertices_617, vertices_241, vertices_782, vertices_454, vertices_412, vertices_952, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_515, vertices_21, vertices_69, vertices_41, vertices_521, vertices_49, vertices_209, vertices_97, vertices_577, vertices_14, vertices_70, vertices_262, vertices_522, vertices_322, vertices_770, vertices_28, vertices_268, vertices_148, vertices_196, vertices_388, vertices_56, vertices_408, vertices_552, vertices_776, vertices_176, vertices_224, vertices_608, vertices_928, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_523), (false, vertices_835), (false, vertices_213), (false, vertices_617), (false, vertices_241), (true, vertices_262), (true, vertices_268), (true, vertices_388), (true, vertices_408), (true, vertices_776), (true, vertices_928), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 7 9 11 14 17 19 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 10 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_523) then 1 else
  if p.val = (false, vertices_835) then 8 else
  if p.val = (false, vertices_213) then 15 else
  if p.val = (false, vertices_617) then 12 else
  if p.val = (false, vertices_241) then 16 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_408) then 13 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_928) then 18 else
  if p.val = (true, vertices_448) then 6 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_523), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 7 => Sum.inl 0
  | 8 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 11 => Sum.inl 2
  | 12 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 17 => Sum.inl 4
  | 18 => Sum.inr ⟨(true, vertices_928), by decide +kernel⟩
  | 19 => Sum.inl 5
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 70 3
cert_row_4 1 0 1 2 7 8 782 14 3
cert_row_4 2 2 3 4 6 7 952 56 3
cert_row_4 3 2 3 4 6 8 952 56 3
cert_rows
cert_pivot_2 5 0 7 2
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 14 782 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 412
cert_cover 2 3 3 1 2 3 2 6 4 28 412 408 56 952 6
cert_coverFacet 3 952
cert_cover_2 3 3 2 4 6 56 952 3
cert_coverFacet 4 992
cert_cover 4 6 3 4 5 3 2 7 4 224 992 928 56 952 6
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0024

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_multi_six_0025.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0025

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 213, 921, 526, 838, 620, 244, 696, 992, 7, 11, 67, 259, 21, 69, 25, 777, 145, 193, 385, 14, 70, 518, 522, 322, 770, 44, 524, 52, 212, 100, 580, 56, 664, 552, 176, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_213, vertices_921, vertices_526, vertices_838, vertices_620, vertices_244, vertices_696, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_25, vertices_777, vertices_145, vertices_193, vertices_385, vertices_14, vertices_70, vertices_518, vertices_522, vertices_322, vertices_770, vertices_44, vertices_524, vertices_52, vertices_212, vertices_100, vertices_580, vertices_56, vertices_664, vertices_552, vertices_176, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_213), (false, vertices_921), (true, vertices_518), (true, vertices_524), (true, vertices_100), (true, vertices_580), (true, vertices_552), (true, vertices_176), (true, vertices_224), (true, vertices_608), (true, vertices_672), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_451) then 12 else
  if p.val = (false, vertices_213) then 15 else
  if p.val = (false, vertices_921) then 19 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_580) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_224) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_921), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 7 8 838 70 3
cert_row_4 1 4 5 6 7 8 992 224 3
cert_row_4 2 1 2 4 5 8 620 44 3
cert_row_2 3 2 3 6 8 664
cert_row_2 4 1 3 5 6 212
cert_rows_2
cert_pivot 0 7 4 2 1
cert_heightProof 5
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 838
cert_cover_5 1 0 0 1 5 7 70 838 3
cert_coverFacet 2 620
cert_cover_5 2 2 1 2 4 5 44 620 3
cert_coverFacet 3 244
cert_cover_5 3 4 1 3 4 5 52 244 3
cert_coverFacet 4 696
cert_cover_5 4 3 2 3 4 6 56 696 3
cert_coverFacet 5 992
cert_cover_5 5 1 4 5 6 7 224 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 5 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0025

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_multi_six_0026.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0026

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 845, 214, 538, 914, 620, 244, 696, 992, 7, 11, 67, 259, 13, 69, 777, 321, 22, 70, 26, 522, 146, 530, 194, 386, 770, 44, 588, 52, 212, 100, 56, 536, 552, 176, 656, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_845, vertices_214, vertices_538, vertices_914, vertices_620, vertices_244, vertices_696, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_69, vertices_777, vertices_321, vertices_22, vertices_70, vertices_26, vertices_522, vertices_146, vertices_530, vertices_194, vertices_386, vertices_770, vertices_44, vertices_588, vertices_52, vertices_212, vertices_100, vertices_56, vertices_536, vertices_552, vertices_176, vertices_656, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_845), (true, vertices_146), (true, vertices_530), (true, vertices_212), (true, vertices_100), (true, vertices_536), (true, vertices_552), (true, vertices_176), (true, vertices_656), (true, vertices_224), (true, vertices_608), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 17 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_451) then 13 else
  if p.val = (false, vertices_845) then 19 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_212) then 16 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_656) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_212), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_845), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 6 7 8 914 146 3
cert_row_4 1 4 5 6 7 8 992 224 3
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_2 3 1 2 5 8 588
cert_row_2 4 1 3 5 6 212
cert_rows_2
cert_pivot 0 7 4 2 1
cert_heightProof 5
cert_coverFacet 0 214
cert_cover_5 0 4 0 1 3 5 22 214 3
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 914
cert_cover_5 2 0 0 3 6 7 146 914 3
cert_coverFacet 3 620
cert_cover_5 3 3 1 2 4 5 44 620 3
cert_coverFacet 4 244
cert_cover_5 4 4 1 3 4 5 52 244 3
cert_coverFacet 5 696
cert_cover_5 5 2 2 3 4 6 56 696 3
cert_coverFacet 6 992
cert_cover_5 6 1 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 5 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0026

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_multi_six_0027.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0027

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 263, 203, 899, 789, 233, 689, 78, 454, 348, 888, 992, 7, 11, 131, 259, 21, 261, 41, 201, 49, 529, 161, 641, 769, 14, 70, 262, 74, 194, 386, 28, 76, 276, 324, 56, 344, 104, 560, 784, 224, 864, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_263, vertices_203, vertices_899, vertices_789, vertices_233, vertices_689, vertices_78, vertices_454, vertices_348, vertices_888, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_21, vertices_261, vertices_41, vertices_201, vertices_49, vertices_529, vertices_161, vertices_641, vertices_769, vertices_14, vertices_70, vertices_262, vertices_74, vertices_194, vertices_386, vertices_28, vertices_76, vertices_276, vertices_324, vertices_56, vertices_344, vertices_104, vertices_560, vertices_784, vertices_224, vertices_864, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_263), (false, vertices_203), (false, vertices_899), (false, vertices_789), (false, vertices_233), (false, vertices_689), (true, vertices_70), (true, vertices_76), (true, vertices_324), (true, vertices_344), (true, vertices_864), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 5 7 13 10 16 18 19 20 21
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 8 else
  if p.val = (false, vertices_263) then 0 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_899) then 6 else
  if p.val = (false, vertices_789) then 9 else
  if p.val = (false, vertices_233) then 15 else
  if p.val = (false, vertices_689) then 11 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_324) then 3 else
  if p.val = (true, vertices_344) then 12 else
  if p.val = (true, vertices_864) then 17 else
  if p.val = (true, vertices_448) then 4 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_263), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 5 => Sum.inl 0
  | 6 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 7 => Sum.inl 1
  | 8 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 10 => Sum.inl 3
  | 11 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_344), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 16 => Sum.inl 4
  | 17 => Sum.inr ⟨(true, vertices_864), by decide +kernel⟩
  | 18 => Sum.inl 5
  | 19 => Sum.inl 6
  | 20 => Sum.inl 7
  | 21 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 70 3
cert_row_4 1 2 3 4 5 7 888 56 3
cert_row_4 2 2 3 4 5 8 888 56 3
cert_rows_3
cert_pivot_3 7 0 2
cert_heightProof 3
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 348
cert_cover 2 3 3 1 2 3 2 5 4 28 348 344 56 888 5
cert_coverFacet 3 888
cert_cover_2 3 3 2 4 5 56 888 3
cert_coverFacet 4 992
cert_cover 4 6 3 4 5 3 2 7 4 224 992 864 56 888 5
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 3 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0027

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_multi_six_0028.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0028

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 267, 451, 853, 793, 206, 906, 236, 628, 696, 992, 7, 11, 67, 259, 21, 69, 25, 265, 785, 321, 14, 70, 138, 266, 194, 386, 44, 204, 52, 596, 100, 56, 536, 168, 648, 776, 560, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_267, vertices_451, vertices_853, vertices_793, vertices_206, vertices_906, vertices_236, vertices_628, vertices_696, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_25, vertices_265, vertices_785, vertices_321, vertices_14, vertices_70, vertices_138, vertices_266, vertices_194, vertices_386, vertices_44, vertices_204, vertices_52, vertices_596, vertices_100, vertices_56, vertices_536, vertices_168, vertices_648, vertices_776, vertices_560, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_267), (false, vertices_451), (false, vertices_853), (false, vertices_793), (true, vertices_138), (true, vertices_204), (true, vertices_100), (true, vertices_168), (true, vertices_648), (true, vertices_560), (true, vertices_224), (true, vertices_608), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 17 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_267) then 1 else
  if p.val = (false, vertices_451) then 12 else
  if p.val = (false, vertices_853) then 18 else
  if p.val = (false, vertices_793) then 19 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_204) then 15 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_224) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_853), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 6 7 8 906 138 3
cert_row_4 1 4 5 6 7 8 992 224 3
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_2 3 1 3 5 8 596
cert_row_2 4 1 2 5 6 204
cert_rows_2
cert_pivot 0 7 4 3 1
cert_heightProof 5
cert_coverFacet 0 206
cert_cover_5 0 4 0 1 2 5 14 206 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 236
cert_cover_5 2 4 1 2 4 5 44 236 3
cert_coverFacet 3 628
cert_cover_5 3 3 1 3 4 5 52 628 3
cert_coverFacet 4 696
cert_cover_5 4 2 2 3 4 6 56 696 3
cert_coverFacet 5 992
cert_cover_5 5 1 4 5 6 7 224 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 5 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0028

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_multi_six_0029.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0029

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 589, 961, 214, 410, 812, 756, 312, 944, 7, 11, 67, 259, 13, 69, 521, 449, 577, 769, 22, 70, 26, 266, 146, 194, 386, 44, 524, 52, 212, 548, 580, 56, 280, 296, 776, 688, 304, 400, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_589, vertices_961, vertices_214, vertices_410, vertices_812, vertices_756, vertices_312, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_69, vertices_521, vertices_449, vertices_577, vertices_769, vertices_22, vertices_70, vertices_26, vertices_266, vertices_146, vertices_194, vertices_386, vertices_44, vertices_524, vertices_52, vertices_212, vertices_548, vertices_580, vertices_56, vertices_280, vertices_296, vertices_776, vertices_688, vertices_304, vertices_400, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_589), (false, vertices_961), (true, vertices_146), (true, vertices_212), (true, vertices_548), (true, vertices_280), (true, vertices_296), (true, vertices_688), (true, vertices_304), (true, vertices_400), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 10 14 15 17 18 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 11 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 9 else
  if p.val = (false, vertices_451) then 19 else
  if p.val = (false, vertices_589) then 12 else
  if p.val = (false, vertices_961) then 20 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_212) then 13 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_280) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_688) then 16 else
  if p.val = (true, vertices_304) then 5 else
  if p.val = (true, vertices_400) then 6 else
  if p.val = (true, vertices_800) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_212), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(true, vertices_688), by decide +kernel⟩
  | 17 => Sum.inl 4
  | 18 => Sum.inl 5
  | 19 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 7 410 26 3
cert_row_4 1 1 2 4 7 8 812 44 3
cert_row_4 2 1 3 4 5 6 756 52 3
cert_row_4 3 1 3 4 5 8 756 52 3
cert_rows
cert_pivot_2 0 2 6 1
cert_heightProof 4
cert_coverFacet 0 214
cert_cover 0 3 3 0 1 3 1 5 4 22 214 212 52 756 5
cert_coverFacet 1 410
cert_cover_5 1 0 0 2 3 6 26 410 3
cert_coverFacet 2 812
cert_cover_5 2 1 1 2 4 7 44 812 3
cert_coverFacet 3 756
cert_cover_2 3 3 1 4 5 52 756 3
cert_coverFacet 4 312
cert_cover_2 4 3 2 4 7 56 312 3
cert_coverFacet 5 944
cert_cover 5 6 3 3 4 3 1 7 4 688 944 688 52 756 5
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0029

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_multi_six_0030.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0030

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 267, 835, 597, 425, 817, 398, 454, 220, 760, 992, 7, 11, 67, 259, 21, 69, 41, 265, 49, 529, 289, 577, 769, 14, 70, 390, 266, 322, 28, 140, 84, 196, 56, 216, 168, 392, 560, 592, 736, 416, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_267, vertices_835, vertices_597, vertices_425, vertices_817, vertices_398, vertices_454, vertices_220, vertices_760, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_41, vertices_265, vertices_49, vertices_529, vertices_289, vertices_577, vertices_769, vertices_14, vertices_70, vertices_390, vertices_266, vertices_322, vertices_28, vertices_140, vertices_84, vertices_196, vertices_56, vertices_216, vertices_168, vertices_392, vertices_560, vertices_592, vertices_736, vertices_416, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_267), (false, vertices_835), (false, vertices_597), (false, vertices_425), (false, vertices_817), (true, vertices_390), (true, vertices_140), (true, vertices_196), (true, vertices_216), (true, vertices_736), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 5 8 11 14 16 18 19 20 21
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 9 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_267) then 1 else
  if p.val = (false, vertices_835) then 6 else
  if p.val = (false, vertices_597) then 10 else
  if p.val = (false, vertices_425) then 12 else
  if p.val = (false, vertices_817) then 15 else
  if p.val = (true, vertices_390) then 7 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_196) then 3 else
  if p.val = (true, vertices_216) then 13 else
  if p.val = (true, vertices_736) then 17 else
  if p.val = (true, vertices_448) then 4 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 5 => Sum.inl 0
  | 6 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 8 => Sum.inl 1
  | 9 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 11 => Sum.inl 2
  | 12 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 16 => Sum.inl 4
  | 17 => Sum.inr ⟨(true, vertices_736), by decide +kernel⟩
  | 18 => Sum.inl 5
  | 19 => Sum.inl 6
  | 20 => Sum.inl 7
  | 21 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 7 390
cert_row_4 1 2 3 4 5 6 760 56 3
cert_row_4 2 2 3 4 5 8 760 56 3
cert_rows_3
cert_pivot_3 6 0 2
cert_heightProof 3
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 220
cert_cover 2 3 3 1 2 3 2 5 4 28 220 216 56 760 5
cert_coverFacet 3 760
cert_cover_2 3 3 2 4 5 56 760 3
cert_coverFacet 4 992
cert_cover 4 6 3 4 5 3 2 7 4 736 992 736 56 760 5
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 3 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0030

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_multi_six_0031.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0031

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 267, 835, 597, 425, 817, 398, 454, 732, 696, 992, 7, 11, 67, 259, 21, 69, 41, 265, 49, 529, 289, 577, 769, 14, 70, 390, 266, 322, 28, 140, 596, 196, 56, 664, 168, 392, 560, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_267, vertices_835, vertices_597, vertices_425, vertices_817, vertices_398, vertices_454, vertices_732, vertices_696, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_41, vertices_265, vertices_49, vertices_529, vertices_289, vertices_577, vertices_769, vertices_14, vertices_70, vertices_390, vertices_266, vertices_322, vertices_28, vertices_140, vertices_596, vertices_196, vertices_56, vertices_664, vertices_168, vertices_392, vertices_560, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_267), (false, vertices_835), (false, vertices_597), (false, vertices_425), (false, vertices_817), (true, vertices_390), (true, vertices_140), (true, vertices_196), (true, vertices_664), (true, vertices_672), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 7 10 13 16 18 19 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 11 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_267) then 1 else
  if p.val = (false, vertices_835) then 8 else
  if p.val = (false, vertices_597) then 12 else
  if p.val = (false, vertices_425) then 14 else
  if p.val = (false, vertices_817) then 17 else
  if p.val = (true, vertices_390) then 9 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_196) then 3 else
  if p.val = (true, vertices_664) then 15 else
  if p.val = (true, vertices_672) then 4 else
  if p.val = (true, vertices_448) then 5 else
  if p.val = (true, vertices_704) then 6 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 7 => Sum.inl 0
  | 8 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_664), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 7 390
cert_row_4 1 4 5 6 7 8 992 416 1
cert_row_4 2 1 2 3 5 6 732 28 3
cert_row_4 3 1 2 3 5 8 732 28 3
cert_rows
cert_pivot_2 0 4 6 1
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 732
cert_cover_2 2 2 1 3 5 28 732 3
cert_coverFacet 3 696
cert_cover 3 4 2 2 3 3 1 6 3 56 696 664 28 732 5
cert_coverFacet 4 992
cert_cover_5 4 1 4 5 6 7 416 992 1
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0031

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_multi_six_0032.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0032

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 331, 213, 361, 625, 910, 454, 668, 824, 720, 992, 7, 11, 67, 21, 69, 41, 329, 49, 81, 97, 14, 70, 390, 266, 322, 28, 652, 148, 196, 56, 536, 296, 776, 560, 208, 592, 656, 352, 608, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_331, vertices_213, vertices_361, vertices_625, vertices_910, vertices_454, vertices_668, vertices_824, vertices_720, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_41, vertices_329, vertices_49, vertices_81, vertices_97, vertices_14, vertices_70, vertices_390, vertices_266, vertices_322, vertices_28, vertices_652, vertices_148, vertices_196, vertices_56, vertices_536, vertices_296, vertices_776, vertices_560, vertices_208, vertices_592, vertices_656, vertices_352, vertices_608, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_331), (false, vertices_213), (false, vertices_361), (false, vertices_625), (true, vertices_390), (true, vertices_652), (true, vertices_536), (true, vertices_776), (true, vertices_656), (true, vertices_800), (true, vertices_448), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 10 14 17 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 11 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_331) then 15 else
  if p.val = (false, vertices_213) then 12 else
  if p.val = (false, vertices_361) then 16 else
  if p.val = (false, vertices_625) then 18 else
  if p.val = (true, vertices_390) then 9 else
  if p.val = (true, vertices_652) then 13 else
  if p.val = (true, vertices_536) then 1 else
  if p.val = (true, vertices_776) then 2 else
  if p.val = (true, vertices_656) then 3 else
  if p.val = (true, vertices_800) then 4 else
  if p.val = (true, vertices_448) then 5 else
  if p.val = (true, vertices_704) then 6 else
  if p.val = (true, vertices_896) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_652), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 4 7 8 824 56 3
cert_row_4 1 4 5 6 7 8 992 352 2
cert_row_4 2 0 1 2 6 7 910 14 3
cert_row_4 3 0 1 2 6 8 910 14 3
cert_rows
cert_pivot_2 3 4 7 1
cert_heightProof 4
cert_coverFacet 0 910
cert_cover_2 0 1 0 2 6 14 910 3
cert_coverFacet 1 454
cert_cover 1 5 1 0 1 3 0 6 2 70 454 390 14 910 6
cert_coverFacet 2 668
cert_cover 2 3 1 1 2 3 0 6 2 28 668 652 14 910 6
cert_coverFacet 3 824
cert_cover_5 3 0 2 3 4 7 56 824 3
cert_coverFacet 4 720
cert_cover_2 4 5 3 6 8 208 720 3
cert_coverFacet 5 992
cert_cover_5 5 1 4 5 6 7 352 992 2
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0032

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_multi_six_0033.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0033

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 331, 213, 361, 689, 225, 910, 454, 668, 824, 992, 7, 11, 67, 21, 69, 41, 329, 49, 145, 97, 161, 193, 14, 70, 390, 266, 322, 28, 652, 148, 196, 56, 536, 296, 776, 560, 656, 224, 352, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_331, vertices_213, vertices_361, vertices_689, vertices_225, vertices_910, vertices_454, vertices_668, vertices_824, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_41, vertices_329, vertices_49, vertices_145, vertices_97, vertices_161, vertices_193, vertices_14, vertices_70, vertices_390, vertices_266, vertices_322, vertices_28, vertices_652, vertices_148, vertices_196, vertices_56, vertices_536, vertices_296, vertices_776, vertices_560, vertices_656, vertices_224, vertices_352, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_331), (false, vertices_213), (false, vertices_361), (false, vertices_689), (false, vertices_225), (true, vertices_390), (true, vertices_652), (true, vertices_536), (true, vertices_776), (true, vertices_800), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 7 9 13 16 18 19 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 10 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_331) then 14 else
  if p.val = (false, vertices_213) then 11 else
  if p.val = (false, vertices_361) then 15 else
  if p.val = (false, vertices_689) then 17 else
  if p.val = (false, vertices_225) then 1 else
  if p.val = (true, vertices_390) then 8 else
  if p.val = (true, vertices_652) then 12 else
  if p.val = (true, vertices_536) then 2 else
  if p.val = (true, vertices_776) then 3 else
  if p.val = (true, vertices_800) then 4 else
  if p.val = (true, vertices_448) then 5 else
  if p.val = (true, vertices_896) then 6 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_225), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 7 => Sum.inl 0
  | 8 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_652), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 4 7 8 824 56 3
cert_row_4 1 4 5 6 7 8 992 224 3
cert_row_4 2 0 1 2 6 7 910 14 3
cert_row_4 3 0 1 2 6 8 910 14 3
cert_rows
cert_pivot_2 3 4 7 1
cert_heightProof 4
cert_coverFacet 0 910
cert_cover_2 0 1 0 2 6 14 910 3
cert_coverFacet 1 454
cert_cover 1 5 1 0 1 3 0 6 2 70 454 390 14 910 6
cert_coverFacet 2 668
cert_cover 2 3 1 1 2 3 0 6 2 28 668 652 14 910 6
cert_coverFacet 3 824
cert_cover_5 3 0 2 3 4 7 56 824 3
cert_coverFacet 4 992
cert_cover_5 4 1 4 5 6 7 224 992 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0033

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_multi_six_0034.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0034

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 597, 425, 241, 398, 966, 796, 824, 624, 992, 7, 11, 67, 21, 69, 41, 137, 49, 81, 161, 193, 14, 70, 390, 138, 194, 28, 268, 532, 580, 772, 56, 792, 296, 392, 112, 560, 592, 224, 608, 416, 800, 960]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_597, vertices_425, vertices_241, vertices_398, vertices_966, vertices_796, vertices_824, vertices_624, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_41, vertices_137, vertices_49, vertices_81, vertices_161, vertices_193, vertices_14, vertices_70, vertices_390, vertices_138, vertices_194, vertices_28, vertices_268, vertices_532, vertices_580, vertices_772, vertices_56, vertices_792, vertices_296, vertices_392, vertices_112, vertices_560, vertices_592, vertices_224, vertices_608, vertices_416, vertices_800, vertices_960] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_597), (false, vertices_425), (false, vertices_241), (true, vertices_390), (true, vertices_268), (true, vertices_772), (true, vertices_792), (true, vertices_560), (true, vertices_608), (true, vertices_800), (true, vertices_960)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 6 9 12 15 17 18 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 10 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 7 else
  if p.val = (false, vertices_597) then 11 else
  if p.val = (false, vertices_425) then 13 else
  if p.val = (false, vertices_241) then 16 else
  if p.val = (true, vertices_390) then 8 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_772) then 2 else
  if p.val = (true, vertices_792) then 14 else
  if p.val = (true, vertices_560) then 3 else
  if p.val = (true, vertices_608) then 4 else
  if p.val = (true, vertices_800) then 5 else
  if p.val = (true, vertices_960) then 19 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 6 => Sum.inl 0
  | 7 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 12 => Sum.inl 2
  | 13 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_792), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 17 => Sum.inl 4
  | 18 => Sum.inl 5
  | 19 => Sum.inr ⟨(true, vertices_960), by decide +kernel⟩
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 7 8 792
cert_row_4 1 0 1 5 6 7 966 70 3
cert_row_4 2 0 1 5 6 8 966 70 3
cert_rows_3
cert_pivot_3 7 2 0
cert_heightProof 3
cert_coverFacet 0 398
cert_cover 0 2 1 0 1 3 0 6 5 14 398 390 70 966 6
cert_coverFacet 1 966
cert_cover_2 1 1 0 5 6 70 966 3
cert_coverFacet 2 796
cert_cover_5 2 0 1 2 3 7 28 796 3
cert_coverFacet 3 824
cert_cover_5 3 0 2 3 4 7 56 824 3
cert_coverFacet 4 624
cert_cover_2 4 4 3 5 8 112 624 3
cert_coverFacet 5 992
cert_cover 5 6 1 4 5 3 0 7 5 224 992 960 70 966 6
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0034

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_multi_six_0035.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0035

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 597, 233, 817, 609, 398, 966, 796, 440, 992, 7, 11, 67, 21, 69, 41, 201, 49, 529, 97, 545, 577, 14, 70, 390, 138, 194, 28, 268, 532, 580, 772, 56, 280, 168, 392, 304, 784, 224, 608, 416, 800, 960]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_597, vertices_233, vertices_817, vertices_609, vertices_398, vertices_966, vertices_796, vertices_440, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_41, vertices_201, vertices_49, vertices_529, vertices_97, vertices_545, vertices_577, vertices_14, vertices_70, vertices_390, vertices_138, vertices_194, vertices_28, vertices_268, vertices_532, vertices_580, vertices_772, vertices_56, vertices_280, vertices_168, vertices_392, vertices_304, vertices_784, vertices_224, vertices_608, vertices_416, vertices_800, vertices_960] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_597), (false, vertices_233), (false, vertices_817), (false, vertices_609), (true, vertices_390), (true, vertices_268), (true, vertices_772), (true, vertices_280), (true, vertices_392), (true, vertices_416), (true, vertices_960)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 7 9 12 15 17 18 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 10 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 13 else
  if p.val = (false, vertices_597) then 11 else
  if p.val = (false, vertices_233) then 14 else
  if p.val = (false, vertices_817) then 16 else
  if p.val = (false, vertices_609) then 1 else
  if p.val = (true, vertices_390) then 8 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_772) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_392) then 5 else
  if p.val = (true, vertices_416) then 6 else
  if p.val = (true, vertices_960) then 19 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_609), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 7 => Sum.inl 0
  | 8 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 12 => Sum.inl 2
  | 13 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 17 => Sum.inl 4
  | 18 => Sum.inl 5
  | 19 => Sum.inr ⟨(true, vertices_960), by decide +kernel⟩
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 4 6 7 440 56 3
cert_row_4 1 1 2 3 7 8 796 28 3
cert_row_4 2 0 1 5 6 7 966 70 3
cert_row_4 3 0 1 5 6 8 966 70 3
cert_rows
cert_pivot_2 4 2 7 0
cert_heightProof 4
cert_coverFacet 0 398
cert_cover 0 2 1 0 1 3 0 6 5 14 398 390 70 966 6
cert_coverFacet 1 966
cert_cover_2 1 1 0 5 6 70 966 3
cert_coverFacet 2 796
cert_cover_5 2 1 1 2 3 7 28 796 3
cert_coverFacet 3 440
cert_cover_5 3 0 2 3 4 6 56 440 3
cert_coverFacet 4 992
cert_cover 4 6 1 4 5 3 0 7 5 224 992 960 70 966 6
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0035

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_multi_six_0036.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0036

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 587, 149, 745, 433, 782, 838, 284, 468, 824, 992, 7, 11, 67, 21, 133, 41, 585, 49, 145, 161, 193, 14, 70, 774, 522, 578, 28, 268, 148, 276, 196, 324, 56, 280, 552, 776, 304, 400, 736, 416, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_587, vertices_149, vertices_745, vertices_433, vertices_782, vertices_838, vertices_284, vertices_468, vertices_824, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_133, vertices_41, vertices_585, vertices_49, vertices_145, vertices_161, vertices_193, vertices_14, vertices_70, vertices_774, vertices_522, vertices_578, vertices_28, vertices_268, vertices_148, vertices_276, vertices_196, vertices_324, vertices_56, vertices_280, vertices_552, vertices_776, vertices_304, vertices_400, vertices_736, vertices_416, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_587), (false, vertices_149), (false, vertices_745), (false, vertices_433), (true, vertices_774), (true, vertices_268), (true, vertices_276), (true, vertices_324), (true, vertices_280), (true, vertices_776), (true, vertices_800), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 9 11 18 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_199) then 15 else
  if p.val = (false, vertices_587) then 10 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_745) then 19 else
  if p.val = (false, vertices_433) then 13 else
  if p.val = (true, vertices_774) then 16 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_324) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_800) then 6 else
  if p.val = (true, vertices_448) then 7 else
  if p.val = (true, vertices_832) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 9 => Sum.inl 2
  | 10 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 11 => Sum.inl 3
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inl 4
  | 19 => Sum.inr ⟨(false, vertices_745), by decide +kernel⟩
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 7 8 774
cert_row_4 1 1 3 5 6 7 468 148 2
cert_row_2 2 4 5 6 8 736
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 0 1 5 2
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 838
cert_cover_5 1 0 0 1 5 7 70 838 3
cert_coverFacet 2 284
cert_cover_2 2 2 1 3 7 28 284 3
cert_coverFacet 3 468
cert_cover_5 3 1 1 3 5 6 148 468 2
cert_coverFacet 4 824
cert_cover_5 4 3 2 3 4 7 56 824 3
cert_coverFacet 5 992
cert_cover_5 5 2 4 5 6 7 736 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0036

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_multi_six_0037.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0037

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 397, 961, 86, 282, 850, 940, 244, 824, 752, 7, 11, 67, 13, 133, 265, 193, 321, 385, 22, 70, 26, 266, 82, 274, 322, 44, 396, 52, 84, 164, 196, 56, 280, 808, 240, 560, 592, 784, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_397, vertices_961, vertices_86, vertices_282, vertices_850, vertices_940, vertices_244, vertices_824, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_266, vertices_82, vertices_274, vertices_322, vertices_44, vertices_396, vertices_52, vertices_84, vertices_164, vertices_196, vertices_56, vertices_280, vertices_808, vertices_240, vertices_560, vertices_592, vertices_784, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_274), (true, vertices_84), (true, vertices_164), (true, vertices_280), (true, vertices_808), (true, vertices_240), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 15 17 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_199) then 10 else
  if p.val = (false, vertices_331) then 11 else
  if p.val = (false, vertices_397) then 14 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_808) then 16 else
  if p.val = (true, vertices_240) then 18 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_592) then 6 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_672) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
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
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(true, vertices_808), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 7 8 850 82 3
cert_row_2 1 3 4 5 6 240
cert_row_4 2 1 2 4 6 7 940 44 3
cert_row_4 3 1 2 4 6 8 940 44 3
cert_rows
cert_pivot_2 0 3 7 1
cert_heightProof 4
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 850
cert_cover_5 2 0 0 3 5 7 82 850 3
cert_coverFacet 3 940
cert_cover_2 3 2 1 4 6 44 940 3
cert_coverFacet 4 244
cert_cover_5 4 1 1 3 4 5 52 244 3
cert_coverFacet 5 824
cert_cover 5 4 2 2 3 3 1 7 4 56 824 808 44 940 6
cert_coverFacet 6 752
cert_cover_5 6 1 3 4 5 8 240 752 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0037

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_multi_six_0038.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0038

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 141, 905, 961, 342, 794, 172, 884, 740, 696, 7, 11, 67, 13, 133, 137, 265, 193, 321, 897, 22, 70, 26, 266, 274, 322, 44, 140, 52, 340, 612, 164, 196, 56, 536, 168, 648, 776, 560, 784, 672, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_141, vertices_905, vertices_961, vertices_342, vertices_794, vertices_172, vertices_884, vertices_740, vertices_696] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_137, vertices_265, vertices_193, vertices_321, vertices_897, vertices_22, vertices_70, vertices_26, vertices_266, vertices_274, vertices_322, vertices_44, vertices_140, vertices_52, vertices_340, vertices_612, vertices_164, vertices_196, vertices_56, vertices_536, vertices_168, vertices_648, vertices_776, vertices_560, vertices_784, vertices_672, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_141), (false, vertices_905), (false, vertices_961), (true, vertices_274), (true, vertices_340), (true, vertices_612), (true, vertices_164), (true, vertices_536), (true, vertices_168), (true, vertices_560), (true, vertices_784), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 15 16 17 18 19 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_199) then 9 else
  if p.val = (false, vertices_331) then 10 else
  if p.val = (false, vertices_141) then 0 else
  if p.val = (false, vertices_905) then 20 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_340) then 13 else
  if p.val = (true, vertices_612) then 14 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_536) then 3 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_784) then 6 else
  if p.val = (true, vertices_672) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_141), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_340), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_612), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inl 3
  | 17 => Sum.inl 4
  | 18 => Sum.inl 5
  | 19 => Sum.inl 6
  | 20 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 7 8 794 26 3
cert_row_4 1 1 3 4 5 7 884 52 3
cert_row_4 2 1 3 4 5 8 884 52 3
cert_row_4 3 2 3 4 6 8 696 56 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 342
cert_cover 0 3 3 0 1 3 1 5 4 22 342 340 52 884 5
cert_coverFacet 1 794
cert_cover_5 1 0 0 2 3 7 26 794 3
cert_coverFacet 2 172
cert_cover_2 2 2 1 4 6 44 172 3
cert_coverFacet 3 884
cert_cover_2 3 3 1 4 5 52 884 3
cert_coverFacet 4 740
cert_cover 4 5 3 1 4 3 1 6 4 612 740 612 52 884 5
cert_coverFacet 5 696
cert_cover_5 5 3 2 3 4 6 56 696 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0038

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_multi_six_0039.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0039

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 397, 961, 86, 858, 300, 244, 932, 824, 752, 7, 11, 67, 13, 133, 265, 193, 321, 385, 22, 70, 26, 330, 82, 44, 268, 52, 84, 164, 292, 196, 388, 56, 792, 296, 240, 560, 592, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_397, vertices_961, vertices_86, vertices_858, vertices_300, vertices_244, vertices_932, vertices_824, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_330, vertices_82, vertices_44, vertices_268, vertices_52, vertices_84, vertices_164, vertices_292, vertices_196, vertices_388, vertices_56, vertices_792, vertices_296, vertices_240, vertices_560, vertices_592, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_84), (true, vertices_164), (true, vertices_292), (true, vertices_792), (true, vertices_296), (true, vertices_240), (true, vertices_560), (true, vertices_592), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 15 17 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_199) then 10 else
  if p.val = (false, vertices_331) then 11 else
  if p.val = (false, vertices_397) then 14 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_292) then 3 else
  if p.val = (true, vertices_792) then 16 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_240) then 18 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_592) then 6 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_800) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(true, vertices_792), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 4 6 7 8 932 164 3
cert_row_2 1 3 4 5 6 240
cert_row_4 2 0 2 3 5 7 858 26 3
cert_row_4 3 0 2 3 5 8 858 26 3
cert_rows
cert_pivot_2 1 4 7 0
cert_heightProof 4
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 858
cert_cover_2 1 2 0 3 5 26 858 3
cert_coverFacet 2 300
cert_cover_2 2 2 1 4 7 44 300 3
cert_coverFacet 3 244
cert_cover_5 3 1 1 3 4 5 52 244 3
cert_coverFacet 4 932
cert_cover_5 4 0 1 4 6 7 164 932 3
cert_coverFacet 5 824
cert_cover 5 4 2 2 3 3 0 7 3 56 824 792 26 858 5
cert_coverFacet 6 752
cert_cover_5 6 1 3 4 5 8 240 752 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0039

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_multi_six_0040.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0040

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 835, 141, 713, 342, 282, 684, 244, 824, 1008, 7, 11, 67, 771, 13, 133, 137, 521, 193, 577, 22, 70, 26, 266, 274, 322, 44, 140, 52, 84, 164, 196, 56, 280, 552, 648, 776, 240, 816, 336, 672, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_835, vertices_141, vertices_713, vertices_342, vertices_282, vertices_684, vertices_244, vertices_824, vertices_1008] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_771, vertices_13, vertices_133, vertices_137, vertices_521, vertices_193, vertices_577, vertices_22, vertices_70, vertices_26, vertices_266, vertices_274, vertices_322, vertices_44, vertices_140, vertices_52, vertices_84, vertices_164, vertices_196, vertices_56, vertices_280, vertices_552, vertices_648, vertices_776, vertices_240, vertices_816, vertices_336, vertices_672, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_835), (false, vertices_141), (false, vertices_713), (true, vertices_274), (true, vertices_84), (true, vertices_164), (true, vertices_280), (true, vertices_552), (true, vertices_240), (true, vertices_816), (true, vertices_336), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 8 14 16 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 11 else
  if p.val = (false, vertices_199) then 9 else
  if p.val = (false, vertices_779) then 12 else
  if p.val = (false, vertices_835) then 13 else
  if p.val = (false, vertices_141) then 0 else
  if p.val = (false, vertices_713) then 15 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_240) then 17 else
  if p.val = (true, vertices_816) then 18 else
  if p.val = (true, vertices_336) then 6 else
  if p.val = (true, vertices_672) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_141), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inl 1
  | 9 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 7 342 22 3
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_4 2 3 4 5 7 6 1008 240 3
cert_row_4 3 3 4 5 7 8 1008 240 3
cert_rows
cert_pivot_2 0 1 6 3
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 0 0 1 3 5 22 342 3
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 684
cert_cover_5 2 1 1 2 4 6 44 684 3
cert_coverFacet 3 244
cert_cover 3 4 4 1 3 3 3 5 5 52 244 240 240 1008 7
cert_coverFacet 4 824
cert_cover 4 4 4 2 3 3 3 7 5 56 824 816 240 1008 7
cert_coverFacet 5 1008
cert_cover_2 5 4 3 5 7 240 1008 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0040

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_multi_six_0041.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0041

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 139, 341, 681, 497, 782, 838, 714, 284, 824, 992, 7, 11, 131, 21, 69, 41, 137, 49, 337, 161, 193, 14, 70, 774, 138, 522, 194, 578, 28, 268, 276, 324, 56, 280, 552, 648, 776, 304, 480, 672, 800, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_139, vertices_341, vertices_681, vertices_497, vertices_782, vertices_838, vertices_714, vertices_284, vertices_824, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_69, vertices_41, vertices_137, vertices_49, vertices_337, vertices_161, vertices_193, vertices_14, vertices_70, vertices_774, vertices_138, vertices_522, vertices_194, vertices_578, vertices_28, vertices_268, vertices_276, vertices_324, vertices_56, vertices_280, vertices_552, vertices_648, vertices_776, vertices_304, vertices_480, vertices_672, vertices_800, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_139), (false, vertices_341), (false, vertices_681), (false, vertices_497), (true, vertices_774), (true, vertices_522), (true, vertices_578), (true, vertices_268), (true, vertices_280), (true, vertices_776), (true, vertices_800), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 9 11 18 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_199) then 15 else
  if p.val = (false, vertices_139) then 0 else
  if p.val = (false, vertices_341) then 13 else
  if p.val = (false, vertices_681) then 10 else
  if p.val = (false, vertices_497) then 19 else
  if p.val = (true, vertices_774) then 16 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_578) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_800) then 6 else
  if p.val = (true, vertices_704) then 7 else
  if p.val = (true, vertices_832) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_139), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 9 => Sum.inl 2
  | 10 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 11 => Sum.inl 3
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inl 4
  | 19 => Sum.inr ⟨(false, vertices_497), by decide +kernel⟩
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 7 8 774
cert_row_4 1 0 2 5 6 8 714 138 2
cert_row_2 2 4 5 6 7 480
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 1 0 5 2
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 838
cert_cover_5 1 0 0 1 5 7 70 838 3
cert_coverFacet 2 714
cert_cover_5 2 1 0 2 5 6 138 714 2
cert_coverFacet 3 284
cert_cover_2 3 2 1 3 7 28 284 3
cert_coverFacet 4 824
cert_cover_5 4 3 2 3 4 7 56 824 3
cert_coverFacet 5 992
cert_cover_5 5 2 4 5 6 8 480 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0041

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_multi_six_0045.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0045

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 853, 537, 206, 906, 236, 628, 696, 992, 7, 11, 67, 259, 21, 69, 25, 521, 529, 321, 769, 14, 70, 138, 778, 194, 386, 44, 204, 52, 596, 100, 56, 536, 168, 648, 560, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_853, vertices_537, vertices_206, vertices_906, vertices_236, vertices_628, vertices_696, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_25, vertices_521, vertices_529, vertices_321, vertices_769, vertices_14, vertices_70, vertices_138, vertices_778, vertices_194, vertices_386, vertices_44, vertices_204, vertices_52, vertices_596, vertices_100, vertices_56, vertices_536, vertices_168, vertices_648, vertices_560, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_853), (false, vertices_537), (true, vertices_138), (true, vertices_204), (true, vertices_100), (true, vertices_168), (true, vertices_648), (true, vertices_560), (true, vertices_224), (true, vertices_608), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 12 else
  if p.val = (false, vertices_451) then 13 else
  if p.val = (false, vertices_853) then 19 else
  if p.val = (false, vertices_537) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_204) then 16 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_224) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_537), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_853), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 7 8 778
cert_row_4 1 4 5 6 7 8 992 224 3
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_2 3 1 3 5 8 596
cert_row_2 4 1 2 5 6 204
cert_rows_2
cert_pivot 0 7 4 3 1
cert_heightProof 5
cert_coverFacet 0 206
cert_cover_5 0 4 0 1 2 5 14 206 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 236
cert_cover_5 2 4 1 2 4 5 44 236 3
cert_coverFacet 3 628
cert_cover_5 3 3 1 3 4 5 52 628 3
cert_coverFacet 4 696
cert_cover_5 4 2 2 3 4 6 56 696 3
cert_coverFacet 5 992
cert_cover_5 5 1 4 5 6 7 224 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 5 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0045

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_multi_six_0046.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0046

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 963, 213, 409, 590, 620, 436, 484, 824, 864, 7, 11, 67, 771, 21, 69, 25, 265, 145, 193, 385, 14, 70, 522, 578, 44, 588, 52, 148, 100, 420, 196, 56, 280, 552, 776, 304, 400, 352, 608, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_963, vertices_213, vertices_409, vertices_590, vertices_620, vertices_436, vertices_484, vertices_824, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_771, vertices_21, vertices_69, vertices_25, vertices_265, vertices_145, vertices_193, vertices_385, vertices_14, vertices_70, vertices_522, vertices_578, vertices_44, vertices_588, vertices_52, vertices_148, vertices_100, vertices_420, vertices_196, vertices_56, vertices_280, vertices_552, vertices_776, vertices_304, vertices_400, vertices_352, vertices_608, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_963), (false, vertices_213), (false, vertices_409), (true, vertices_588), (true, vertices_100), (true, vertices_420), (true, vertices_552), (true, vertices_304), (true, vertices_352), (true, vertices_608), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 7 13 9 16 17 18 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 10 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 8 else
  if p.val = (false, vertices_963) then 19 else
  if p.val = (false, vertices_213) then 14 else
  if p.val = (false, vertices_409) then 11 else
  if p.val = (true, vertices_588) then 12 else
  if p.val = (true, vertices_100) then 1 else
  if p.val = (true, vertices_420) then 15 else
  if p.val = (true, vertices_552) then 2 else
  if p.val = (true, vertices_304) then 3 else
  if p.val = (true, vertices_352) then 4 else
  if p.val = (true, vertices_608) then 5 else
  if p.val = (true, vertices_800) then 6 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 7 => Sum.inl 0
  | 8 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 9 => Sum.inl 2
  | 10 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_588), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_420), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inl 4
  | 18 => Sum.inl 5
  | 19 => Sum.inr ⟨(false, vertices_963), by decide +kernel⟩
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 6 7 420
cert_row_2 1 1 2 5 8 588
cert_row_4 2 2 3 4 7 8 824 56 3
cert_rows_3
cert_pivot_3 1 6 2
cert_heightProof 3
cert_coverFacet 0 590
cert_cover_5 0 1 0 1 2 5 14 590 3
cert_coverFacet 1 620
cert_cover_5 1 1 1 2 4 5 44 620 3
cert_coverFacet 2 436
cert_cover_5 2 0 1 3 4 6 52 436 3
cert_coverFacet 3 484
cert_cover_5 3 0 1 4 5 6 100 484 3
cert_coverFacet 4 824
cert_cover_5 4 2 2 3 4 7 56 824 3
cert_coverFacet 5 864
cert_cover_2 5 5 4 7 8 352 864 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0046

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_0540 : Certifies 540 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0014.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0541 : Certifies 541 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0015.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0542 : Certifies 542 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0016.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0543 : Certifies 543 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0017.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0544 : Certifies 544 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0018.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0545 : Certifies 545 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0019.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0546 : Certifies 546 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0020.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0547 : Certifies 547 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0021.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0548 : Certifies 548 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0022.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0549 : Certifies 549 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0023.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0550 : Certifies 550 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0024.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0551 : Certifies 551 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0025.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0552 : Certifies 552 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0026.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0553 : Certifies 553 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0027.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0554 : Certifies 554 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0028.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0555 : Certifies 555 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0029.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0556 : Certifies 556 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0030.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0557 : Certifies 557 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0031.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0558 : Certifies 558 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0032.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0559 : Certifies 559 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0033.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0560 : Certifies 560 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0034.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0561 : Certifies 561 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0035.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0562 : Certifies 562 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0036.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0563 : Certifies 563 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0037.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0564 : Certifies 564 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0038.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0565 : Certifies 565 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0039.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0566 : Certifies 566 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0040.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0567 : Certifies 567 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0041.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0568 : Certifies 568 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0045.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0569 : Certifies 569 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_multi_six_0046.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B018 (j : Fin 30) :
    Certifies (540 + j.val) := by
  fin_cases j
  · exact projection_0540
  · exact projection_0541
  · exact projection_0542
  · exact projection_0543
  · exact projection_0544
  · exact projection_0545
  · exact projection_0546
  · exact projection_0547
  · exact projection_0548
  · exact projection_0549
  · exact projection_0550
  · exact projection_0551
  · exact projection_0552
  · exact projection_0553
  · exact projection_0554
  · exact projection_0555
  · exact projection_0556
  · exact projection_0557
  · exact projection_0558
  · exact projection_0559
  · exact projection_0560
  · exact projection_0561
  · exact projection_0562
  · exact projection_0563
  · exact projection_0564
  · exact projection_0565
  · exact projection_0566
  · exact projection_0567
  · exact projection_0568
  · exact projection_0569

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
