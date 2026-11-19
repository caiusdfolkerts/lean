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
/- Source: ProjectionCertificates/R_one_six_0169.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0169

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 267, 835, 597, 425, 817, 398, 454, 156, 724, 696, 992, 7, 11, 67, 259, 21, 69, 41, 265, 49, 529, 289, 577, 769, 14, 70, 390, 266, 322, 28, 140, 596, 148, 196, 56, 152, 168, 392, 560, 656, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_267, vertices_835, vertices_597, vertices_425, vertices_817, vertices_398, vertices_454, vertices_156, vertices_724, vertices_696, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_41, vertices_265, vertices_49, vertices_529, vertices_289, vertices_577, vertices_769, vertices_14, vertices_70, vertices_390, vertices_266, vertices_322, vertices_28, vertices_140, vertices_596, vertices_148, vertices_196, vertices_56, vertices_152, vertices_168, vertices_392, vertices_560, vertices_656, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_267), (false, vertices_835), (false, vertices_597), (false, vertices_425), (false, vertices_817), (true, vertices_390), (true, vertices_140), (true, vertices_148), (true, vertices_196), (true, vertices_152), (true, vertices_656), (true, vertices_672), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_267) then 1 else
  if p.val = (false, vertices_835) then 11 else
  if p.val = (false, vertices_597) then 15 else
  if p.val = (false, vertices_425) then 17 else
  if p.val = (false, vertices_817) then 19 else
  if p.val = (true, vertices_390) then 12 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_656) then 6 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_704) then 9 else
  0
cert_priority
cert_nodeAtPriority_3 267 140 148 196 152 656 672 448 704 835 390 597 425 817
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 7 390
cert_row_2 1 1 3 5 8 596
cert_row_4 2 2 3 4 6 8 696 56 3
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
cert_coverFacet 4 696
cert_cover_5 4 2 2 3 4 6 56 696 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 416 992 1
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0169

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_one_six_0170.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0170

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 587, 213, 809, 625, 398, 454, 842, 156, 440, 240, 992, 7, 11, 67, 21, 69, 41, 521, 49, 81, 545, 577, 14, 70, 390, 586, 266, 322, 28, 140, 148, 196, 56, 152, 296, 392, 776, 112, 176, 208, 224, 608, 416, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_587, vertices_213, vertices_809, vertices_625, vertices_398, vertices_454, vertices_842, vertices_156, vertices_440, vertices_240, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_41, vertices_521, vertices_49, vertices_81, vertices_545, vertices_577, vertices_14, vertices_70, vertices_390, vertices_586, vertices_266, vertices_322, vertices_28, vertices_140, vertices_148, vertices_196, vertices_56, vertices_152, vertices_296, vertices_392, vertices_776, vertices_112, vertices_176, vertices_208, vertices_224, vertices_608, vertices_416, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_587), (false, vertices_213), (false, vertices_809), (false, vertices_625), (true, vertices_390), (true, vertices_266), (true, vertices_322), (true, vertices_140), (true, vertices_152), (true, vertices_392), (true, vertices_176), (true, vertices_224), (true, vertices_416), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_587) then 12 else
  if p.val = (false, vertices_213) then 16 else
  if p.val = (false, vertices_809) then 18 else
  if p.val = (false, vertices_625) then 20 else
  if p.val = (true, vertices_390) then 13 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_152) then 4 else
  if p.val = (true, vertices_392) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_224) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 7 390
cert_row_2 1 0 2 5 8 586
cert_row_4 2 2 3 4 6 7 440 56 3
cert_row_4 3 4 5 6 7 8 992 224 3
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
cert_coverFacet 5 240
cert_cover_2 5 4 3 5 6 112 240 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0170

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_one_six_0171.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0171

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 587, 213, 809, 625, 398, 454, 842, 156, 440, 816, 976, 7, 11, 67, 21, 69, 41, 521, 49, 81, 545, 577, 14, 70, 390, 586, 266, 322, 28, 140, 148, 196, 56, 152, 296, 392, 776, 304, 560, 208, 592, 400, 784, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_587, vertices_213, vertices_809, vertices_625, vertices_398, vertices_454, vertices_842, vertices_156, vertices_440, vertices_816, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_41, vertices_521, vertices_49, vertices_81, vertices_545, vertices_577, vertices_14, vertices_70, vertices_390, vertices_586, vertices_266, vertices_322, vertices_28, vertices_140, vertices_148, vertices_196, vertices_56, vertices_152, vertices_296, vertices_392, vertices_776, vertices_304, vertices_560, vertices_208, vertices_592, vertices_400, vertices_784, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_587), (false, vertices_213), (false, vertices_809), (false, vertices_625), (true, vertices_390), (true, vertices_266), (true, vertices_322), (true, vertices_140), (true, vertices_152), (true, vertices_392), (true, vertices_304), (true, vertices_400), (true, vertices_784), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_587) then 12 else
  if p.val = (false, vertices_213) then 16 else
  if p.val = (false, vertices_809) then 18 else
  if p.val = (false, vertices_625) then 20 else
  if p.val = (true, vertices_390) then 13 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_152) then 4 else
  if p.val = (true, vertices_392) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_400) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 7 390
cert_row_2 1 0 2 5 8 586
cert_row_4 2 2 3 4 6 7 440 56 3
cert_row_4 3 3 5 6 7 8 976 208 3
cert_rows
cert_pivot_2 1 0 2 3
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
cert_coverFacet 5 816
cert_cover_2 5 4 3 7 8 304 816 3
cert_coverFacet 6 976
cert_cover_5 6 3 3 5 6 7 208 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0171

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_one_six_0172.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0172

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 587, 213, 809, 689, 705, 398, 454, 842, 156, 440, 992, 7, 11, 67, 21, 69, 41, 521, 49, 145, 545, 193, 577, 641, 14, 70, 390, 586, 266, 322, 28, 140, 148, 196, 56, 152, 296, 392, 776, 176, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_587, vertices_213, vertices_809, vertices_689, vertices_705, vertices_398, vertices_454, vertices_842, vertices_156, vertices_440, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_41, vertices_521, vertices_49, vertices_145, vertices_545, vertices_193, vertices_577, vertices_641, vertices_14, vertices_70, vertices_390, vertices_586, vertices_266, vertices_322, vertices_28, vertices_140, vertices_148, vertices_196, vertices_56, vertices_152, vertices_296, vertices_392, vertices_776, vertices_176, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_587), (false, vertices_213), (false, vertices_809), (false, vertices_689), (false, vertices_705), (true, vertices_390), (true, vertices_266), (true, vertices_322), (true, vertices_140), (true, vertices_152), (true, vertices_392), (true, vertices_416), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_587) then 11 else
  if p.val = (false, vertices_213) then 15 else
  if p.val = (false, vertices_809) then 17 else
  if p.val = (false, vertices_689) then 19 else
  if p.val = (false, vertices_705) then 1 else
  if p.val = (true, vertices_390) then 12 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_416) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
cert_nodeAtPriority_3 705 266 322 140 152 392 416 448 832 587 390 213 809 689
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0172

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_one_six_0173.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0173

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 587, 149, 709, 809, 689, 398, 454, 842, 156, 440, 992, 7, 11, 67, 21, 69, 133, 41, 521, 49, 145, 545, 577, 641, 14, 70, 390, 586, 266, 322, 28, 140, 148, 196, 56, 152, 296, 392, 776, 176, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_587, vertices_149, vertices_709, vertices_809, vertices_689, vertices_398, vertices_454, vertices_842, vertices_156, vertices_440, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_133, vertices_41, vertices_521, vertices_49, vertices_145, vertices_545, vertices_577, vertices_641, vertices_14, vertices_70, vertices_390, vertices_586, vertices_266, vertices_322, vertices_28, vertices_140, vertices_148, vertices_196, vertices_56, vertices_152, vertices_296, vertices_392, vertices_776, vertices_176, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_587), (false, vertices_149), (false, vertices_709), (false, vertices_809), (false, vertices_689), (true, vertices_390), (true, vertices_266), (true, vertices_322), (true, vertices_140), (true, vertices_152), (true, vertices_392), (true, vertices_416), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_587) then 11 else
  if p.val = (false, vertices_149) then 1 else
  if p.val = (false, vertices_709) then 15 else
  if p.val = (false, vertices_809) then 17 else
  if p.val = (false, vertices_689) then 19 else
  if p.val = (true, vertices_390) then 12 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_416) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
cert_nodeAtPriority_3 149 266 322 140 152 392 416 448 832 587 390 709 809 689
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0173

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_one_six_0174.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0174

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 661, 233, 689, 782, 326, 540, 964, 824, 360, 992, 7, 11, 67, 21, 133, 41, 73, 49, 657, 161, 193, 14, 70, 262, 266, 322, 28, 524, 532, 196, 324, 644, 772, 56, 536, 104, 296, 328, 776, 560, 224, 352, 672, 800, 960]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_661, vertices_233, vertices_689, vertices_782, vertices_326, vertices_540, vertices_964, vertices_824, vertices_360, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_133, vertices_41, vertices_73, vertices_49, vertices_657, vertices_161, vertices_193, vertices_14, vertices_70, vertices_262, vertices_266, vertices_322, vertices_28, vertices_524, vertices_532, vertices_196, vertices_324, vertices_644, vertices_772, vertices_56, vertices_536, vertices_104, vertices_296, vertices_328, vertices_776, vertices_560, vertices_224, vertices_352, vertices_672, vertices_800, vertices_960] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_661), (false, vertices_233), (false, vertices_689), (true, vertices_262), (true, vertices_524), (true, vertices_324), (true, vertices_772), (true, vertices_536), (true, vertices_296), (true, vertices_776), (true, vertices_352), (true, vertices_800), (true, vertices_960)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 14 16 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_199) then 10 else
  if p.val = (false, vertices_331) then 11 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_233) then 15 else
  if p.val = (false, vertices_689) then 18 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_524) then 1 else
  if p.val = (true, vertices_324) then 2 else
  if p.val = (true, vertices_772) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_352) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_960) then 21 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(true, vertices_960), by decide +kernel⟩
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 5 6 7 8 960
cert_row_4 1 0 1 2 7 8 782 14 3
cert_row_4 2 2 3 4 7 8 824 56 3
cert_rows_3
cert_pivot_3 0 5 2
cert_heightProof 3
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 14 782 3
cert_coverFacet 1 326
cert_cover_2 1 1 0 5 7 70 326 3
cert_coverFacet 2 540
cert_cover_2 2 2 1 3 8 28 540 3
cert_coverFacet 3 964
cert_cover_5 3 0 1 5 6 7 196 964 3
cert_coverFacet 4 824
cert_cover_5 4 2 2 3 4 7 56 824 3
cert_coverFacet 5 360
cert_cover_2 5 4 2 5 7 104 360 3
cert_coverFacet 6 992
cert_cover_5 6 0 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0174

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_one_six_0175.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0175

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 323, 333, 662, 538, 962, 236, 692, 824, 488, 928, 7, 11, 67, 259, 13, 69, 265, 321, 22, 134, 26, 522, 530, 194, 322, 642, 770, 44, 76, 52, 660, 164, 196, 56, 536, 232, 296, 328, 776, 560, 416, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_323, vertices_333, vertices_662, vertices_538, vertices_962, vertices_236, vertices_692, vertices_824, vertices_488, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_69, vertices_265, vertices_321, vertices_22, vertices_134, vertices_26, vertices_522, vertices_530, vertices_194, vertices_322, vertices_642, vertices_770, vertices_44, vertices_76, vertices_52, vertices_660, vertices_164, vertices_196, vertices_56, vertices_536, vertices_232, vertices_296, vertices_328, vertices_776, vertices_560, vertices_416, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_323), (false, vertices_333), (true, vertices_530), (true, vertices_642), (true, vertices_660), (true, vertices_164), (true, vertices_536), (true, vertices_232), (true, vertices_296), (true, vertices_560), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_333) then 17 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_660) then 18 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_232) then 20 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_416) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_660), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(true, vertices_232), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 6 8 660
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_2 2 2 4 5 6 232
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 1 0 5 2
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 22 662 3
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 962
cert_cover_5 2 1 0 5 6 7 194 962 3
cert_coverFacet 3 236
cert_cover_5 3 2 1 2 4 5 44 236 3
cert_coverFacet 4 692
cert_cover_5 4 0 1 3 4 6 52 692 3
cert_coverFacet 5 824
cert_cover_5 5 3 2 3 4 7 56 824 3
cert_coverFacet 6 488
cert_cover_5 6 2 2 4 5 7 232 488 3
cert_coverFacet 7 928
cert_cover_2 7 6 4 7 8 416 928 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0175

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_one_six_0176.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0176

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 323, 149, 665, 961, 334, 364, 244, 824, 944, 480, 7, 11, 67, 259, 21, 133, 25, 521, 145, 193, 321, 641, 769, 14, 70, 266, 322, 44, 332, 52, 148, 100, 196, 56, 536, 296, 776, 176, 816, 656, 224, 352, 416, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_323, vertices_149, vertices_665, vertices_961, vertices_334, vertices_364, vertices_244, vertices_824, vertices_944, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_133, vertices_25, vertices_521, vertices_145, vertices_193, vertices_321, vertices_641, vertices_769, vertices_14, vertices_70, vertices_266, vertices_322, vertices_44, vertices_332, vertices_52, vertices_148, vertices_100, vertices_196, vertices_56, vertices_536, vertices_296, vertices_776, vertices_176, vertices_816, vertices_656, vertices_224, vertices_352, vertices_416, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_323), (false, vertices_149), (false, vertices_665), (false, vertices_961), (true, vertices_332), (true, vertices_100), (true, vertices_296), (true, vertices_176), (true, vertices_816), (true, vertices_224), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 14 16 18 19 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_199) then 9 else
  if p.val = (false, vertices_779) then 10 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_149) then 1 else
  if p.val = (false, vertices_665) then 15 else
  if p.val = (false, vertices_961) then 20 else
  if p.val = (true, vertices_332) then 13 else
  if p.val = (true, vertices_100) then 2 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_176) then 4 else
  if p.val = (true, vertices_816) then 17 else
  if p.val = (true, vertices_224) then 5 else
  if p.val = (true, vertices_352) then 6 else
  if p.val = (true, vertices_416) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_332), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 7 8 816
cert_row_2 1 1 2 5 7 332
cert_row_4 2 1 3 4 5 6 244 52 3
cert_rows_3
cert_pivot_3 2 8 1
cert_heightProof 3
cert_coverFacet 0 334
cert_cover_5 0 1 0 1 2 5 14 334 3
cert_coverFacet 1 364
cert_cover_5 1 1 1 2 4 5 44 364 3
cert_coverFacet 2 244
cert_cover_5 2 2 1 3 4 5 52 244 3
cert_coverFacet 3 824
cert_cover_5 3 0 2 3 4 7 56 824 3
cert_coverFacet 4 944
cert_cover_5 4 0 3 4 6 7 176 944 3
cert_coverFacet 5 480
cert_cover_2 5 5 4 6 7 224 480 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0176

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_one_six_0177.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0177

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 323, 149, 665, 961, 334, 364, 244, 824, 496, 912, 7, 11, 67, 259, 21, 133, 25, 521, 145, 193, 321, 641, 769, 14, 70, 266, 322, 44, 332, 52, 148, 100, 196, 56, 536, 296, 776, 240, 304, 400, 656, 784, 352, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_323, vertices_149, vertices_665, vertices_961, vertices_334, vertices_364, vertices_244, vertices_824, vertices_496, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_133, vertices_25, vertices_521, vertices_145, vertices_193, vertices_321, vertices_641, vertices_769, vertices_14, vertices_70, vertices_266, vertices_322, vertices_44, vertices_332, vertices_52, vertices_148, vertices_100, vertices_196, vertices_56, vertices_536, vertices_296, vertices_776, vertices_240, vertices_304, vertices_400, vertices_656, vertices_784, vertices_352, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_323), (false, vertices_149), (false, vertices_665), (false, vertices_961), (true, vertices_332), (true, vertices_100), (true, vertices_296), (true, vertices_240), (true, vertices_304), (true, vertices_400), (true, vertices_784), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 14 16 18 19 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_199) then 9 else
  if p.val = (false, vertices_779) then 10 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_149) then 1 else
  if p.val = (false, vertices_665) then 15 else
  if p.val = (false, vertices_961) then 20 else
  if p.val = (true, vertices_332) then 13 else
  if p.val = (true, vertices_100) then 2 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_240) then 17 else
  if p.val = (true, vertices_304) then 4 else
  if p.val = (true, vertices_400) then 5 else
  if p.val = (true, vertices_784) then 6 else
  if p.val = (true, vertices_352) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_332), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 5 6 240
cert_row_2 1 1 2 5 7 332
cert_row_4 2 2 3 4 7 8 824 56 3
cert_rows_3
cert_pivot_3 1 6 2
cert_heightProof 3
cert_coverFacet 0 334
cert_cover_5 0 1 0 1 2 5 14 334 3
cert_coverFacet 1 364
cert_cover_5 1 1 1 2 4 5 44 364 3
cert_coverFacet 2 244
cert_cover_5 2 0 1 3 4 5 52 244 3
cert_coverFacet 3 824
cert_cover_5 3 2 2 3 4 7 56 824 3
cert_coverFacet 4 496
cert_cover_5 4 0 3 4 5 7 240 496 3
cert_coverFacet 5 912
cert_cover_2 5 6 3 7 8 400 912 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0177

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_one_six_0178.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0178

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 323, 149, 665, 961, 334, 364, 628, 724, 824, 864, 7, 11, 67, 259, 21, 133, 25, 521, 145, 193, 321, 641, 769, 14, 70, 266, 322, 44, 332, 52, 596, 148, 100, 196, 56, 536, 296, 776, 560, 656, 352, 608, 800, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_323, vertices_149, vertices_665, vertices_961, vertices_334, vertices_364, vertices_628, vertices_724, vertices_824, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_133, vertices_25, vertices_521, vertices_145, vertices_193, vertices_321, vertices_641, vertices_769, vertices_14, vertices_70, vertices_266, vertices_322, vertices_44, vertices_332, vertices_52, vertices_596, vertices_148, vertices_100, vertices_196, vertices_56, vertices_536, vertices_296, vertices_776, vertices_560, vertices_656, vertices_352, vertices_608, vertices_800, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_323), (false, vertices_149), (false, vertices_665), (false, vertices_961), (true, vertices_332), (true, vertices_596), (true, vertices_100), (true, vertices_296), (true, vertices_560), (true, vertices_352), (true, vertices_608), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 15 11 17 18 19 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_199) then 9 else
  if p.val = (false, vertices_779) then 10 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_149) then 1 else
  if p.val = (false, vertices_665) then 13 else
  if p.val = (false, vertices_961) then 20 else
  if p.val = (true, vertices_332) then 14 else
  if p.val = (true, vertices_596) then 16 else
  if p.val = (true, vertices_100) then 2 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_560) then 4 else
  if p.val = (true, vertices_352) then 5 else
  if p.val = (true, vertices_608) then 6 else
  if p.val = (true, vertices_800) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 11 => Sum.inl 2
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_332), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(true, vertices_596), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 4 7 8 824 56 3
cert_row_2 1 1 3 5 8 596
cert_row_2 2 1 2 5 7 332
cert_rows_3
cert_pivot_3 3 4 1
cert_heightProof 3
cert_coverFacet 0 334
cert_cover_5 0 2 0 1 2 5 14 334 3
cert_coverFacet 1 364
cert_cover_5 1 2 1 2 4 5 44 364 3
cert_coverFacet 2 628
cert_cover_5 2 1 1 3 4 5 52 628 3
cert_coverFacet 3 724
cert_cover_5 3 1 1 3 5 6 596 724 3
cert_coverFacet 4 824
cert_cover_5 4 0 2 3 4 7 56 824 3
cert_coverFacet 5 864
cert_cover_2 5 5 4 7 8 352 864 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0178

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_one_six_0179.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0179

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 323, 149, 665, 961, 334, 364, 692, 740, 824, 864, 7, 11, 67, 259, 21, 133, 25, 521, 145, 193, 321, 641, 769, 14, 70, 266, 322, 44, 332, 52, 148, 100, 676, 196, 56, 536, 296, 776, 560, 656, 352, 608, 800, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_323, vertices_149, vertices_665, vertices_961, vertices_334, vertices_364, vertices_692, vertices_740, vertices_824, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_133, vertices_25, vertices_521, vertices_145, vertices_193, vertices_321, vertices_641, vertices_769, vertices_14, vertices_70, vertices_266, vertices_322, vertices_44, vertices_332, vertices_52, vertices_148, vertices_100, vertices_676, vertices_196, vertices_56, vertices_536, vertices_296, vertices_776, vertices_560, vertices_656, vertices_352, vertices_608, vertices_800, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_323), (false, vertices_149), (false, vertices_665), (false, vertices_961), (true, vertices_332), (true, vertices_100), (true, vertices_676), (true, vertices_296), (true, vertices_560), (true, vertices_352), (true, vertices_608), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 15 11 17 18 19 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_199) then 9 else
  if p.val = (false, vertices_779) then 10 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_149) then 1 else
  if p.val = (false, vertices_665) then 13 else
  if p.val = (false, vertices_961) then 20 else
  if p.val = (true, vertices_332) then 14 else
  if p.val = (true, vertices_100) then 2 else
  if p.val = (true, vertices_676) then 16 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_560) then 4 else
  if p.val = (true, vertices_352) then 5 else
  if p.val = (true, vertices_608) then 6 else
  if p.val = (true, vertices_800) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 11 => Sum.inl 2
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_332), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(true, vertices_676), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 6 8 676
cert_row_2 1 1 2 5 7 332
cert_row_4 2 2 3 4 7 8 824 56 3
cert_rows_3
cert_pivot_3 1 6 2
cert_heightProof 3
cert_coverFacet 0 334
cert_cover_5 0 1 0 1 2 5 14 334 3
cert_coverFacet 1 364
cert_cover_5 1 1 1 2 4 5 44 364 3
cert_coverFacet 2 692
cert_cover_5 2 0 1 3 4 6 52 692 3
cert_coverFacet 3 740
cert_cover_5 3 0 1 4 5 6 100 740 3
cert_coverFacet 4 824
cert_cover_5 4 2 2 3 4 7 56 824 3
cert_coverFacet 5 864
cert_cover_2 5 5 4 7 8 352 864 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0179

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_one_six_0180.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0180

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 323, 149, 665, 961, 334, 364, 244, 824, 752, 864, 7, 11, 67, 259, 21, 133, 25, 521, 145, 193, 321, 641, 769, 14, 70, 266, 322, 44, 332, 52, 148, 100, 196, 56, 536, 296, 776, 240, 560, 656, 352, 608, 800, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_323, vertices_149, vertices_665, vertices_961, vertices_334, vertices_364, vertices_244, vertices_824, vertices_752, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_133, vertices_25, vertices_521, vertices_145, vertices_193, vertices_321, vertices_641, vertices_769, vertices_14, vertices_70, vertices_266, vertices_322, vertices_44, vertices_332, vertices_52, vertices_148, vertices_100, vertices_196, vertices_56, vertices_536, vertices_296, vertices_776, vertices_240, vertices_560, vertices_656, vertices_352, vertices_608, vertices_800, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_323), (false, vertices_149), (false, vertices_665), (false, vertices_961), (true, vertices_332), (true, vertices_100), (true, vertices_296), (true, vertices_240), (true, vertices_560), (true, vertices_352), (true, vertices_608), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 14 16 18 19 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_199) then 9 else
  if p.val = (false, vertices_779) then 10 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_149) then 1 else
  if p.val = (false, vertices_665) then 15 else
  if p.val = (false, vertices_961) then 20 else
  if p.val = (true, vertices_332) then 13 else
  if p.val = (true, vertices_100) then 2 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_240) then 17 else
  if p.val = (true, vertices_560) then 4 else
  if p.val = (true, vertices_352) then 5 else
  if p.val = (true, vertices_608) then 6 else
  if p.val = (true, vertices_800) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_332), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 5 6 240
cert_row_2 1 1 2 5 7 332
cert_row_4 2 2 3 4 7 8 824 56 3
cert_rows_3
cert_pivot_3 1 6 2
cert_heightProof 3
cert_coverFacet 0 334
cert_cover_5 0 1 0 1 2 5 14 334 3
cert_coverFacet 1 364
cert_cover_5 1 1 1 2 4 5 44 364 3
cert_coverFacet 2 244
cert_cover_5 2 0 1 3 4 5 52 244 3
cert_coverFacet 3 824
cert_cover_5 3 2 2 3 4 7 56 824 3
cert_coverFacet 4 752
cert_cover_5 4 0 3 4 5 8 240 752 3
cert_coverFacet 5 864
cert_cover_2 5 5 4 7 8 352 864 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0180

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_one_six_0181.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0181

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 323, 149, 665, 961, 334, 364, 244, 824, 880, 720, 7, 11, 67, 259, 21, 133, 25, 521, 145, 193, 321, 641, 769, 14, 70, 266, 322, 44, 332, 52, 148, 100, 196, 56, 536, 296, 776, 112, 816, 208, 592, 656, 352, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_323, vertices_149, vertices_665, vertices_961, vertices_334, vertices_364, vertices_244, vertices_824, vertices_880, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_133, vertices_25, vertices_521, vertices_145, vertices_193, vertices_321, vertices_641, vertices_769, vertices_14, vertices_70, vertices_266, vertices_322, vertices_44, vertices_332, vertices_52, vertices_148, vertices_100, vertices_196, vertices_56, vertices_536, vertices_296, vertices_776, vertices_112, vertices_816, vertices_208, vertices_592, vertices_656, vertices_352, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_323), (false, vertices_149), (false, vertices_665), (false, vertices_961), (true, vertices_332), (true, vertices_100), (true, vertices_296), (true, vertices_112), (true, vertices_816), (true, vertices_208), (true, vertices_592), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 14 16 18 19 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_199) then 9 else
  if p.val = (false, vertices_779) then 10 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_149) then 1 else
  if p.val = (false, vertices_665) then 15 else
  if p.val = (false, vertices_961) then 20 else
  if p.val = (true, vertices_332) then 13 else
  if p.val = (true, vertices_100) then 2 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_112) then 4 else
  if p.val = (true, vertices_816) then 17 else
  if p.val = (true, vertices_208) then 5 else
  if p.val = (true, vertices_592) then 6 else
  if p.val = (true, vertices_352) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_332), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 7 8 816
cert_row_2 1 1 2 5 7 332
cert_row_4 2 1 3 4 5 6 244 52 3
cert_rows_3
cert_pivot_3 2 8 1
cert_heightProof 3
cert_coverFacet 0 334
cert_cover_5 0 1 0 1 2 5 14 334 3
cert_coverFacet 1 364
cert_cover_5 1 1 1 2 4 5 44 364 3
cert_coverFacet 2 244
cert_cover_5 2 2 1 3 4 5 52 244 3
cert_coverFacet 3 824
cert_cover_5 3 0 2 3 4 7 56 824 3
cert_coverFacet 4 880
cert_cover_5 4 0 3 4 5 7 112 880 3
cert_coverFacet 5 720
cert_cover_2 5 5 3 6 8 208 720 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0181

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_one_six_0182.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0182

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 149, 361, 241, 782, 326, 668, 964, 824, 368, 976, 7, 11, 67, 21, 133, 41, 329, 49, 145, 97, 193, 14, 70, 262, 266, 322, 28, 524, 148, 196, 324, 644, 772, 56, 536, 296, 776, 112, 304, 208, 336, 656, 784, 352, 960]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_149, vertices_361, vertices_241, vertices_782, vertices_326, vertices_668, vertices_964, vertices_824, vertices_368, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_133, vertices_41, vertices_329, vertices_49, vertices_145, vertices_97, vertices_193, vertices_14, vertices_70, vertices_262, vertices_266, vertices_322, vertices_28, vertices_524, vertices_148, vertices_196, vertices_324, vertices_644, vertices_772, vertices_56, vertices_536, vertices_296, vertices_776, vertices_112, vertices_304, vertices_208, vertices_336, vertices_656, vertices_784, vertices_352, vertices_960] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_149), (false, vertices_361), (false, vertices_241), (true, vertices_262), (true, vertices_524), (true, vertices_324), (true, vertices_644), (true, vertices_772), (true, vertices_536), (true, vertices_776), (true, vertices_304), (true, vertices_336), (true, vertices_656), (true, vertices_784), (true, vertices_960)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 16 19 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_331) then 17 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_361) then 18 else
  if p.val = (false, vertices_241) then 20 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_324) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_960) then 23 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(true, vertices_960), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 5 6 7 8 960
cert_row_4 1 0 1 2 7 8 782 14 3
cert_row_4 2 1 2 3 6 8 668 28 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 5 0 1 2
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 14 782 3
cert_coverFacet 1 326
cert_cover_2 1 1 0 5 7 70 326 3
cert_coverFacet 2 668
cert_cover_5 2 2 1 2 3 6 28 668 3
cert_coverFacet 3 964
cert_cover_5 3 0 1 5 6 7 196 964 3
cert_coverFacet 4 824
cert_cover_5 4 3 2 3 4 7 56 824 3
cert_coverFacet 5 368
cert_cover_2 5 4 3 5 7 112 368 3
cert_coverFacet 6 976
cert_cover_5 6 0 3 5 6 7 208 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0182

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_one_six_0183.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0183

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 149, 361, 241, 782, 326, 668, 964, 824, 688, 992, 7, 11, 67, 21, 133, 41, 329, 49, 145, 97, 193, 14, 70, 262, 266, 322, 28, 524, 148, 196, 324, 644, 772, 56, 536, 296, 776, 176, 560, 656, 224, 352, 672, 800, 960]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_149, vertices_361, vertices_241, vertices_782, vertices_326, vertices_668, vertices_964, vertices_824, vertices_688, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_133, vertices_41, vertices_329, vertices_49, vertices_145, vertices_97, vertices_193, vertices_14, vertices_70, vertices_262, vertices_266, vertices_322, vertices_28, vertices_524, vertices_148, vertices_196, vertices_324, vertices_644, vertices_772, vertices_56, vertices_536, vertices_296, vertices_776, vertices_176, vertices_560, vertices_656, vertices_224, vertices_352, vertices_672, vertices_800, vertices_960] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_149), (false, vertices_361), (false, vertices_241), (true, vertices_262), (true, vertices_524), (true, vertices_324), (true, vertices_644), (true, vertices_772), (true, vertices_536), (true, vertices_776), (true, vertices_560), (true, vertices_656), (true, vertices_672), (true, vertices_800), (true, vertices_960)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 16 19 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_331) then 17 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_361) then 18 else
  if p.val = (false, vertices_241) then 20 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_324) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_800) then 11 else
  if p.val = (true, vertices_960) then 23 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(true, vertices_960), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 5 6 7 8 960
cert_row_4 1 0 1 2 7 8 782 14 3
cert_row_4 2 1 2 3 6 8 668 28 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 5 0 1 2
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 14 782 3
cert_coverFacet 1 326
cert_cover_2 1 1 0 5 7 70 326 3
cert_coverFacet 2 668
cert_cover_5 2 2 1 2 3 6 28 668 3
cert_coverFacet 3 964
cert_cover_5 3 0 1 5 6 7 196 964 3
cert_coverFacet 4 824
cert_cover_5 4 3 2 3 4 7 56 824 3
cert_coverFacet 5 688
cert_cover_2 5 4 3 6 8 176 688 3
cert_coverFacet 6 992
cert_cover_5 6 0 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0183

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_one_six_0184.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0184

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 149, 361, 689, 225, 782, 326, 668, 964, 824, 992, 7, 11, 67, 21, 133, 41, 329, 49, 145, 97, 161, 193, 14, 70, 262, 266, 322, 28, 524, 148, 196, 324, 644, 772, 56, 536, 296, 776, 560, 656, 224, 352, 672, 800, 960]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_149, vertices_361, vertices_689, vertices_225, vertices_782, vertices_326, vertices_668, vertices_964, vertices_824, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_133, vertices_41, vertices_329, vertices_49, vertices_145, vertices_97, vertices_161, vertices_193, vertices_14, vertices_70, vertices_262, vertices_266, vertices_322, vertices_28, vertices_524, vertices_148, vertices_196, vertices_324, vertices_644, vertices_772, vertices_56, vertices_536, vertices_296, vertices_776, vertices_560, vertices_656, vertices_224, vertices_352, vertices_672, vertices_800, vertices_960] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_149), (false, vertices_361), (false, vertices_689), (false, vertices_225), (true, vertices_262), (true, vertices_524), (true, vertices_324), (true, vertices_644), (true, vertices_772), (true, vertices_536), (true, vertices_776), (true, vertices_800), (true, vertices_960)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 14 17 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_199) then 11 else
  if p.val = (false, vertices_331) then 15 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_361) then 16 else
  if p.val = (false, vertices_689) then 18 else
  if p.val = (false, vertices_225) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_324) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_772) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_960) then 21 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_225), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(true, vertices_960), by decide +kernel⟩
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 5 6 7 8 960
cert_row_4 1 0 1 2 7 8 782 14 3
cert_row_4 2 1 2 3 6 8 668 28 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 5 0 1 2
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 14 782 3
cert_coverFacet 1 326
cert_cover_2 1 1 0 5 7 70 326 3
cert_coverFacet 2 668
cert_cover_5 2 2 1 2 3 6 28 668 3
cert_coverFacet 3 964
cert_cover_5 3 0 1 5 6 7 196 964 3
cert_coverFacet 4 824
cert_cover_5 4 3 2 3 4 7 56 824 3
cert_coverFacet 5 992
cert_cover_5 5 0 4 5 6 7 224 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0184

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_one_six_0206.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0206

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 587, 405, 233, 433, 782, 838, 284, 452, 824, 616, 992, 7, 11, 67, 21, 133, 41, 73, 49, 401, 161, 193, 14, 70, 774, 522, 578, 28, 268, 276, 196, 324, 388, 56, 280, 104, 552, 584, 776, 304, 224, 608, 416, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_587, vertices_405, vertices_233, vertices_433, vertices_782, vertices_838, vertices_284, vertices_452, vertices_824, vertices_616, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_133, vertices_41, vertices_73, vertices_49, vertices_401, vertices_161, vertices_193, vertices_14, vertices_70, vertices_774, vertices_522, vertices_578, vertices_28, vertices_268, vertices_276, vertices_196, vertices_324, vertices_388, vertices_56, vertices_280, vertices_104, vertices_552, vertices_584, vertices_776, vertices_304, vertices_224, vertices_608, vertices_416, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_587), (false, vertices_405), (false, vertices_233), (false, vertices_433), (true, vertices_774), (true, vertices_268), (true, vertices_324), (true, vertices_280), (true, vertices_552), (true, vertices_776), (true, vertices_608), (true, vertices_800), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 9 12 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_199) then 17 else
  if p.val = (false, vertices_587) then 10 else
  if p.val = (false, vertices_405) then 14 else
  if p.val = (false, vertices_233) then 11 else
  if p.val = (false, vertices_433) then 15 else
  if p.val = (true, vertices_774) then 18 else
  if p.val = (true, vertices_268) then 0 else
  if p.val = (true, vertices_324) then 1 else
  if p.val = (true, vertices_280) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_776) then 4 else
  if p.val = (true, vertices_608) then 5 else
  if p.val = (true, vertices_800) then 6 else
  if p.val = (true, vertices_448) then 7 else
  if p.val = (true, vertices_832) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 9 => Sum.inl 2
  | 10 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 12 => Sum.inl 3
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 7 8 774
cert_row_4 1 2 3 4 7 8 824 56 3
cert_row_4 2 4 5 6 7 8 992 224 3
cert_rows_3
cert_pivot_3 2 0 4
cert_heightProof 3
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 838
cert_cover_5 1 0 0 1 5 7 70 838 3
cert_coverFacet 2 284
cert_cover_2 2 2 1 3 7 28 284 3
cert_coverFacet 3 452
cert_cover_2 3 5 1 6 7 196 452 3
cert_coverFacet 4 824
cert_cover_5 4 1 2 3 4 7 56 824 3
cert_coverFacet 5 616
cert_cover_2 5 4 2 5 8 104 616 3
cert_coverFacet 6 992
cert_cover_5 6 2 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0206

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_one_six_0207.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0207

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 835, 589, 150, 410, 450, 556, 244, 868, 824, 496, 7, 11, 67, 771, 13, 69, 521, 577, 22, 134, 26, 266, 146, 194, 322, 386, 44, 524, 52, 148, 100, 548, 196, 580, 56, 280, 552, 776, 240, 304, 400, 352, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_835, vertices_589, vertices_150, vertices_410, vertices_450, vertices_556, vertices_244, vertices_868, vertices_824, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_771, vertices_13, vertices_69, vertices_521, vertices_577, vertices_22, vertices_134, vertices_26, vertices_266, vertices_146, vertices_194, vertices_322, vertices_386, vertices_44, vertices_524, vertices_52, vertices_148, vertices_100, vertices_548, vertices_196, vertices_580, vertices_56, vertices_280, vertices_552, vertices_776, vertices_240, vertices_304, vertices_400, vertices_352, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_835), (false, vertices_589), (true, vertices_146), (true, vertices_386), (true, vertices_148), (true, vertices_100), (true, vertices_548), (true, vertices_280), (true, vertices_552), (true, vertices_240), (true, vertices_304), (true, vertices_400), (true, vertices_352), (true, vertices_800), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 12 19 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_589) then 14 else
  if p.val = (true, vertices_146) then 0 else
  if p.val = (true, vertices_386) then 1 else
  if p.val = (true, vertices_148) then 2 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_240) then 21 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_352) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_448) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 7 410 26 3
cert_row_2 1 3 4 5 6 240
cert_row_4 2 1 4 5 7 8 868 100 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 150
cert_cover_2 0 1 0 3 6 22 150 3
cert_coverFacet 1 410
cert_cover_5 1 0 0 2 3 6 26 410 3
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
cert_coverFacet 3 556
cert_cover_2 3 2 1 4 8 44 556 3
cert_coverFacet 4 244
cert_cover_5 4 1 1 3 4 5 52 244 3
cert_coverFacet 5 868
cert_cover_5 5 2 1 4 5 7 100 868 3
cert_coverFacet 6 824
cert_cover_5 6 3 2 3 4 7 56 824 3
cert_coverFacet 7 496
cert_cover_5 7 1 3 4 5 7 240 496 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0207

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_one_six_0208.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0208

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 835, 589, 150, 410, 450, 556, 436, 740, 824, 992, 7, 11, 67, 771, 13, 69, 521, 577, 22, 134, 26, 266, 146, 194, 322, 386, 44, 524, 52, 148, 164, 548, 196, 580, 56, 280, 552, 776, 304, 400, 736, 416, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_835, vertices_589, vertices_150, vertices_410, vertices_450, vertices_556, vertices_436, vertices_740, vertices_824, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_771, vertices_13, vertices_69, vertices_521, vertices_577, vertices_22, vertices_134, vertices_26, vertices_266, vertices_146, vertices_194, vertices_322, vertices_386, vertices_44, vertices_524, vertices_52, vertices_148, vertices_164, vertices_548, vertices_196, vertices_580, vertices_56, vertices_280, vertices_552, vertices_776, vertices_304, vertices_400, vertices_736, vertices_416, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_835), (false, vertices_589), (true, vertices_146), (true, vertices_386), (true, vertices_148), (true, vertices_164), (true, vertices_548), (true, vertices_280), (true, vertices_552), (true, vertices_304), (true, vertices_400), (true, vertices_736), (true, vertices_416), (true, vertices_800), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 12 19 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_589) then 14 else
  if p.val = (true, vertices_146) then 0 else
  if p.val = (true, vertices_386) then 1 else
  if p.val = (true, vertices_148) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_736) then 22 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_448) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(true, vertices_736), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 4 5 6 8 736
cert_row_4 1 0 2 3 6 7 410 26 3
cert_row_4 2 1 3 4 6 7 436 52 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 5 0 1 2
cert_heightProof 4
cert_coverFacet 0 150
cert_cover_2 0 1 0 3 6 22 150 3
cert_coverFacet 1 410
cert_cover_5 1 1 0 2 3 6 26 410 3
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
cert_coverFacet 3 556
cert_cover_2 3 2 1 4 8 44 556 3
cert_coverFacet 4 436
cert_cover_5 4 2 1 3 4 6 52 436 3
cert_coverFacet 5 740
cert_cover_5 5 0 1 4 5 6 164 740 2
cert_coverFacet 6 824
cert_cover_5 6 3 2 3 4 7 56 824 3
cert_coverFacet 7 992
cert_cover_5 7 0 4 5 6 7 736 992 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0208

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_one_six_0209.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0209

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 587, 149, 809, 689, 705, 782, 838, 412, 452, 440, 992, 7, 11, 67, 21, 133, 41, 521, 49, 145, 545, 193, 577, 641, 14, 70, 774, 522, 578, 28, 268, 148, 196, 324, 388, 56, 408, 296, 776, 176, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_587, vertices_149, vertices_809, vertices_689, vertices_705, vertices_782, vertices_838, vertices_412, vertices_452, vertices_440, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_133, vertices_41, vertices_521, vertices_49, vertices_145, vertices_545, vertices_193, vertices_577, vertices_641, vertices_14, vertices_70, vertices_774, vertices_522, vertices_578, vertices_28, vertices_268, vertices_148, vertices_196, vertices_324, vertices_388, vertices_56, vertices_408, vertices_296, vertices_776, vertices_176, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_587), (false, vertices_149), (false, vertices_809), (false, vertices_689), (false, vertices_705), (true, vertices_774), (true, vertices_268), (true, vertices_324), (true, vertices_388), (true, vertices_408), (true, vertices_416), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 11 8 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_199) then 16 else
  if p.val = (false, vertices_587) then 13 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_809) then 14 else
  if p.val = (false, vertices_689) then 9 else
  if p.val = (false, vertices_705) then 1 else
  if p.val = (true, vertices_774) then 17 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_324) then 3 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_408) then 10 else
  if p.val = (true, vertices_416) then 5 else
  if p.val = (true, vertices_448) then 6 else
  if p.val = (true, vertices_832) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_705), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 8 => Sum.inl 3
  | 9 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
  | 11 => Sum.inl 2
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 6 7 408
cert_row_2 1 0 1 7 8 774
cert_row_4 2 4 5 6 7 8 992 416 1
cert_rows_3
cert_pivot_3 0 2 4
cert_heightProof 3
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 14 782 3
cert_coverFacet 1 838
cert_cover_5 1 1 0 1 5 7 70 838 3
cert_coverFacet 2 412
cert_cover_5 2 0 1 2 3 6 28 412 3
cert_coverFacet 3 452
cert_cover_2 3 5 1 6 7 196 452 3
cert_coverFacet 4 440
cert_cover_5 4 0 2 3 4 6 56 440 3
cert_coverFacet 5 992
cert_cover_5 5 2 4 5 6 7 416 992 1
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0209

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_one_six_0210.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0210

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 587, 149, 809, 241, 609, 782, 838, 412, 452, 440, 992, 7, 11, 67, 21, 133, 41, 521, 49, 145, 97, 545, 193, 577, 14, 70, 774, 522, 578, 28, 268, 148, 196, 324, 388, 56, 408, 296, 776, 176, 224, 608, 416, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_587, vertices_149, vertices_809, vertices_241, vertices_609, vertices_782, vertices_838, vertices_412, vertices_452, vertices_440, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_133, vertices_41, vertices_521, vertices_49, vertices_145, vertices_97, vertices_545, vertices_193, vertices_577, vertices_14, vertices_70, vertices_774, vertices_522, vertices_578, vertices_28, vertices_268, vertices_148, vertices_196, vertices_324, vertices_388, vertices_56, vertices_408, vertices_296, vertices_776, vertices_176, vertices_224, vertices_608, vertices_416, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_587), (false, vertices_149), (false, vertices_809), (false, vertices_241), (false, vertices_609), (true, vertices_774), (true, vertices_268), (true, vertices_324), (true, vertices_388), (true, vertices_408), (true, vertices_416), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 11 8 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_199) then 16 else
  if p.val = (false, vertices_587) then 13 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_809) then 14 else
  if p.val = (false, vertices_241) then 9 else
  if p.val = (false, vertices_609) then 1 else
  if p.val = (true, vertices_774) then 17 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_324) then 3 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_408) then 10 else
  if p.val = (true, vertices_416) then 5 else
  if p.val = (true, vertices_448) then 6 else
  if p.val = (true, vertices_832) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_609), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 8 => Sum.inl 3
  | 9 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
  | 11 => Sum.inl 2
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 6 7 408
cert_row_2 1 0 1 7 8 774
cert_row_4 2 4 5 6 7 8 992 224 3
cert_rows_3
cert_pivot_3 0 2 4
cert_heightProof 3
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 14 782 3
cert_coverFacet 1 838
cert_cover_5 1 1 0 1 5 7 70 838 3
cert_coverFacet 2 412
cert_cover_5 2 0 1 2 3 6 28 412 3
cert_coverFacet 3 452
cert_cover_2 3 5 1 6 7 196 452 3
cert_coverFacet 4 440
cert_cover_5 4 0 2 3 4 6 56 440 3
cert_coverFacet 5 992
cert_cover_5 5 2 4 5 6 7 224 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0210

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_one_six_0211.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0211

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 587, 405, 681, 433, 705, 782, 838, 284, 452, 824, 992, 7, 11, 67, 21, 133, 41, 521, 49, 401, 161, 193, 577, 641, 14, 70, 774, 522, 578, 28, 268, 276, 196, 324, 388, 56, 280, 552, 776, 304, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_587, vertices_405, vertices_681, vertices_433, vertices_705, vertices_782, vertices_838, vertices_284, vertices_452, vertices_824, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_133, vertices_41, vertices_521, vertices_49, vertices_401, vertices_161, vertices_193, vertices_577, vertices_641, vertices_14, vertices_70, vertices_774, vertices_522, vertices_578, vertices_28, vertices_268, vertices_276, vertices_196, vertices_324, vertices_388, vertices_56, vertices_280, vertices_552, vertices_776, vertices_304, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_587), (false, vertices_405), (false, vertices_681), (false, vertices_433), (false, vertices_705), (true, vertices_774), (true, vertices_268), (true, vertices_324), (true, vertices_280), (true, vertices_776), (true, vertices_800), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 8 11 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_199) then 16 else
  if p.val = (false, vertices_587) then 9 else
  if p.val = (false, vertices_405) then 13 else
  if p.val = (false, vertices_681) then 10 else
  if p.val = (false, vertices_433) then 14 else
  if p.val = (false, vertices_705) then 0 else
  if p.val = (true, vertices_774) then 17 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_324) then 2 else
  if p.val = (true, vertices_280) then 3 else
  if p.val = (true, vertices_776) then 4 else
  if p.val = (true, vertices_800) then 5 else
  if p.val = (true, vertices_448) then 6 else
  if p.val = (true, vertices_832) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_705), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 8 => Sum.inl 2
  | 9 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 11 => Sum.inl 3
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 7 8 774
cert_row_4 1 2 3 4 7 8 824 56 3
cert_row_4 2 4 5 6 7 8 992 416 1
cert_rows_3
cert_pivot_3 2 0 4
cert_heightProof 3
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 838
cert_cover_5 1 0 0 1 5 7 70 838 3
cert_coverFacet 2 284
cert_cover_2 2 2 1 3 7 28 284 3
cert_coverFacet 3 452
cert_cover_2 3 5 1 6 7 196 452 3
cert_coverFacet 4 824
cert_cover_5 4 1 2 3 4 7 56 824 3
cert_coverFacet 5 992
cert_cover_5 5 2 4 5 6 7 416 992 1
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0211

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_one_six_0212.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0212

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 835, 589, 150, 282, 466, 556, 692, 964, 440, 936, 7, 11, 67, 771, 13, 69, 521, 577, 22, 134, 26, 266, 146, 274, 194, 322, 44, 524, 52, 148, 548, 196, 580, 644, 56, 280, 424, 552, 776, 176, 400, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_835, vertices_589, vertices_150, vertices_282, vertices_466, vertices_556, vertices_692, vertices_964, vertices_440, vertices_936] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_771, vertices_13, vertices_69, vertices_521, vertices_577, vertices_22, vertices_134, vertices_26, vertices_266, vertices_146, vertices_274, vertices_194, vertices_322, vertices_44, vertices_524, vertices_52, vertices_148, vertices_548, vertices_196, vertices_580, vertices_644, vertices_56, vertices_280, vertices_424, vertices_552, vertices_776, vertices_176, vertices_400, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_835), (false, vertices_589), (true, vertices_146), (true, vertices_274), (true, vertices_148), (true, vertices_548), (true, vertices_644), (true, vertices_280), (true, vertices_424), (true, vertices_552), (true, vertices_176), (true, vertices_400), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 12 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_589) then 14 else
  if p.val = (true, vertices_146) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_148) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_424) then 20 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(true, vertices_424), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 4 6 7 424
cert_row_4 1 0 3 5 6 7 466 146 2
cert_row_4 2 1 3 4 6 8 692 52 3
cert_row_4 3 1 5 6 7 8 964 196 3
cert_rows
cert_pivot_2 2 0 3 1
cert_heightProof 4
cert_coverFacet 0 150
cert_cover_2 0 1 0 3 6 22 150 3
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 466
cert_cover_5 2 1 0 3 5 6 146 466 2
cert_coverFacet 3 556
cert_cover_2 3 2 1 4 8 44 556 3
cert_coverFacet 4 692
cert_cover_5 4 2 1 3 4 6 52 692 3
cert_coverFacet 5 964
cert_cover_5 5 3 1 5 6 7 196 964 3
cert_coverFacet 6 440
cert_cover_5 6 0 2 3 4 6 56 440 3
cert_coverFacet 7 936
cert_cover_5 7 0 2 4 6 8 424 936 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0212

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_one_six_0213.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0213

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 835, 589, 150, 282, 466, 556, 436, 740, 824, 992, 7, 11, 67, 771, 13, 69, 521, 577, 22, 134, 26, 266, 146, 274, 194, 322, 44, 524, 52, 148, 164, 548, 196, 580, 56, 280, 552, 776, 304, 400, 736, 416, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_835, vertices_589, vertices_150, vertices_282, vertices_466, vertices_556, vertices_436, vertices_740, vertices_824, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_771, vertices_13, vertices_69, vertices_521, vertices_577, vertices_22, vertices_134, vertices_26, vertices_266, vertices_146, vertices_274, vertices_194, vertices_322, vertices_44, vertices_524, vertices_52, vertices_148, vertices_164, vertices_548, vertices_196, vertices_580, vertices_56, vertices_280, vertices_552, vertices_776, vertices_304, vertices_400, vertices_736, vertices_416, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_835), (false, vertices_589), (true, vertices_146), (true, vertices_274), (true, vertices_148), (true, vertices_164), (true, vertices_548), (true, vertices_280), (true, vertices_552), (true, vertices_304), (true, vertices_400), (true, vertices_736), (true, vertices_416), (true, vertices_800), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 12 19 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_589) then 14 else
  if p.val = (true, vertices_146) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_148) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_736) then 22 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_448) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(true, vertices_736), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 6 7 466 146 2
cert_row_2 1 4 5 6 8 736
cert_row_4 2 1 3 4 6 7 436 52 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 150
cert_cover_2 0 1 0 3 6 22 150 3
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 466
cert_cover_5 2 0 0 3 5 6 146 466 2
cert_coverFacet 3 556
cert_cover_2 3 2 1 4 8 44 556 3
cert_coverFacet 4 436
cert_cover_5 4 2 1 3 4 6 52 436 3
cert_coverFacet 5 740
cert_cover_5 5 1 1 4 5 6 164 740 2
cert_coverFacet 6 824
cert_cover_5 6 3 2 3 4 7 56 824 3
cert_coverFacet 7 992
cert_cover_5 7 1 4 5 6 7 736 992 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0213

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_one_six_0214.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0214

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 587, 149, 617, 433, 225, 782, 838, 412, 452, 824, 992, 7, 11, 67, 21, 133, 41, 585, 49, 145, 97, 161, 193, 14, 70, 774, 522, 578, 28, 268, 148, 196, 324, 388, 56, 280, 552, 776, 304, 400, 224, 608, 416, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_587, vertices_149, vertices_617, vertices_433, vertices_225, vertices_782, vertices_838, vertices_412, vertices_452, vertices_824, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_133, vertices_41, vertices_585, vertices_49, vertices_145, vertices_97, vertices_161, vertices_193, vertices_14, vertices_70, vertices_774, vertices_522, vertices_578, vertices_28, vertices_268, vertices_148, vertices_196, vertices_324, vertices_388, vertices_56, vertices_280, vertices_552, vertices_776, vertices_304, vertices_400, vertices_224, vertices_608, vertices_416, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_587), (false, vertices_149), (false, vertices_617), (false, vertices_433), (false, vertices_225), (true, vertices_774), (true, vertices_268), (true, vertices_324), (true, vertices_388), (true, vertices_280), (true, vertices_776), (true, vertices_800), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 10 13 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 17 else
  if p.val = (false, vertices_587) then 11 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_617) then 12 else
  if p.val = (false, vertices_433) then 15 else
  if p.val = (false, vertices_225) then 1 else
  if p.val = (true, vertices_774) then 18 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_324) then 3 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_800) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_225), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 2
  | 11 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 13 => Sum.inl 3
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 7 8 774
cert_row_4 1 1 2 3 6 7 412 28 3
cert_row_4 2 2 3 4 7 8 824 56 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 838
cert_cover_5 1 0 0 1 5 7 70 838 3
cert_coverFacet 2 412
cert_cover_5 2 1 1 2 3 6 28 412 3
cert_coverFacet 3 452
cert_cover_2 3 5 1 6 7 196 452 3
cert_coverFacet 4 824
cert_cover_5 4 2 2 3 4 7 56 824 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 224 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0214

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_one_six_0215.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0215

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 587, 149, 617, 241, 782, 838, 412, 452, 824, 432, 992, 7, 11, 67, 21, 133, 41, 585, 49, 145, 97, 193, 14, 70, 774, 522, 578, 28, 268, 148, 196, 324, 388, 56, 280, 552, 776, 176, 304, 400, 224, 608, 416, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_587, vertices_149, vertices_617, vertices_241, vertices_782, vertices_838, vertices_412, vertices_452, vertices_824, vertices_432, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_133, vertices_41, vertices_585, vertices_49, vertices_145, vertices_97, vertices_193, vertices_14, vertices_70, vertices_774, vertices_522, vertices_578, vertices_28, vertices_268, vertices_148, vertices_196, vertices_324, vertices_388, vertices_56, vertices_280, vertices_552, vertices_776, vertices_176, vertices_304, vertices_400, vertices_224, vertices_608, vertices_416, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_587), (false, vertices_149), (false, vertices_617), (false, vertices_241), (true, vertices_774), (true, vertices_268), (true, vertices_324), (true, vertices_388), (true, vertices_280), (true, vertices_776), (true, vertices_304), (true, vertices_400), (true, vertices_416), (true, vertices_800), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 21 12 15 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 19 else
  if p.val = (false, vertices_587) then 13 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_617) then 14 else
  if p.val = (false, vertices_241) then 17 else
  if p.val = (true, vertices_774) then 20 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_324) then 2 else
  if p.val = (true, vertices_388) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_400) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 2
  | 13 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 7 8 774
cert_row_4 1 1 2 3 6 7 412 28 3
cert_row_4 2 2 3 4 7 8 824 56 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 838
cert_cover_5 1 0 0 1 5 7 70 838 3
cert_coverFacet 2 412
cert_cover_5 2 1 1 2 3 6 28 412 3
cert_coverFacet 3 452
cert_cover_2 3 5 1 6 7 196 452 3
cert_coverFacet 4 824
cert_cover_5 4 2 2 3 4 7 56 824 3
cert_coverFacet 5 432
cert_cover_2 5 4 3 6 7 176 432 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0215

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_one_six_0216.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0216

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 587, 149, 617, 241, 782, 838, 412, 452, 696, 904, 992, 7, 11, 67, 21, 133, 41, 585, 49, 145, 97, 193, 14, 70, 774, 522, 578, 28, 268, 148, 196, 324, 388, 56, 152, 552, 392, 648, 776, 176, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_587, vertices_149, vertices_617, vertices_241, vertices_782, vertices_838, vertices_412, vertices_452, vertices_696, vertices_904, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_133, vertices_41, vertices_585, vertices_49, vertices_145, vertices_97, vertices_193, vertices_14, vertices_70, vertices_774, vertices_522, vertices_578, vertices_28, vertices_268, vertices_148, vertices_196, vertices_324, vertices_388, vertices_56, vertices_152, vertices_552, vertices_392, vertices_648, vertices_776, vertices_176, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_587), (false, vertices_149), (false, vertices_617), (false, vertices_241), (true, vertices_774), (true, vertices_268), (true, vertices_324), (true, vertices_388), (true, vertices_152), (true, vertices_392), (true, vertices_648), (true, vertices_776), (true, vertices_672), (true, vertices_448), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 21 12 15 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 19 else
  if p.val = (false, vertices_587) then 13 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_617) then 14 else
  if p.val = (false, vertices_241) then 17 else
  if p.val = (true, vertices_774) then 20 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_324) then 2 else
  if p.val = (true, vertices_388) then 3 else
  if p.val = (true, vertices_152) then 4 else
  if p.val = (true, vertices_392) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_832) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 2
  | 13 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 7 8 774
cert_row_4 1 1 2 3 6 7 412 28 3
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 838
cert_cover_5 1 0 0 1 5 7 70 838 3
cert_coverFacet 2 412
cert_cover_5 2 1 1 2 3 6 28 412 3
cert_coverFacet 3 452
cert_cover_2 3 5 1 6 7 196 452 3
cert_coverFacet 4 696
cert_cover_5 4 2 2 3 4 6 56 696 3
cert_coverFacet 5 904
cert_cover_2 5 6 2 7 8 392 904 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0216

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_one_six_0217.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0217

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 587, 405, 617, 241, 782, 838, 284, 452, 440, 808, 992, 7, 11, 67, 21, 133, 41, 585, 49, 145, 97, 193, 14, 70, 774, 522, 578, 28, 268, 276, 196, 324, 388, 56, 280, 296, 552, 776, 176, 400, 224, 608, 416, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_587, vertices_405, vertices_617, vertices_241, vertices_782, vertices_838, vertices_284, vertices_452, vertices_440, vertices_808, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_133, vertices_41, vertices_585, vertices_49, vertices_145, vertices_97, vertices_193, vertices_14, vertices_70, vertices_774, vertices_522, vertices_578, vertices_28, vertices_268, vertices_276, vertices_196, vertices_324, vertices_388, vertices_56, vertices_280, vertices_296, vertices_552, vertices_776, vertices_176, vertices_400, vertices_224, vertices_608, vertices_416, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_587), (false, vertices_405), (false, vertices_617), (false, vertices_241), (true, vertices_774), (true, vertices_268), (true, vertices_324), (true, vertices_280), (true, vertices_296), (true, vertices_776), (true, vertices_416), (true, vertices_800), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 9 12 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_199) then 17 else
  if p.val = (false, vertices_587) then 10 else
  if p.val = (false, vertices_405) then 14 else
  if p.val = (false, vertices_617) then 11 else
  if p.val = (false, vertices_241) then 15 else
  if p.val = (true, vertices_774) then 18 else
  if p.val = (true, vertices_268) then 0 else
  if p.val = (true, vertices_324) then 1 else
  if p.val = (true, vertices_280) then 2 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_776) then 4 else
  if p.val = (true, vertices_416) then 5 else
  if p.val = (true, vertices_800) then 6 else
  if p.val = (true, vertices_448) then 7 else
  if p.val = (true, vertices_832) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 9 => Sum.inl 2
  | 10 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 12 => Sum.inl 3
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 7 8 774
cert_row_4 1 2 3 4 6 7 440 56 3
cert_row_4 2 4 5 6 7 8 992 224 3
cert_rows_3
cert_pivot_3 2 0 4
cert_heightProof 3
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 838
cert_cover_5 1 0 0 1 5 7 70 838 3
cert_coverFacet 2 284
cert_cover_2 2 2 1 3 7 28 284 3
cert_coverFacet 3 452
cert_cover_2 3 5 1 6 7 196 452 3
cert_coverFacet 4 440
cert_cover_5 4 1 2 3 4 6 56 440 3
cert_coverFacet 5 808
cert_cover_2 5 4 2 7 8 296 808 3
cert_coverFacet 6 992
cert_cover_5 6 2 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0217

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_one_six_0218.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0218

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 587, 405, 617, 241, 782, 838, 284, 452, 824, 432, 992, 7, 11, 67, 21, 133, 41, 585, 49, 145, 97, 193, 14, 70, 774, 522, 578, 28, 268, 276, 196, 324, 388, 56, 280, 552, 776, 176, 304, 400, 224, 608, 416, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_587, vertices_405, vertices_617, vertices_241, vertices_782, vertices_838, vertices_284, vertices_452, vertices_824, vertices_432, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_133, vertices_41, vertices_585, vertices_49, vertices_145, vertices_97, vertices_193, vertices_14, vertices_70, vertices_774, vertices_522, vertices_578, vertices_28, vertices_268, vertices_276, vertices_196, vertices_324, vertices_388, vertices_56, vertices_280, vertices_552, vertices_776, vertices_176, vertices_304, vertices_400, vertices_224, vertices_608, vertices_416, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_587), (false, vertices_405), (false, vertices_617), (false, vertices_241), (true, vertices_774), (true, vertices_268), (true, vertices_324), (true, vertices_280), (true, vertices_776), (true, vertices_304), (true, vertices_416), (true, vertices_800), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 9 12 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_199) then 17 else
  if p.val = (false, vertices_587) then 10 else
  if p.val = (false, vertices_405) then 14 else
  if p.val = (false, vertices_617) then 11 else
  if p.val = (false, vertices_241) then 15 else
  if p.val = (true, vertices_774) then 18 else
  if p.val = (true, vertices_268) then 0 else
  if p.val = (true, vertices_324) then 1 else
  if p.val = (true, vertices_280) then 2 else
  if p.val = (true, vertices_776) then 3 else
  if p.val = (true, vertices_304) then 4 else
  if p.val = (true, vertices_416) then 5 else
  if p.val = (true, vertices_800) then 6 else
  if p.val = (true, vertices_448) then 7 else
  if p.val = (true, vertices_832) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 9 => Sum.inl 2
  | 10 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 12 => Sum.inl 3
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 7 8 774
cert_row_4 1 2 3 4 7 8 824 56 3
cert_row_4 2 4 5 6 7 8 992 224 3
cert_rows_3
cert_pivot_3 2 0 4
cert_heightProof 3
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 838
cert_cover_5 1 0 0 1 5 7 70 838 3
cert_coverFacet 2 284
cert_cover_2 2 2 1 3 7 28 284 3
cert_coverFacet 3 452
cert_cover_2 3 5 1 6 7 196 452 3
cert_coverFacet 4 824
cert_cover_5 4 1 2 3 4 7 56 824 3
cert_coverFacet 5 432
cert_cover_2 5 4 3 6 7 176 432 3
cert_coverFacet 6 992
cert_cover_5 6 2 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0218

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_one_six_0219.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0219

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 587, 149, 617, 433, 225, 782, 838, 284, 468, 824, 992, 7, 11, 67, 21, 133, 41, 585, 49, 145, 97, 161, 193, 14, 70, 774, 522, 578, 28, 268, 148, 276, 196, 324, 56, 280, 552, 776, 304, 400, 224, 608, 416, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_587, vertices_149, vertices_617, vertices_433, vertices_225, vertices_782, vertices_838, vertices_284, vertices_468, vertices_824, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_133, vertices_41, vertices_585, vertices_49, vertices_145, vertices_97, vertices_161, vertices_193, vertices_14, vertices_70, vertices_774, vertices_522, vertices_578, vertices_28, vertices_268, vertices_148, vertices_276, vertices_196, vertices_324, vertices_56, vertices_280, vertices_552, vertices_776, vertices_304, vertices_400, vertices_224, vertices_608, vertices_416, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_587), (false, vertices_149), (false, vertices_617), (false, vertices_433), (false, vertices_225), (true, vertices_774), (true, vertices_268), (true, vertices_276), (true, vertices_324), (true, vertices_280), (true, vertices_776), (true, vertices_800), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 10 13 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 17 else
  if p.val = (false, vertices_587) then 11 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_617) then 12 else
  if p.val = (false, vertices_433) then 15 else
  if p.val = (false, vertices_225) then 1 else
  if p.val = (true, vertices_774) then 18 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_324) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_800) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_225), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 2
  | 11 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 13 => Sum.inl 3
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 7 8 774
cert_row_4 1 1 3 5 6 7 468 148 2
cert_row_4 2 2 3 4 7 8 824 56 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 1 2 4
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
cert_cover_5 4 2 2 3 4 7 56 824 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 224 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0219

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_0810 : Certifies 810 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0169.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0811 : Certifies 811 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0170.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0812 : Certifies 812 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0171.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0813 : Certifies 813 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0172.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0814 : Certifies 814 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0173.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0815 : Certifies 815 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0174.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0816 : Certifies 816 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0175.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0817 : Certifies 817 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0176.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0818 : Certifies 818 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0177.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0819 : Certifies 819 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0178.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0820 : Certifies 820 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0179.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0821 : Certifies 821 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0180.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0822 : Certifies 822 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0181.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0823 : Certifies 823 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0182.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0824 : Certifies 824 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0183.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0825 : Certifies 825 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0184.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0826 : Certifies 826 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0206.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0827 : Certifies 827 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0207.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0828 : Certifies 828 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0208.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0829 : Certifies 829 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0209.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0830 : Certifies 830 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0210.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0831 : Certifies 831 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0211.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0832 : Certifies 832 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0212.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0833 : Certifies 833 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0213.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0834 : Certifies 834 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0214.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0835 : Certifies 835 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0215.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0836 : Certifies 836 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0216.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0837 : Certifies 837 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0217.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0838 : Certifies 838 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0218.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0839 : Certifies 839 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0219.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B027 (j : Fin 30) :
    Certifies (810 + j.val) := by
  fin_cases j
  · exact projection_0810
  · exact projection_0811
  · exact projection_0812
  · exact projection_0813
  · exact projection_0814
  · exact projection_0815
  · exact projection_0816
  · exact projection_0817
  · exact projection_0818
  · exact projection_0819
  · exact projection_0820
  · exact projection_0821
  · exact projection_0822
  · exact projection_0823
  · exact projection_0824
  · exact projection_0825
  · exact projection_0826
  · exact projection_0827
  · exact projection_0828
  · exact projection_0829
  · exact projection_0830
  · exact projection_0831
  · exact projection_0832
  · exact projection_0833
  · exact projection_0834
  · exact projection_0835
  · exact projection_0836
  · exact projection_0837
  · exact projection_0838
  · exact projection_0839

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
