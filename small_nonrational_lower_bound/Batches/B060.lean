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
/- Source: ProjectionCertificates/R_one_six_1658.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1658

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 267, 899, 93, 457, 678, 810, 820, 852, 708, 376, 960, 7, 11, 131, 259, 29, 69, 73, 265, 193, 385, 38, 134, 42, 266, 546, 642, 770, 52, 84, 788, 548, 196, 580, 644, 56, 88, 296, 328, 304, 336, 800, 448, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_267, vertices_899, vertices_93, vertices_457, vertices_678, vertices_810, vertices_820, vertices_852, vertices_708, vertices_376, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_29, vertices_69, vertices_73, vertices_265, vertices_193, vertices_385, vertices_38, vertices_134, vertices_42, vertices_266, vertices_546, vertices_642, vertices_770, vertices_52, vertices_84, vertices_788, vertices_548, vertices_196, vertices_580, vertices_644, vertices_56, vertices_88, vertices_296, vertices_328, vertices_304, vertices_336, vertices_800, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_267), (false, vertices_899), (false, vertices_93), (false, vertices_457), (true, vertices_546), (true, vertices_788), (true, vertices_548), (true, vertices_580), (true, vertices_644), (true, vertices_296), (true, vertices_304), (true, vertices_336), (true, vertices_800), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 18 14 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_899) then 13 else
  if p.val = (false, vertices_93) then 16 else
  if p.val = (false, vertices_457) then 17 else
  if p.val = (true, vertices_546) then 1 else
  if p.val = (true, vertices_788) then 19 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_580) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(true, vertices_788), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 38 3
cert_row_2 1 1 3 7 8 788
cert_row_4 2 0 2 4 7 8 810 42 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 6 1 0 2
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 38 678 3
cert_coverFacet 1 810
cert_cover_5 1 2 0 2 4 7 42 810 3
cert_coverFacet 2 820
cert_cover_5 2 1 1 3 4 7 52 820 3
cert_coverFacet 3 852
cert_cover_5 3 1 1 3 5 7 84 852 3
cert_coverFacet 4 708
cert_cover_2 4 5 1 6 8 196 708 3
cert_coverFacet 5 376
cert_cover_5 5 3 2 3 4 5 56 376 3
cert_coverFacet 6 960
cert_cover_2 6 6 5 7 8 448 960 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1658

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_one_six_1659.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1659

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 267, 899, 93, 457, 678, 810, 564, 724, 376, 880, 960, 7, 11, 131, 259, 29, 69, 73, 265, 193, 385, 38, 134, 42, 266, 546, 642, 770, 52, 84, 532, 548, 196, 644, 56, 88, 296, 328, 368, 560, 592, 800, 448, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_267, vertices_899, vertices_93, vertices_457, vertices_678, vertices_810, vertices_564, vertices_724, vertices_376, vertices_880, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_29, vertices_69, vertices_73, vertices_265, vertices_193, vertices_385, vertices_38, vertices_134, vertices_42, vertices_266, vertices_546, vertices_642, vertices_770, vertices_52, vertices_84, vertices_532, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_296, vertices_328, vertices_368, vertices_560, vertices_592, vertices_800, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_267), (false, vertices_899), (false, vertices_93), (false, vertices_457), (true, vertices_546), (true, vertices_532), (true, vertices_548), (true, vertices_644), (true, vertices_296), (true, vertices_368), (true, vertices_560), (true, vertices_592), (true, vertices_800), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_899) then 13 else
  if p.val = (false, vertices_93) then 16 else
  if p.val = (false, vertices_457) then 18 else
  if p.val = (true, vertices_546) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_368) then 20 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
cert_nodeAtPriority_18 267 546 532 548 644 296 560 592 800 704 832 199 899 93 457 368
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 7 8 810 42 3
cert_row_2 1 3 4 5 7 368
cert_row_4 2 0 1 4 6 8 678 38 3
cert_row_4 3 1 3 5 6 8 724 84 3
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 2 0 1 4 6 38 678 3
cert_coverFacet 1 810
cert_cover_5 1 0 0 2 4 7 42 810 3
cert_coverFacet 2 564
cert_cover_2 2 3 1 4 8 52 564 3
cert_coverFacet 3 724
cert_cover_5 3 3 1 3 5 6 84 724 3
cert_coverFacet 4 376
cert_cover_5 4 1 2 3 4 5 56 376 3
cert_coverFacet 5 880
cert_cover_5 5 1 3 4 5 8 368 880 3
cert_coverFacet 6 960
cert_cover_2 6 6 5 7 8 448 960 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1659

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_one_six_1660.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1660

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 267, 899, 93, 457, 678, 810, 564, 468, 916, 568, 856, 7, 11, 131, 259, 29, 69, 73, 265, 193, 385, 38, 134, 42, 266, 546, 642, 770, 52, 84, 404, 532, 548, 196, 644, 56, 88, 536, 552, 328, 776, 560, 336, 784, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_267, vertices_899, vertices_93, vertices_457, vertices_678, vertices_810, vertices_564, vertices_468, vertices_916, vertices_568, vertices_856] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_29, vertices_69, vertices_73, vertices_265, vertices_193, vertices_385, vertices_38, vertices_134, vertices_42, vertices_266, vertices_546, vertices_642, vertices_770, vertices_52, vertices_84, vertices_404, vertices_532, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_536, vertices_552, vertices_328, vertices_776, vertices_560, vertices_336, vertices_784, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_267), (false, vertices_899), (false, vertices_93), (false, vertices_457), (true, vertices_546), (true, vertices_404), (true, vertices_532), (true, vertices_548), (true, vertices_644), (true, vertices_536), (true, vertices_552), (true, vertices_776), (true, vertices_560), (true, vertices_336), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 18 14 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_899) then 13 else
  if p.val = (false, vertices_93) then 16 else
  if p.val = (false, vertices_457) then 17 else
  if p.val = (true, vertices_546) then 1 else
  if p.val = (true, vertices_404) then 19 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_784) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(true, vertices_404), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 5 7 8 856 88 3
cert_row_2 1 1 3 6 7 404
cert_row_4 2 0 1 4 6 8 678 38 3
cert_row_4 3 0 2 4 7 8 810 42 3
cert_rows
cert_pivot_2 5 3 1 0
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 2 0 1 4 6 38 678 3
cert_coverFacet 1 810
cert_cover_5 1 3 0 2 4 7 42 810 3
cert_coverFacet 2 564
cert_cover_2 2 3 1 4 8 52 564 3
cert_coverFacet 3 468
cert_cover_5 3 1 1 3 5 6 84 468 3
cert_coverFacet 4 916
cert_cover_5 4 1 1 3 6 8 404 916 3
cert_coverFacet 5 568
cert_cover_2 5 3 2 4 8 56 568 3
cert_coverFacet 6 856
cert_cover_5 6 0 2 3 5 7 88 856 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1660

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_one_six_1661.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1661

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 267, 899, 93, 457, 678, 810, 692, 468, 568, 856, 912, 7, 11, 131, 259, 29, 69, 73, 265, 193, 385, 38, 134, 42, 266, 546, 642, 770, 52, 84, 148, 676, 196, 56, 88, 536, 552, 328, 776, 560, 336, 400, 656, 784, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_267, vertices_899, vertices_93, vertices_457, vertices_678, vertices_810, vertices_692, vertices_468, vertices_568, vertices_856, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_29, vertices_69, vertices_73, vertices_265, vertices_193, vertices_385, vertices_38, vertices_134, vertices_42, vertices_266, vertices_546, vertices_642, vertices_770, vertices_52, vertices_84, vertices_148, vertices_676, vertices_196, vertices_56, vertices_88, vertices_536, vertices_552, vertices_328, vertices_776, vertices_560, vertices_336, vertices_400, vertices_656, vertices_784, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_267), (false, vertices_899), (false, vertices_93), (false, vertices_457), (true, vertices_546), (true, vertices_148), (true, vertices_676), (true, vertices_536), (true, vertices_552), (true, vertices_776), (true, vertices_560), (true, vertices_336), (true, vertices_400), (true, vertices_656), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 18 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_899) then 13 else
  if p.val = (false, vertices_93) then 16 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (true, vertices_546) then 1 else
  if p.val = (true, vertices_148) then 2 else
  if p.val = (true, vertices_676) then 17 else
  if p.val = (true, vertices_536) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_784) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_676), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 7 8 810 42 3
cert_row_2 1 1 4 6 8 676
cert_row_4 2 1 3 5 6 7 468 84 3
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 0 4 1 2
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 1 0 1 4 6 38 678 3
cert_coverFacet 1 810
cert_cover_5 1 0 0 2 4 7 42 810 3
cert_coverFacet 2 692
cert_cover_5 2 1 1 3 4 6 52 692 3
cert_coverFacet 3 468
cert_cover_5 3 2 1 3 5 6 84 468 3
cert_coverFacet 4 568
cert_cover_2 4 3 2 4 8 56 568 3
cert_coverFacet 5 856
cert_cover_5 5 3 2 3 5 7 88 856 3
cert_coverFacet 6 912
cert_cover_2 6 6 3 7 8 400 912 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1661

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_one_six_1662.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1662

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 899, 93, 457, 678, 554, 180, 468, 568, 856, 944, 7, 11, 131, 771, 29, 69, 73, 265, 193, 385, 38, 134, 42, 522, 546, 642, 52, 84, 148, 164, 196, 56, 88, 536, 552, 328, 776, 176, 560, 336, 400, 784, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_899, vertices_93, vertices_457, vertices_678, vertices_554, vertices_180, vertices_468, vertices_568, vertices_856, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_771, vertices_29, vertices_69, vertices_73, vertices_265, vertices_193, vertices_385, vertices_38, vertices_134, vertices_42, vertices_522, vertices_546, vertices_642, vertices_52, vertices_84, vertices_148, vertices_164, vertices_196, vertices_56, vertices_88, vertices_536, vertices_552, vertices_328, vertices_776, vertices_176, vertices_560, vertices_336, vertices_400, vertices_784, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_899), (false, vertices_93), (false, vertices_457), (true, vertices_546), (true, vertices_148), (true, vertices_164), (true, vertices_536), (true, vertices_552), (true, vertices_176), (true, vertices_560), (true, vertices_336), (true, vertices_400), (true, vertices_784), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 11 18 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_899) then 17 else
  if p.val = (false, vertices_93) then 13 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (true, vertices_546) then 0 else
  if p.val = (true, vertices_148) then 1 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_536) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_176) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_672) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 38 3
cert_row_4 1 1 3 5 6 7 468 84 3
cert_row_4 2 2 3 5 7 8 856 88 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 38 678 3
cert_coverFacet 1 554
cert_cover_2 1 2 0 4 8 42 554 3
cert_coverFacet 2 180
cert_cover_2 2 3 1 4 6 52 180 3
cert_coverFacet 3 468
cert_cover_5 3 1 1 3 5 6 84 468 3
cert_coverFacet 4 568
cert_cover_2 4 3 2 4 8 56 568 3
cert_coverFacet 5 856
cert_cover_5 5 2 2 3 5 7 88 856 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 176 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1662

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_one_six_1663.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1663

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 899, 93, 457, 678, 554, 820, 468, 900, 568, 856, 7, 11, 131, 771, 29, 69, 73, 265, 193, 385, 38, 134, 42, 522, 546, 642, 52, 84, 276, 548, 196, 388, 644, 772, 56, 88, 536, 552, 328, 776, 560, 336, 784, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_899, vertices_93, vertices_457, vertices_678, vertices_554, vertices_820, vertices_468, vertices_900, vertices_568, vertices_856] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_771, vertices_29, vertices_69, vertices_73, vertices_265, vertices_193, vertices_385, vertices_38, vertices_134, vertices_42, vertices_522, vertices_546, vertices_642, vertices_52, vertices_84, vertices_276, vertices_548, vertices_196, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_536, vertices_552, vertices_328, vertices_776, vertices_560, vertices_336, vertices_784, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_899), (false, vertices_93), (false, vertices_457), (true, vertices_546), (true, vertices_276), (true, vertices_548), (true, vertices_388), (true, vertices_644), (true, vertices_772), (true, vertices_536), (true, vertices_552), (true, vertices_560), (true, vertices_336), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 11 18 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_899) then 17 else
  if p.val = (false, vertices_93) then 13 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (true, vertices_546) then 0 else
  if p.val = (true, vertices_276) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_388) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_784) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 38 3
cert_row_4 1 1 3 4 7 8 820 52 3
cert_row_4 2 1 3 5 6 7 468 84 3
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 0 4 1 2
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 38 678 3
cert_coverFacet 1 554
cert_cover_2 1 2 0 4 8 42 554 3
cert_coverFacet 2 820
cert_cover_5 2 1 1 3 4 7 52 820 3
cert_coverFacet 3 468
cert_cover_5 3 2 1 3 5 6 84 468 3
cert_coverFacet 4 900
cert_cover_2 4 6 1 7 8 388 900 3
cert_coverFacet 5 568
cert_cover_2 5 3 2 4 8 56 568 3
cert_coverFacet 6 856
cert_cover_5 6 3 2 3 5 7 88 856 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1663

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_one_six_1664.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1664

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 267, 899, 677, 809, 94, 458, 820, 724, 312, 472, 912, 7, 11, 131, 259, 37, 133, 41, 265, 545, 641, 769, 30, 70, 74, 266, 194, 386, 52, 84, 532, 548, 196, 644, 56, 88, 280, 296, 456, 304, 208, 400, 656, 784, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_267, vertices_899, vertices_677, vertices_809, vertices_94, vertices_458, vertices_820, vertices_724, vertices_312, vertices_472, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_37, vertices_133, vertices_41, vertices_265, vertices_545, vertices_641, vertices_769, vertices_30, vertices_70, vertices_74, vertices_266, vertices_194, vertices_386, vertices_52, vertices_84, vertices_532, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_280, vertices_296, vertices_456, vertices_304, vertices_208, vertices_400, vertices_656, vertices_784, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_267), (false, vertices_899), (false, vertices_677), (false, vertices_809), (true, vertices_74), (true, vertices_84), (true, vertices_532), (true, vertices_88), (true, vertices_280), (true, vertices_456), (true, vertices_304), (true, vertices_208), (true, vertices_400), (true, vertices_656), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_899) then 13 else
  if p.val = (false, vertices_677) then 16 else
  if p.val = (false, vertices_809) then 18 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_88) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_456) then 19 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_784) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_456), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 3 30
cert_row_2 1 2 5 6 7 456
cert_row_4 2 1 3 4 7 8 820 52 3
cert_row_4 3 1 3 5 6 8 724 84 3
cert_rows
cert_pivot_2 0 2 4 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 5 30 94 3
cert_coverFacet 1 458
cert_cover_5 1 1 0 2 5 6 74 458 3
cert_coverFacet 2 820
cert_cover_5 2 2 1 3 4 7 52 820 3
cert_coverFacet 3 724
cert_cover_5 3 3 1 3 5 6 84 724 3
cert_coverFacet 4 312
cert_cover_2 4 3 2 4 7 56 312 3
cert_coverFacet 5 472
cert_cover_5 5 1 2 3 5 6 88 472 3
cert_coverFacet 6 912
cert_cover_2 6 6 3 7 8 400 912 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1664

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_one_six_1665.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1665

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 677, 817, 721, 398, 458, 300, 420, 312, 856, 992, 7, 27, 67, 37, 133, 49, 81, 529, 545, 193, 641, 14, 134, 74, 394, 194, 44, 268, 164, 292, 388, 56, 88, 280, 296, 328, 304, 592, 784, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_677, vertices_817, vertices_721, vertices_398, vertices_458, vertices_300, vertices_420, vertices_312, vertices_856, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_529, vertices_545, vertices_193, vertices_641, vertices_14, vertices_134, vertices_74, vertices_394, vertices_194, vertices_44, vertices_268, vertices_164, vertices_292, vertices_388, vertices_56, vertices_88, vertices_280, vertices_296, vertices_328, vertices_304, vertices_592, vertices_784, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_677), (false, vertices_817), (false, vertices_721), (true, vertices_394), (true, vertices_268), (true, vertices_292), (true, vertices_388), (true, vertices_280), (true, vertices_296), (true, vertices_328), (true, vertices_416), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 9 20 14 12 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 10 else
  if p.val = (false, vertices_91) then 16 else
  if p.val = (false, vertices_677) then 11 else
  if p.val = (false, vertices_817) then 13 else
  if p.val = (false, vertices_721) then 17 else
  if p.val = (true, vertices_394) then 19 else
  if p.val = (true, vertices_268) then 0 else
  if p.val = (true, vertices_292) then 1 else
  if p.val = (true, vertices_388) then 2 else
  if p.val = (true, vertices_280) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_416) then 6 else
  if p.val = (true, vertices_448) then 7 else
  if p.val = (true, vertices_832) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 12 => Sum.inl 4
  | 13 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(true, vertices_394), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 6 7 394
cert_row_4 1 2 3 5 7 8 856 88 3
cert_row_4 2 4 5 6 7 8 992 416 1
cert_rows_3
cert_pivot_3 2 0 4
cert_heightProof 3
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 6 74 458 3
cert_coverFacet 2 300
cert_cover_2 2 2 1 4 7 44 300 3
cert_coverFacet 3 420
cert_cover_2 3 4 1 6 7 164 420 3
cert_coverFacet 4 312
cert_cover_2 4 3 2 4 7 56 312 3
cert_coverFacet 5 856
cert_cover_5 5 1 2 3 5 7 88 856 3
cert_coverFacet 6 992
cert_cover_5 6 2 4 5 6 7 416 992 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1665

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_one_six_1666.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1666

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 293, 901, 817, 721, 398, 458, 300, 632, 360, 992, 7, 27, 67, 37, 133, 261, 49, 81, 529, 289, 193, 641, 769, 14, 134, 74, 394, 194, 44, 268, 292, 388, 56, 88, 104, 296, 328, 560, 592, 352, 608, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_293, vertices_901, vertices_817, vertices_721, vertices_398, vertices_458, vertices_300, vertices_632, vertices_360, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_261, vertices_49, vertices_81, vertices_529, vertices_289, vertices_193, vertices_641, vertices_769, vertices_14, vertices_134, vertices_74, vertices_394, vertices_194, vertices_44, vertices_268, vertices_292, vertices_388, vertices_56, vertices_88, vertices_104, vertices_296, vertices_328, vertices_560, vertices_592, vertices_352, vertices_608, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_293), (false, vertices_901), (false, vertices_817), (false, vertices_721), (true, vertices_394), (true, vertices_268), (true, vertices_104), (true, vertices_296), (true, vertices_328), (true, vertices_352), (true, vertices_608), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 8 19 13 11 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 9 else
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_293) then 0 else
  if p.val = (false, vertices_901) then 10 else
  if p.val = (false, vertices_817) then 12 else
  if p.val = (false, vertices_721) then 16 else
  if p.val = (true, vertices_394) then 18 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_104) then 2 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_352) then 5 else
  if p.val = (true, vertices_608) then 6 else
  if p.val = (true, vertices_448) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 8 => Sum.inl 1
  | 9 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 11 => Sum.inl 4
  | 12 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 13 => Sum.inl 3
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(true, vertices_394), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 6 7 394
cert_row_4 1 2 3 4 5 8 632 56 3
cert_row_4 2 4 5 6 7 8 992 352 2
cert_rows_3
cert_pivot_3 2 0 4
cert_heightProof 3
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 6 74 458 3
cert_coverFacet 2 300
cert_cover_2 2 2 1 4 7 44 300 3
cert_coverFacet 3 632
cert_cover_5 3 1 2 3 4 5 56 632 3
cert_coverFacet 4 360
cert_cover_2 4 4 2 5 7 104 360 3
cert_coverFacet 5 992
cert_cover_5 5 2 4 5 6 7 352 992 2
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1666

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_one_six_1667.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1667

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 421, 177, 721, 398, 458, 812, 568, 856, 688, 992, 7, 27, 67, 37, 133, 49, 81, 145, 161, 193, 14, 134, 74, 394, 194, 44, 268, 292, 388, 56, 88, 536, 552, 328, 776, 176, 560, 592, 656, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_421, vertices_177, vertices_721, vertices_398, vertices_458, vertices_812, vertices_568, vertices_856, vertices_688, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_145, vertices_161, vertices_193, vertices_14, vertices_134, vertices_74, vertices_394, vertices_194, vertices_44, vertices_268, vertices_292, vertices_388, vertices_56, vertices_88, vertices_536, vertices_552, vertices_328, vertices_776, vertices_176, vertices_560, vertices_592, vertices_656, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_421), (false, vertices_177), (false, vertices_721), (true, vertices_394), (true, vertices_268), (true, vertices_536), (true, vertices_552), (true, vertices_328), (true, vertices_776), (true, vertices_560), (true, vertices_672), (true, vertices_800), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 11 20 14 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_91) then 16 else
  if p.val = (false, vertices_421) then 13 else
  if p.val = (false, vertices_177) then 0 else
  if p.val = (false, vertices_721) then 17 else
  if p.val = (true, vertices_394) then 19 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_536) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_177), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(true, vertices_394), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 6 7 394
cert_row_4 1 1 2 4 7 8 812 44 3
cert_row_4 2 2 3 5 7 8 856 88 3
cert_row_4 3 4 5 6 7 8 992 416 1
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 6 74 458 3
cert_coverFacet 2 812
cert_cover_5 2 1 1 2 4 7 44 812 3
cert_coverFacet 3 568
cert_cover_2 3 3 2 4 8 56 568 3
cert_coverFacet 4 856
cert_cover_5 4 2 2 3 5 7 88 856 3
cert_coverFacet 5 688
cert_cover_2 5 4 3 6 8 176 688 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 416 992 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1667

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_one_six_1668.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1668

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 421, 561, 721, 673, 398, 458, 812, 568, 856, 992, 7, 27, 67, 37, 133, 49, 81, 529, 161, 545, 193, 641, 14, 134, 74, 394, 194, 44, 268, 292, 388, 56, 88, 536, 552, 328, 776, 560, 592, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_421, vertices_561, vertices_721, vertices_673, vertices_398, vertices_458, vertices_812, vertices_568, vertices_856, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_529, vertices_161, vertices_545, vertices_193, vertices_641, vertices_14, vertices_134, vertices_74, vertices_394, vertices_194, vertices_44, vertices_268, vertices_292, vertices_388, vertices_56, vertices_88, vertices_536, vertices_552, vertices_328, vertices_776, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_421), (false, vertices_561), (false, vertices_721), (false, vertices_673), (true, vertices_394), (true, vertices_268), (true, vertices_536), (true, vertices_552), (true, vertices_328), (true, vertices_776), (true, vertices_800), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 10 19 13 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 11 else
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_421) then 12 else
  if p.val = (false, vertices_561) then 0 else
  if p.val = (false, vertices_721) then 16 else
  if p.val = (false, vertices_673) then 1 else
  if p.val = (true, vertices_394) then 18 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_536) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_800) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_561), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_673), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 13 => Sum.inl 3
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(true, vertices_394), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 6 7 394
cert_row_4 1 1 2 4 7 8 812 44 3
cert_row_4 2 2 3 5 7 8 856 88 3
cert_row_4 3 4 5 6 7 8 992 416 1
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 6 74 458 3
cert_coverFacet 2 812
cert_cover_5 2 1 1 2 4 7 44 812 3
cert_coverFacet 3 568
cert_cover_2 3 3 2 4 8 56 568 3
cert_coverFacet 4 856
cert_cover_5 4 2 2 3 5 7 88 856 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 416 992 1
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1668

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_one_six_1669.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1669

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 91, 195, 899, 421, 241, 590, 706, 812, 440, 856, 976, 7, 27, 67, 131, 771, 37, 261, 49, 81, 161, 193, 385, 14, 518, 74, 194, 578, 642, 44, 524, 292, 772, 56, 88, 280, 296, 584, 776, 176, 208, 848, 400, 416, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_91, vertices_195, vertices_899, vertices_421, vertices_241, vertices_590, vertices_706, vertices_812, vertices_440, vertices_856, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_771, vertices_37, vertices_261, vertices_49, vertices_81, vertices_161, vertices_193, vertices_385, vertices_14, vertices_518, vertices_74, vertices_194, vertices_578, vertices_642, vertices_44, vertices_524, vertices_292, vertices_772, vertices_56, vertices_88, vertices_280, vertices_296, vertices_584, vertices_776, vertices_176, vertices_208, vertices_848, vertices_400, vertices_416, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_91), (false, vertices_195), (false, vertices_899), (false, vertices_421), (false, vertices_241), (true, vertices_578), (true, vertices_524), (true, vertices_280), (true, vertices_296), (true, vertices_584), (true, vertices_776), (true, vertices_848), (true, vertices_400), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 9 11 17 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_775) then 15 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_899) then 16 else
  if p.val = (false, vertices_421) then 10 else
  if p.val = (false, vertices_241) then 18 else
  if p.val = (true, vertices_578) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_280) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_848) then 19 else
  if p.val = (true, vertices_400) then 7 else
  if p.val = (true, vertices_704) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 9 => Sum.inl 1
  | 10 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 11 => Sum.inl 2
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_848), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_2 1 3 5 7 8 848
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 2 3 4 6 7 440 56 3
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 706
cert_cover_2 1 5 0 6 8 194 706 3
cert_coverFacet 2 812
cert_cover_5 2 2 1 2 4 7 44 812 3
cert_coverFacet 3 440
cert_cover_5 3 3 2 3 4 6 56 440 3
cert_coverFacet 4 856
cert_cover_5 4 1 2 3 5 7 88 856 3
cert_coverFacet 5 976
cert_cover_5 5 1 3 5 6 7 208 976 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1669

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_one_six_1670.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1670

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 677, 817, 721, 782, 646, 458, 898, 812, 376, 976, 7, 27, 67, 37, 133, 49, 81, 529, 545, 193, 641, 14, 134, 518, 74, 266, 194, 386, 642, 770, 44, 780, 548, 644, 56, 88, 296, 328, 304, 720, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_677, vertices_817, vertices_721, vertices_782, vertices_646, vertices_458, vertices_898, vertices_812, vertices_376, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_529, vertices_545, vertices_193, vertices_641, vertices_14, vertices_134, vertices_518, vertices_74, vertices_266, vertices_194, vertices_386, vertices_642, vertices_770, vertices_44, vertices_780, vertices_548, vertices_644, vertices_56, vertices_88, vertices_296, vertices_328, vertices_304, vertices_720, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_677), (false, vertices_817), (false, vertices_721), (true, vertices_518), (true, vertices_266), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_780), (true, vertices_296), (true, vertices_328), (true, vertices_336), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 17 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 11 else
  if p.val = (false, vertices_91) then 12 else
  if p.val = (false, vertices_677) then 15 else
  if p.val = (false, vertices_817) then 19 else
  if p.val = (false, vertices_721) then 20 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_780) then 16 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_780), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 7 8 780
cert_row_2 1 3 5 6 8 720
cert_row_4 2 0 2 5 6 7 458 74 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 458
cert_cover_5 2 2 0 2 5 6 74 458 3
cert_coverFacet 3 898
cert_cover_2 3 6 0 7 8 386 898 3
cert_coverFacet 4 812
cert_cover_5 4 0 1 2 4 7 44 812 3
cert_coverFacet 5 376
cert_cover_5 5 3 2 3 4 5 56 376 3
cert_coverFacet 6 976
cert_cover_5 6 1 3 5 6 7 720 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1670

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_one_six_1671.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1671

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 899, 93, 457, 678, 554, 372, 484, 568, 856, 944, 7, 11, 131, 771, 29, 69, 73, 265, 193, 385, 38, 134, 42, 522, 546, 642, 52, 84, 356, 164, 196, 56, 88, 536, 552, 328, 776, 304, 560, 336, 784, 416, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_899, vertices_93, vertices_457, vertices_678, vertices_554, vertices_372, vertices_484, vertices_568, vertices_856, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_771, vertices_29, vertices_69, vertices_73, vertices_265, vertices_193, vertices_385, vertices_38, vertices_134, vertices_42, vertices_522, vertices_546, vertices_642, vertices_52, vertices_84, vertices_356, vertices_164, vertices_196, vertices_56, vertices_88, vertices_536, vertices_552, vertices_328, vertices_776, vertices_304, vertices_560, vertices_336, vertices_784, vertices_416, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_899), (false, vertices_93), (false, vertices_457), (true, vertices_546), (true, vertices_356), (true, vertices_164), (true, vertices_536), (true, vertices_552), (true, vertices_304), (true, vertices_560), (true, vertices_336), (true, vertices_784), (true, vertices_416), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 12 19 10 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_899) then 18 else
  if p.val = (false, vertices_93) then 11 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (true, vertices_546) then 0 else
  if p.val = (true, vertices_356) then 15 else
  if p.val = (true, vertices_164) then 1 else
  if p.val = (true, vertices_536) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_304) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_336) then 6 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_672) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inl 3
  | 11 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_356), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 38 3
cert_row_2 1 1 4 5 7 356
cert_row_4 2 2 3 5 7 8 856 88 3
cert_row_4 3 3 4 6 7 8 944 304 2
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 38 678 3
cert_coverFacet 1 554
cert_cover_2 1 2 0 4 8 42 554 3
cert_coverFacet 2 372
cert_cover_5 2 1 1 3 4 5 52 372 3
cert_coverFacet 3 484
cert_cover_5 3 1 1 4 5 6 356 484 3
cert_coverFacet 4 568
cert_cover_2 4 3 2 4 8 56 568 3
cert_coverFacet 5 856
cert_cover_5 5 2 2 3 5 7 88 856 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 304 944 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1671

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_one_six_1672.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1672

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 899, 93, 457, 678, 554, 820, 724, 376, 808, 976, 7, 11, 131, 771, 29, 69, 73, 265, 193, 385, 38, 134, 42, 522, 546, 642, 52, 84, 532, 548, 196, 644, 56, 88, 296, 552, 328, 776, 304, 720, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_899, vertices_93, vertices_457, vertices_678, vertices_554, vertices_820, vertices_724, vertices_376, vertices_808, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_771, vertices_29, vertices_69, vertices_73, vertices_265, vertices_193, vertices_385, vertices_38, vertices_134, vertices_42, vertices_522, vertices_546, vertices_642, vertices_52, vertices_84, vertices_532, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_296, vertices_552, vertices_328, vertices_776, vertices_304, vertices_720, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_899), (false, vertices_93), (false, vertices_457), (true, vertices_546), (true, vertices_532), (true, vertices_548), (true, vertices_644), (true, vertices_296), (true, vertices_552), (true, vertices_304), (true, vertices_720), (true, vertices_336), (true, vertices_784), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 10 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 11 else
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_899) then 16 else
  if p.val = (false, vertices_93) then 12 else
  if p.val = (false, vertices_457) then 18 else
  if p.val = (true, vertices_546) then 0 else
  if p.val = (true, vertices_532) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_644) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_720) then 20 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_800) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(true, vertices_720), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 38 3
cert_row_2 1 3 5 6 8 720
cert_row_4 2 1 3 4 7 8 820 52 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 38 678 3
cert_coverFacet 1 554
cert_cover_2 1 2 0 4 8 42 554 3
cert_coverFacet 2 820
cert_cover_5 2 2 1 3 4 7 52 820 3
cert_coverFacet 3 724
cert_cover_5 3 1 1 3 5 6 84 724 3
cert_coverFacet 4 376
cert_cover_5 4 3 2 3 4 5 56 376 3
cert_coverFacet 5 808
cert_cover_2 5 4 2 7 8 296 808 3
cert_coverFacet 6 976
cert_cover_5 6 1 3 5 6 7 720 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1672

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_one_six_1673.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1673

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 91, 677, 817, 721, 526, 646, 458, 906, 812, 376, 976, 7, 27, 67, 37, 133, 49, 81, 529, 545, 193, 641, 14, 134, 518, 74, 394, 522, 194, 642, 44, 524, 548, 644, 56, 88, 296, 328, 776, 304, 720, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_91, vertices_677, vertices_817, vertices_721, vertices_526, vertices_646, vertices_458, vertices_906, vertices_812, vertices_376, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_133, vertices_49, vertices_81, vertices_529, vertices_545, vertices_193, vertices_641, vertices_14, vertices_134, vertices_518, vertices_74, vertices_394, vertices_522, vertices_194, vertices_642, vertices_44, vertices_524, vertices_548, vertices_644, vertices_56, vertices_88, vertices_296, vertices_328, vertices_776, vertices_304, vertices_720, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_91), (false, vertices_677), (false, vertices_817), (false, vertices_721), (true, vertices_518), (true, vertices_394), (true, vertices_522), (true, vertices_642), (true, vertices_524), (true, vertices_296), (true, vertices_328), (true, vertices_776), (true, vertices_336), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 10 21 15 13 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 11 else
  if p.val = (false, vertices_91) then 17 else
  if p.val = (false, vertices_677) then 12 else
  if p.val = (false, vertices_817) then 14 else
  if p.val = (false, vertices_721) then 18 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_394) then 20 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 13 => Sum.inl 4
  | 14 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(true, vertices_394), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 6 7 394
cert_row_2 1 3 5 6 8 720
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 458
cert_cover_5 2 0 0 2 5 6 74 458 3
cert_coverFacet 3 906
cert_cover_5 3 0 0 2 6 8 394 906 3
cert_coverFacet 4 812
cert_cover_5 4 2 1 2 4 7 44 812 3
cert_coverFacet 5 376
cert_cover_5 5 3 2 3 4 5 56 376 3
cert_coverFacet 6 976
cert_cover_5 6 1 3 5 6 7 720 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1673

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_one_six_1674.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1674

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 451, 805, 369, 897, 78, 198, 684, 204, 824, 728, 976, 7, 27, 67, 131, 37, 517, 49, 81, 289, 321, 385, 641, 769, 14, 70, 134, 74, 194, 44, 76, 140, 548, 196, 644, 56, 88, 536, 552, 200, 648, 304, 720, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_451, vertices_805, vertices_369, vertices_897, vertices_78, vertices_198, vertices_684, vertices_204, vertices_824, vertices_728, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_517, vertices_49, vertices_81, vertices_289, vertices_321, vertices_385, vertices_641, vertices_769, vertices_14, vertices_70, vertices_134, vertices_74, vertices_194, vertices_44, vertices_76, vertices_140, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_536, vertices_552, vertices_200, vertices_648, vertices_304, vertices_720, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_451), (false, vertices_805), (false, vertices_369), (false, vertices_897), (true, vertices_70), (true, vertices_76), (true, vertices_140), (true, vertices_196), (true, vertices_536), (true, vertices_552), (true, vertices_200), (true, vertices_648), (true, vertices_720), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 10 17 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_647) then 11 else
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_451) then 16 else
  if p.val = (false, vertices_805) then 12 else
  if p.val = (false, vertices_369) then 19 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_648) then 8 else
  if p.val = (true, vertices_720) then 20 else
  if p.val = (true, vertices_784) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_720), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 5 6 8 720
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_4 2 2 3 4 7 8 824 56 3
cert_rows_3
cert_pivot_3 1 5 2
cert_heightProof 3
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 684
cert_cover_5 2 1 1 2 4 6 44 684 3
cert_coverFacet 3 204
cert_cover_2 3 2 1 5 6 76 204 3
cert_coverFacet 4 824
cert_cover_5 4 2 2 3 4 7 56 824 3
cert_coverFacet 5 728
cert_cover_5 5 0 2 3 5 6 88 728 3
cert_coverFacet 6 976
cert_cover_5 6 0 3 5 6 7 720 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1674

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_one_six_1675.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1675

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 451, 805, 369, 897, 78, 198, 556, 716, 696, 472, 944, 7, 27, 67, 131, 37, 517, 49, 81, 289, 321, 385, 641, 769, 14, 70, 134, 74, 194, 44, 76, 524, 548, 196, 644, 56, 88, 152, 552, 200, 648, 688, 304, 336, 400, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_451, vertices_805, vertices_369, vertices_897, vertices_78, vertices_198, vertices_556, vertices_716, vertices_696, vertices_472, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_131, vertices_37, vertices_517, vertices_49, vertices_81, vertices_289, vertices_321, vertices_385, vertices_641, vertices_769, vertices_14, vertices_70, vertices_134, vertices_74, vertices_194, vertices_44, vertices_76, vertices_524, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_152, vertices_552, vertices_200, vertices_648, vertices_688, vertices_304, vertices_336, vertices_400, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_451), (false, vertices_805), (false, vertices_369), (false, vertices_897), (true, vertices_70), (true, vertices_76), (true, vertices_524), (true, vertices_196), (true, vertices_152), (true, vertices_552), (true, vertices_200), (true, vertices_648), (true, vertices_688), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 10 17 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_647) then 11 else
  if p.val = (false, vertices_91) then 15 else
  if p.val = (false, vertices_451) then 16 else
  if p.val = (false, vertices_805) then 12 else
  if p.val = (false, vertices_369) then 19 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_648) then 8 else
  if p.val = (true, vertices_688) then 20 else
  if p.val = (true, vertices_400) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_688), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 6 8 688
cert_row_4 1 1 2 5 6 8 716 76 3
cert_row_4 2 2 3 5 6 7 472 88 3
cert_rows_3
cert_pivot_3 1 4 2
cert_heightProof 3
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 716
cert_cover_5 3 1 1 2 5 6 76 716 3
cert_coverFacet 4 696
cert_cover_5 4 0 2 3 4 6 56 696 3
cert_coverFacet 5 472
cert_cover_5 5 2 2 3 5 6 88 472 3
cert_coverFacet 6 944
cert_cover_5 6 0 3 4 6 7 688 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1675

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_one_six_1676.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1676

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 263, 91, 451, 805, 369, 78, 198, 902, 684, 204, 824, 728, 976, 7, 27, 67, 259, 37, 261, 49, 81, 289, 321, 14, 70, 134, 262, 74, 194, 386, 44, 76, 140, 548, 196, 644, 772, 56, 88, 536, 552, 200, 648, 304, 720, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_263, vertices_91, vertices_451, vertices_805, vertices_369, vertices_78, vertices_198, vertices_902, vertices_684, vertices_204, vertices_824, vertices_728, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_259, vertices_37, vertices_261, vertices_49, vertices_81, vertices_289, vertices_321, vertices_14, vertices_70, vertices_134, vertices_262, vertices_74, vertices_194, vertices_386, vertices_44, vertices_76, vertices_140, vertices_548, vertices_196, vertices_644, vertices_772, vertices_56, vertices_88, vertices_536, vertices_552, vertices_200, vertices_648, vertices_304, vertices_720, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_263), (false, vertices_91), (false, vertices_451), (false, vertices_805), (false, vertices_369), (true, vertices_70), (true, vertices_134), (true, vertices_76), (true, vertices_140), (true, vertices_196), (true, vertices_644), (true, vertices_536), (true, vertices_552), (true, vertices_200), (true, vertices_648), (true, vertices_720), (true, vertices_784), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_263) then 0 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_451) then 15 else
  if p.val = (false, vertices_805) then 18 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_720) then 22 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_263), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_720), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 5 6 8 720
cert_row_4 1 0 1 6 7 8 902 134 3
cert_row_4 2 1 2 4 6 8 684 44 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 5 0 1 2
cert_heightProof 4
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 902
cert_cover_5 2 1 0 1 6 7 134 902 3
cert_coverFacet 3 684
cert_cover_5 3 2 1 2 4 6 44 684 3
cert_coverFacet 4 204
cert_cover_2 4 2 1 5 6 76 204 3
cert_coverFacet 5 824
cert_cover_5 5 3 2 3 4 7 56 824 3
cert_coverFacet 6 728
cert_cover_5 6 0 2 3 5 6 88 728 3
cert_coverFacet 7 976
cert_cover_5 7 0 3 5 6 7 720 976 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1676

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_one_six_1677.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1677

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 263, 91, 451, 805, 369, 78, 198, 902, 556, 716, 696, 472, 944, 7, 27, 67, 259, 37, 261, 49, 81, 289, 321, 14, 70, 134, 262, 74, 194, 386, 44, 76, 524, 548, 196, 644, 772, 56, 88, 152, 552, 200, 648, 688, 304, 336, 400, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_263, vertices_91, vertices_451, vertices_805, vertices_369, vertices_78, vertices_198, vertices_902, vertices_556, vertices_716, vertices_696, vertices_472, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_259, vertices_37, vertices_261, vertices_49, vertices_81, vertices_289, vertices_321, vertices_14, vertices_70, vertices_134, vertices_262, vertices_74, vertices_194, vertices_386, vertices_44, vertices_76, vertices_524, vertices_548, vertices_196, vertices_644, vertices_772, vertices_56, vertices_88, vertices_152, vertices_552, vertices_200, vertices_648, vertices_688, vertices_304, vertices_336, vertices_400, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_263), (false, vertices_91), (false, vertices_451), (false, vertices_805), (false, vertices_369), (true, vertices_70), (true, vertices_134), (true, vertices_76), (true, vertices_524), (true, vertices_196), (true, vertices_644), (true, vertices_152), (true, vertices_552), (true, vertices_200), (true, vertices_648), (true, vertices_688), (true, vertices_400), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_263) then 0 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_451) then 15 else
  if p.val = (false, vertices_805) then 18 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_688) then 22 else
  if p.val = (true, vertices_400) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_263), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_688), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 6 8 688
cert_row_4 1 0 1 6 7 8 902 134 3
cert_row_4 2 1 2 5 6 8 716 76 3
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 4 0 1 2
cert_heightProof 4
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 902
cert_cover_5 2 1 0 1 6 7 134 902 3
cert_coverFacet 3 556
cert_cover_2 3 2 1 4 8 44 556 3
cert_coverFacet 4 716
cert_cover_5 4 2 1 2 5 6 76 716 3
cert_coverFacet 5 696
cert_cover_5 5 0 2 3 4 6 56 696 3
cert_coverFacet 6 472
cert_cover_5 6 3 2 3 5 6 88 472 3
cert_coverFacet 7 944
cert_cover_5 7 0 3 4 6 7 688 944 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1677

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_one_six_1678.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1678

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 91, 805, 709, 625, 270, 198, 902, 458, 300, 440, 728, 944, 7, 27, 67, 37, 69, 517, 49, 81, 545, 577, 14, 70, 134, 262, 74, 266, 194, 386, 44, 268, 292, 196, 644, 772, 56, 88, 152, 296, 200, 392, 432, 560, 592, 656, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_91, vertices_805, vertices_709, vertices_625, vertices_270, vertices_198, vertices_902, vertices_458, vertices_300, vertices_440, vertices_728, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_69, vertices_517, vertices_49, vertices_81, vertices_545, vertices_577, vertices_14, vertices_70, vertices_134, vertices_262, vertices_74, vertices_266, vertices_194, vertices_386, vertices_44, vertices_268, vertices_292, vertices_196, vertices_644, vertices_772, vertices_56, vertices_88, vertices_152, vertices_296, vertices_200, vertices_392, vertices_432, vertices_560, vertices_592, vertices_656, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_91), (false, vertices_805), (false, vertices_709), (false, vertices_625), (true, vertices_134), (true, vertices_262), (true, vertices_266), (true, vertices_194), (true, vertices_386), (true, vertices_268), (true, vertices_152), (true, vertices_296), (true, vertices_200), (true, vertices_392), (true, vertices_432), (true, vertices_656), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_805) then 17 else
  if p.val = (false, vertices_709) then 18 else
  if p.val = (false, vertices_625) then 21 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_432) then 22 else
  if p.val = (true, vertices_656) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_432), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 6 7 432
cert_row_4 1 0 1 6 7 8 902 134 3
cert_row_4 2 0 2 5 6 7 458 74 3
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 4 1 0 2
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 902
cert_cover_5 2 1 0 1 6 7 134 902 3
cert_coverFacet 3 458
cert_cover_5 3 2 0 2 5 6 74 458 3
cert_coverFacet 4 300
cert_cover_2 4 2 1 4 7 44 300 3
cert_coverFacet 5 440
cert_cover_5 5 0 2 3 4 6 56 440 3
cert_coverFacet 6 728
cert_cover_5 6 3 2 3 5 6 88 728 3
cert_coverFacet 7 944
cert_cover_5 7 0 3 4 6 8 432 944 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1678

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_one_six_1679.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1679

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 647, 91, 835, 805, 369, 78, 198, 962, 684, 204, 184, 472, 944, 7, 27, 67, 515, 37, 517, 49, 81, 289, 321, 769, 14, 70, 134, 74, 194, 834, 642, 44, 76, 140, 548, 196, 644, 56, 88, 152, 168, 200, 176, 304, 336, 400, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_647, vertices_91, vertices_835, vertices_805, vertices_369, vertices_78, vertices_198, vertices_962, vertices_684, vertices_204, vertices_184, vertices_472, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_37, vertices_517, vertices_49, vertices_81, vertices_289, vertices_321, vertices_769, vertices_14, vertices_70, vertices_134, vertices_74, vertices_194, vertices_834, vertices_642, vertices_44, vertices_76, vertices_140, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_152, vertices_168, vertices_200, vertices_176, vertices_304, vertices_336, vertices_400, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_647), (false, vertices_91), (false, vertices_835), (false, vertices_805), (false, vertices_369), (true, vertices_70), (true, vertices_194), (true, vertices_76), (true, vertices_140), (true, vertices_196), (true, vertices_152), (true, vertices_168), (true, vertices_200), (true, vertices_176), (true, vertices_400), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 13 20 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_647) then 14 else
  if p.val = (false, vertices_91) then 18 else
  if p.val = (false, vertices_835) then 19 else
  if p.val = (false, vertices_805) then 15 else
  if p.val = (false, vertices_369) then 22 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_448) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
cert_nodeAtPriority_30 1 70 0 194 76 140 196 152 168 200 176 400 672 448 896 647 805 63 91 835 369
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 5 7 8 834
cert_row_4 1 1 2 4 6 8 684 44 3
cert_row_4 2 2 3 5 6 7 472 88 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 194 962 3
cert_coverFacet 3 684
cert_cover_5 3 1 1 2 4 6 44 684 3
cert_coverFacet 4 204
cert_cover_2 4 2 1 5 6 76 204 3
cert_coverFacet 5 184
cert_cover_2 5 3 2 4 6 56 184 3
cert_coverFacet 6 472
cert_cover_5 6 2 2 3 5 6 88 472 3
cert_coverFacet 7 944
cert_cover_5 7 3 3 4 6 7 176 944 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1679

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_one_six_1680.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1680

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 91, 677, 197, 817, 465, 897, 654, 198, 842, 962, 812, 376, 7, 27, 67, 37, 69, 133, 49, 81, 273, 545, 193, 385, 641, 769, 14, 70, 134, 74, 522, 194, 834, 642, 44, 524, 548, 196, 644, 56, 88, 296, 328, 776, 304, 336, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_91, vertices_677, vertices_197, vertices_817, vertices_465, vertices_897, vertices_654, vertices_198, vertices_842, vertices_962, vertices_812, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_69, vertices_133, vertices_49, vertices_81, vertices_273, vertices_545, vertices_193, vertices_385, vertices_641, vertices_769, vertices_14, vertices_70, vertices_134, vertices_74, vertices_522, vertices_194, vertices_834, vertices_642, vertices_44, vertices_524, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_296, vertices_328, vertices_776, vertices_304, vertices_336, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_91), (false, vertices_677), (false, vertices_197), (false, vertices_817), (false, vertices_465), (false, vertices_897), (true, vertices_134), (true, vertices_522), (true, vertices_194), (true, vertices_834), (true, vertices_642), (true, vertices_524), (true, vertices_296), (true, vertices_328), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_91) then 12 else
  if p.val = (false, vertices_677) then 16 else
  if p.val = (false, vertices_197) then 1 else
  if p.val = (false, vertices_817) then 19 else
  if p.val = (false, vertices_465) then 20 else
  if p.val = (false, vertices_897) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_834) then 13 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_776) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_834), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 14 3
cert_row_2 1 0 5 7 8 834
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 6 0 1 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 842
cert_cover_5 2 1 0 2 5 7 74 842 3
cert_coverFacet 3 962
cert_cover_5 3 1 0 5 6 7 194 962 3
cert_coverFacet 4 812
cert_cover_5 4 2 1 2 4 7 44 812 3
cert_coverFacet 5 376
cert_cover_5 5 3 2 3 4 5 56 376 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1680

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_one_six_1681.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1681

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 229, 681, 897, 94, 330, 692, 852, 964, 824, 344, 7, 11, 67, 259, 37, 69, 41, 521, 161, 193, 385, 641, 769, 30, 70, 74, 266, 322, 52, 84, 532, 164, 196, 836, 644, 56, 88, 280, 552, 328, 776, 560, 336, 784, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_229, vertices_681, vertices_897, vertices_94, vertices_330, vertices_692, vertices_852, vertices_964, vertices_824, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_37, vertices_69, vertices_41, vertices_521, vertices_161, vertices_193, vertices_385, vertices_641, vertices_769, vertices_30, vertices_70, vertices_74, vertices_266, vertices_322, vertices_52, vertices_84, vertices_532, vertices_164, vertices_196, vertices_836, vertices_644, vertices_56, vertices_88, vertices_280, vertices_552, vertices_328, vertices_776, vertices_560, vertices_336, vertices_784, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_229), (false, vertices_681), (false, vertices_897), (true, vertices_74), (true, vertices_84), (true, vertices_532), (true, vertices_836), (true, vertices_644), (true, vertices_88), (true, vertices_280), (true, vertices_328), (true, vertices_560), (true, vertices_336), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_451) then 14 else
  if p.val = (false, vertices_229) then 17 else
  if p.val = (false, vertices_681) then 20 else
  if p.val = (false, vertices_897) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_836) then 18 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_328) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_784) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_836), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 5 7 8 836
cert_row_2 1 0 1 2 3 30
cert_row_4 2 1 3 4 6 8 692 52 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 5 0 1 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 1 0 1 2 5 30 94 3
cert_coverFacet 1 330
cert_cover_2 1 2 0 5 7 74 330 3
cert_coverFacet 2 692
cert_cover_5 2 2 1 3 4 6 52 692 3
cert_coverFacet 3 852
cert_cover_5 3 0 1 3 5 7 84 852 3
cert_coverFacet 4 964
cert_cover_5 4 0 1 5 6 7 196 964 3
cert_coverFacet 5 824
cert_cover_5 5 3 2 3 4 7 56 824 3
cert_coverFacet 6 344
cert_cover_2 6 3 2 5 7 88 344 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1681

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_one_six_1682.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1682

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 229, 681, 897, 94, 330, 820, 468, 932, 568, 856, 7, 11, 67, 259, 37, 69, 41, 521, 161, 193, 385, 641, 769, 30, 70, 74, 266, 322, 52, 84, 276, 164, 804, 196, 388, 56, 88, 536, 552, 328, 776, 560, 336, 784, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_229, vertices_681, vertices_897, vertices_94, vertices_330, vertices_820, vertices_468, vertices_932, vertices_568, vertices_856] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_37, vertices_69, vertices_41, vertices_521, vertices_161, vertices_193, vertices_385, vertices_641, vertices_769, vertices_30, vertices_70, vertices_74, vertices_266, vertices_322, vertices_52, vertices_84, vertices_276, vertices_164, vertices_804, vertices_196, vertices_388, vertices_56, vertices_88, vertices_536, vertices_552, vertices_328, vertices_776, vertices_560, vertices_336, vertices_784, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_229), (false, vertices_681), (false, vertices_897), (true, vertices_74), (true, vertices_84), (true, vertices_276), (true, vertices_804), (true, vertices_388), (true, vertices_88), (true, vertices_536), (true, vertices_328), (true, vertices_560), (true, vertices_336), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 18 15 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_451) then 14 else
  if p.val = (false, vertices_229) then 19 else
  if p.val = (false, vertices_681) then 17 else
  if p.val = (false, vertices_897) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_276) then 4 else
  if p.val = (true, vertices_804) then 20 else
  if p.val = (true, vertices_388) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_328) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_784) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_804), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 3 30
cert_row_2 1 1 4 7 8 804
cert_row_4 2 1 3 5 6 7 468 84 3
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 0 4 1 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 5 30 94 3
cert_coverFacet 1 330
cert_cover_2 1 2 0 5 7 74 330 3
cert_coverFacet 2 820
cert_cover_5 2 1 1 3 4 7 52 820 3
cert_coverFacet 3 468
cert_cover_5 3 2 1 3 5 6 84 468 3
cert_coverFacet 4 932
cert_cover_5 4 1 1 4 6 7 164 932 3
cert_coverFacet 5 568
cert_cover_2 5 3 2 4 8 56 568 3
cert_coverFacet 6 856
cert_cover_5 6 3 2 3 5 7 88 856 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1682

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_one_six_1683.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1683

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 91, 357, 817, 721, 961, 270, 454, 202, 906, 812, 696, 216, 7, 27, 67, 37, 69, 49, 81, 529, 289, 705, 321, 769, 14, 70, 262, 74, 138, 266, 194, 386, 44, 268, 292, 324, 56, 88, 152, 552, 200, 648, 776, 560, 208, 656, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_91, vertices_357, vertices_817, vertices_721, vertices_961, vertices_270, vertices_454, vertices_202, vertices_906, vertices_812, vertices_696, vertices_216] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_69, vertices_49, vertices_81, vertices_529, vertices_289, vertices_705, vertices_321, vertices_769, vertices_14, vertices_70, vertices_262, vertices_74, vertices_138, vertices_266, vertices_194, vertices_386, vertices_44, vertices_268, vertices_292, vertices_324, vertices_56, vertices_88, vertices_152, vertices_552, vertices_200, vertices_648, vertices_776, vertices_560, vertices_208, vertices_656, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_91), (false, vertices_357), (false, vertices_817), (false, vertices_721), (false, vertices_961), (true, vertices_262), (true, vertices_138), (true, vertices_266), (true, vertices_194), (true, vertices_386), (true, vertices_268), (true, vertices_152), (true, vertices_552), (true, vertices_200), (true, vertices_648), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 17 18 20 21 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_357) then 16 else
  if p.val = (false, vertices_817) then 19 else
  if p.val = (false, vertices_721) then 22 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_776) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 70 3
cert_row_4 1 0 2 6 7 8 906 138 3
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 2 3 4 6 8 696 56 3
cert_rows
cert_pivot_2 5 0 1 2
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 906
cert_cover_5 3 1 0 2 6 7 138 906 3
cert_coverFacet 4 812
cert_cover_5 4 2 1 2 4 7 44 812 3
cert_coverFacet 5 696
cert_cover_5 5 3 2 3 4 6 56 696 3
cert_coverFacet 6 216
cert_cover_2 6 3 2 5 6 88 216 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1683

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_one_six_1684.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1684

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 91, 357, 689, 465, 929, 270, 454, 202, 906, 812, 568, 728, 7, 27, 67, 37, 69, 49, 81, 145, 673, 289, 321, 385, 14, 70, 262, 74, 138, 266, 194, 386, 44, 268, 292, 324, 56, 88, 536, 552, 200, 648, 776, 560, 208, 656, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_91, vertices_357, vertices_689, vertices_465, vertices_929, vertices_270, vertices_454, vertices_202, vertices_906, vertices_812, vertices_568, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_69, vertices_49, vertices_81, vertices_145, vertices_673, vertices_289, vertices_321, vertices_385, vertices_14, vertices_70, vertices_262, vertices_74, vertices_138, vertices_266, vertices_194, vertices_386, vertices_44, vertices_268, vertices_292, vertices_324, vertices_56, vertices_88, vertices_536, vertices_552, vertices_200, vertices_648, vertices_776, vertices_560, vertices_208, vertices_656, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_91), (false, vertices_357), (false, vertices_689), (false, vertices_465), (false, vertices_929), (true, vertices_262), (true, vertices_138), (true, vertices_266), (true, vertices_194), (true, vertices_386), (true, vertices_268), (true, vertices_536), (true, vertices_552), (true, vertices_200), (true, vertices_648), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 17 18 20 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_357) then 16 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (false, vertices_465) then 19 else
  if p.val = (false, vertices_929) then 22 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_776) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 4 7 8 812 44 3
cert_row_4 1 0 1 5 6 7 454 70 3
cert_row_4 2 0 2 6 7 8 906 138 3
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 4 1 0 2
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 454
cert_cover_5 1 1 0 1 5 6 70 454 3
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 906
cert_cover_5 3 2 0 2 6 7 138 906 3
cert_coverFacet 4 812
cert_cover_5 4 0 1 2 4 7 44 812 3
cert_coverFacet 5 568
cert_cover_2 5 3 2 4 8 56 568 3
cert_coverFacet 6 728
cert_cover_5 6 3 2 3 5 6 88 728 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1684

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_one_six_1685.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1685

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 91, 707, 805, 689, 209, 78, 454, 898, 364, 824, 472, 912, 7, 27, 67, 515, 37, 773, 49, 81, 145, 545, 193, 641, 14, 70, 262, 74, 194, 386, 642, 770, 44, 76, 292, 324, 56, 88, 280, 296, 328, 560, 208, 400, 656, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_91, vertices_707, vertices_805, vertices_689, vertices_209, vertices_78, vertices_454, vertices_898, vertices_364, vertices_824, vertices_472, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_37, vertices_773, vertices_49, vertices_81, vertices_145, vertices_545, vertices_193, vertices_641, vertices_14, vertices_70, vertices_262, vertices_74, vertices_194, vertices_386, vertices_642, vertices_770, vertices_44, vertices_76, vertices_292, vertices_324, vertices_56, vertices_88, vertices_280, vertices_296, vertices_328, vertices_560, vertices_208, vertices_400, vertices_656, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_91), (false, vertices_707), (false, vertices_805), (false, vertices_689), (false, vertices_209), (true, vertices_70), (true, vertices_386), (true, vertices_76), (true, vertices_324), (true, vertices_280), (true, vertices_296), (true, vertices_328), (true, vertices_400), (true, vertices_784), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 12 19 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_775) then 13 else
  if p.val = (false, vertices_91) then 17 else
  if p.val = (false, vertices_707) then 18 else
  if p.val = (false, vertices_805) then 14 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (false, vertices_209) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_324) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_328) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
cert_nodeAtPriority_8 0 209 1 70 386 76 324 280 296 328 400 784 448 896 775 805 63 91 707 689
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 70 3
cert_row_4 1 1 2 4 5 7 364 44 3
cert_row_4 2 2 3 4 7 8 824 56 3
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 0 1 4 2
cert_heightProof 4
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 364
cert_cover_5 3 1 1 2 4 5 44 364 3
cert_coverFacet 4 824
cert_cover_5 4 2 2 3 4 7 56 824 3
cert_coverFacet 5 472
cert_cover_5 5 3 2 3 5 6 88 472 3
cert_coverFacet 6 912
cert_cover_2 6 6 3 7 8 400 912 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1685

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_one_six_1686.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1686

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 91, 707, 805, 689, 209, 78, 454, 898, 364, 184, 472, 936, 7, 27, 67, 515, 37, 773, 49, 81, 145, 545, 193, 641, 14, 70, 262, 74, 194, 386, 642, 770, 44, 76, 292, 324, 56, 88, 152, 168, 296, 328, 392, 176, 208, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_91, vertices_707, vertices_805, vertices_689, vertices_209, vertices_78, vertices_454, vertices_898, vertices_364, vertices_184, vertices_472, vertices_936] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_515, vertices_37, vertices_773, vertices_49, vertices_81, vertices_145, vertices_545, vertices_193, vertices_641, vertices_14, vertices_70, vertices_262, vertices_74, vertices_194, vertices_386, vertices_642, vertices_770, vertices_44, vertices_76, vertices_292, vertices_324, vertices_56, vertices_88, vertices_152, vertices_168, vertices_296, vertices_328, vertices_392, vertices_176, vertices_208, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_91), (false, vertices_707), (false, vertices_805), (false, vertices_689), (false, vertices_209), (true, vertices_70), (true, vertices_386), (true, vertices_76), (true, vertices_324), (true, vertices_152), (true, vertices_168), (true, vertices_296), (true, vertices_328), (true, vertices_392), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 12 19 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_775) then 13 else
  if p.val = (false, vertices_91) then 17 else
  if p.val = (false, vertices_707) then 18 else
  if p.val = (false, vertices_805) then 14 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (false, vertices_209) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_324) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_328) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
cert_nodeAtPriority_8 0 209 1 70 386 76 324 152 168 296 328 392 448 896 775 805 63 91 707 689
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 70 3
cert_row_4 1 1 2 4 5 7 364 44 3
cert_row_4 2 2 3 5 6 7 472 88 3
cert_row_4 3 2 4 6 7 8 936 168 3
cert_rows
cert_pivot_2 0 1 3 2
cert_heightProof 4
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 898
cert_cover_2 2 6 0 7 8 386 898 3
cert_coverFacet 3 364
cert_cover_5 3 1 1 2 4 5 44 364 3
cert_coverFacet 4 184
cert_cover_2 4 3 2 4 6 56 184 3
cert_coverFacet 5 472
cert_cover_5 5 2 2 3 5 6 88 472 3
cert_coverFacet 6 936
cert_cover_5 6 3 2 4 6 7 168 936 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1686

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_one_six_1687.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1687

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 91, 421, 837, 625, 929, 142, 454, 330, 906, 172, 696, 856, 7, 27, 67, 37, 69, 261, 49, 81, 417, 545, 577, 769, 14, 70, 134, 74, 138, 266, 322, 386, 44, 140, 164, 324, 388, 56, 88, 536, 168, 328, 648, 776, 560, 592, 672, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_91, vertices_421, vertices_837, vertices_625, vertices_929, vertices_142, vertices_454, vertices_330, vertices_906, vertices_172, vertices_696, vertices_856] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_27, vertices_67, vertices_37, vertices_69, vertices_261, vertices_49, vertices_81, vertices_417, vertices_545, vertices_577, vertices_769, vertices_14, vertices_70, vertices_134, vertices_74, vertices_138, vertices_266, vertices_322, vertices_386, vertices_44, vertices_140, vertices_164, vertices_324, vertices_388, vertices_56, vertices_88, vertices_536, vertices_168, vertices_328, vertices_648, vertices_776, vertices_560, vertices_592, vertices_672, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_91), (false, vertices_421), (false, vertices_837), (false, vertices_625), (false, vertices_929), (true, vertices_134), (true, vertices_138), (true, vertices_266), (true, vertices_322), (true, vertices_386), (true, vertices_140), (true, vertices_536), (true, vertices_168), (true, vertices_328), (true, vertices_648), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 17 18 20 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_91) then 13 else
  if p.val = (false, vertices_421) then 21 else
  if p.val = (false, vertices_837) then 16 else
  if p.val = (false, vertices_625) then 19 else
  if p.val = (false, vertices_929) then 22 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_168) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_776) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 70 3
cert_row_4 1 0 2 6 7 8 906 138 3
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 1 0 4 2
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 330
cert_cover_2 2 2 0 5 7 74 330 3
cert_coverFacet 3 906
cert_cover_5 3 1 0 2 6 7 138 906 3
cert_coverFacet 4 172
cert_cover_2 4 2 1 4 6 44 172 3
cert_coverFacet 5 696
cert_cover_5 5 2 2 3 4 6 56 696 3
cert_coverFacet 6 856
cert_cover_5 6 3 2 3 5 7 88 856 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1687

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_1800 : Certifies 1800 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1658.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1801 : Certifies 1801 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1659.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1802 : Certifies 1802 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1660.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1803 : Certifies 1803 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1661.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1804 : Certifies 1804 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1662.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1805 : Certifies 1805 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1663.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1806 : Certifies 1806 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1664.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1807 : Certifies 1807 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1665.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1808 : Certifies 1808 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1666.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1809 : Certifies 1809 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1667.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1810 : Certifies 1810 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1668.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1811 : Certifies 1811 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1669.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1812 : Certifies 1812 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1670.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1813 : Certifies 1813 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1671.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1814 : Certifies 1814 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1672.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1815 : Certifies 1815 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1673.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1816 : Certifies 1816 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1674.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1817 : Certifies 1817 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1675.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1818 : Certifies 1818 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1676.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1819 : Certifies 1819 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1677.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1820 : Certifies 1820 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1678.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1821 : Certifies 1821 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1679.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1822 : Certifies 1822 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1680.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1823 : Certifies 1823 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1681.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1824 : Certifies 1824 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1682.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1825 : Certifies 1825 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1683.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1826 : Certifies 1826 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1684.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1827 : Certifies 1827 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1685.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1828 : Certifies 1828 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1686.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1829 : Certifies 1829 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1687.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B060 (j : Fin 30) :
    Certifies (1800 + j.val) := by
  fin_cases j
  · exact projection_1800
  · exact projection_1801
  · exact projection_1802
  · exact projection_1803
  · exact projection_1804
  · exact projection_1805
  · exact projection_1806
  · exact projection_1807
  · exact projection_1808
  · exact projection_1809
  · exact projection_1810
  · exact projection_1811
  · exact projection_1812
  · exact projection_1813
  · exact projection_1814
  · exact projection_1815
  · exact projection_1816
  · exact projection_1817
  · exact projection_1818
  · exact projection_1819
  · exact projection_1820
  · exact projection_1821
  · exact projection_1822
  · exact projection_1823
  · exact projection_1824
  · exact projection_1825
  · exact projection_1826
  · exact projection_1827
  · exact projection_1828
  · exact projection_1829

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
