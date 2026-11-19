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
/- Source: ProjectionCertificates/R_one_six_0358.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0358

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 277, 837, 345, 654, 582, 962, 684, 820, 248, 496, 928, 7, 11, 67, 21, 69, 261, 25, 73, 273, 321, 14, 70, 518, 138, 194, 578, 642, 44, 652, 52, 276, 548, 580, 772, 56, 88, 168, 200, 240, 304, 336, 416, 672, 800, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_277, vertices_837, vertices_345, vertices_654, vertices_582, vertices_962, vertices_684, vertices_820, vertices_248, vertices_496, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_261, vertices_25, vertices_73, vertices_273, vertices_321, vertices_14, vertices_70, vertices_518, vertices_138, vertices_194, vertices_578, vertices_642, vertices_44, vertices_652, vertices_52, vertices_276, vertices_548, vertices_580, vertices_772, vertices_56, vertices_88, vertices_168, vertices_200, vertices_240, vertices_304, vertices_336, vertices_416, vertices_672, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_277), (false, vertices_837), (false, vertices_345), (true, vertices_518), (true, vertices_578), (true, vertices_642), (true, vertices_652), (true, vertices_548), (true, vertices_168), (true, vertices_240), (true, vertices_304), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_277) then 1 else
  if p.val = (false, vertices_837) then 17 else
  if p.val = (false, vertices_345) then 20 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_652) then 18 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_240) then 22 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_448) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_652), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 8 652
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_2 2 3 4 5 6 240
cert_row_4 3 1 3 4 7 8 820 52 3
cert_rows
cert_pivot_2 2 0 5 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 582
cert_cover_2 1 1 0 5 8 70 582 3
cert_coverFacet 2 962
cert_cover_5 2 1 0 5 6 7 194 962 3
cert_coverFacet 3 684
cert_cover_5 3 0 1 2 4 6 44 684 3
cert_coverFacet 4 820
cert_cover_5 4 3 1 3 4 7 52 820 3
cert_coverFacet 5 248
cert_cover_5 5 2 2 3 4 5 56 248 3
cert_coverFacet 6 496
cert_cover_5 6 2 3 4 5 7 240 496 3
cert_coverFacet 7 928
cert_cover_2 7 6 4 7 8 416 928 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0358

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_one_six_0359.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0359

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 789, 837, 345, 654, 582, 962, 684, 564, 312, 488, 944, 7, 11, 67, 21, 69, 773, 25, 73, 273, 321, 14, 70, 518, 138, 194, 578, 642, 44, 652, 52, 532, 548, 580, 56, 280, 168, 296, 200, 328, 304, 560, 784, 416, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_789, vertices_837, vertices_345, vertices_654, vertices_582, vertices_962, vertices_684, vertices_564, vertices_312, vertices_488, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_773, vertices_25, vertices_73, vertices_273, vertices_321, vertices_14, vertices_70, vertices_518, vertices_138, vertices_194, vertices_578, vertices_642, vertices_44, vertices_652, vertices_52, vertices_532, vertices_548, vertices_580, vertices_56, vertices_280, vertices_168, vertices_296, vertices_200, vertices_328, vertices_304, vertices_560, vertices_784, vertices_416, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_789), (false, vertices_837), (false, vertices_345), (true, vertices_518), (true, vertices_578), (true, vertices_642), (true, vertices_652), (true, vertices_548), (true, vertices_168), (true, vertices_296), (true, vertices_304), (true, vertices_560), (true, vertices_416), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 19 15 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_789) then 20 else
  if p.val = (false, vertices_837) then 21 else
  if p.val = (false, vertices_345) then 17 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_578) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_652) then 18 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_448) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_652), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 8 652
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 2 4 5 6 7 488 168 2
cert_row_4 3 3 4 6 7 8 944 304 2
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 582
cert_cover_2 1 1 0 5 8 70 582 3
cert_coverFacet 2 962
cert_cover_5 2 1 0 5 6 7 194 962 3
cert_coverFacet 3 684
cert_cover_5 3 0 1 2 4 6 44 684 3
cert_coverFacet 4 564
cert_cover_2 4 3 1 4 8 52 564 3
cert_coverFacet 5 312
cert_cover_2 5 3 2 4 7 56 312 3
cert_coverFacet 6 488
cert_cover_5 6 2 2 4 5 6 168 488 2
cert_coverFacet 7 944
cert_cover_5 7 3 3 4 6 7 304 944 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0359

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_one_six_0360.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0360

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 789, 837, 345, 654, 582, 962, 684, 564, 248, 944, 464, 7, 11, 67, 21, 69, 773, 25, 73, 273, 321, 14, 70, 518, 138, 194, 578, 642, 44, 652, 52, 532, 548, 580, 56, 88, 168, 200, 176, 560, 208, 336, 400, 784, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_789, vertices_837, vertices_345, vertices_654, vertices_582, vertices_962, vertices_684, vertices_564, vertices_248, vertices_944, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_773, vertices_25, vertices_73, vertices_273, vertices_321, vertices_14, vertices_70, vertices_518, vertices_138, vertices_194, vertices_578, vertices_642, vertices_44, vertices_652, vertices_52, vertices_532, vertices_548, vertices_580, vertices_56, vertices_88, vertices_168, vertices_200, vertices_176, vertices_560, vertices_208, vertices_336, vertices_400, vertices_784, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_789), (false, vertices_837), (false, vertices_345), (true, vertices_518), (true, vertices_578), (true, vertices_642), (true, vertices_652), (true, vertices_548), (true, vertices_168), (true, vertices_176), (true, vertices_560), (true, vertices_208), (true, vertices_400), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 19 15 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_789) then 20 else
  if p.val = (false, vertices_837) then 21 else
  if p.val = (false, vertices_345) then 17 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_578) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_652) then 18 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_448) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_652), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 8 652
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 2 3 4 5 6 248 56 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 582
cert_cover_2 1 1 0 5 8 70 582 3
cert_coverFacet 2 962
cert_cover_5 2 1 0 5 6 7 194 962 3
cert_coverFacet 3 684
cert_cover_5 3 0 1 2 4 6 44 684 3
cert_coverFacet 4 564
cert_cover_2 4 3 1 4 8 52 564 3
cert_coverFacet 5 248
cert_cover_5 5 2 2 3 4 5 56 248 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 176 944 3
cert_coverFacet 7 464
cert_cover_2 7 5 3 6 7 208 464 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0360

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_one_six_0361.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0361

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 277, 837, 345, 654, 582, 962, 684, 820, 248, 944, 464, 7, 11, 67, 21, 69, 261, 25, 73, 273, 321, 14, 70, 518, 138, 194, 578, 642, 44, 652, 52, 276, 548, 580, 772, 56, 88, 168, 200, 176, 816, 208, 336, 400, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_277, vertices_837, vertices_345, vertices_654, vertices_582, vertices_962, vertices_684, vertices_820, vertices_248, vertices_944, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_261, vertices_25, vertices_73, vertices_273, vertices_321, vertices_14, vertices_70, vertices_518, vertices_138, vertices_194, vertices_578, vertices_642, vertices_44, vertices_652, vertices_52, vertices_276, vertices_548, vertices_580, vertices_772, vertices_56, vertices_88, vertices_168, vertices_200, vertices_176, vertices_816, vertices_208, vertices_336, vertices_400, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_277), (false, vertices_837), (false, vertices_345), (true, vertices_518), (true, vertices_578), (true, vertices_642), (true, vertices_652), (true, vertices_548), (true, vertices_168), (true, vertices_176), (true, vertices_816), (true, vertices_208), (true, vertices_400), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_277) then 1 else
  if p.val = (false, vertices_837) then 17 else
  if p.val = (false, vertices_345) then 20 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_652) then 18 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_816) then 22 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_448) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_652), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 8 652
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_2 2 3 4 7 8 816
cert_row_4 3 2 3 4 5 6 248 56 3
cert_rows
cert_pivot_2 1 0 7 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 582
cert_cover_2 1 1 0 5 8 70 582 3
cert_coverFacet 2 962
cert_cover_5 2 1 0 5 6 7 194 962 3
cert_coverFacet 3 684
cert_cover_5 3 0 1 2 4 6 44 684 3
cert_coverFacet 4 820
cert_cover_5 4 2 1 3 4 7 52 820 3
cert_coverFacet 5 248
cert_cover_5 5 3 2 3 4 5 56 248 3
cert_coverFacet 6 944
cert_cover_5 6 2 3 4 6 7 176 944 3
cert_coverFacet 7 464
cert_cover_2 7 5 3 6 7 208 464 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0361

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_one_six_0362.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0362

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 653, 837, 961, 790, 326, 346, 172, 692, 312, 488, 944, 7, 11, 67, 13, 69, 517, 137, 193, 833, 641, 22, 70, 262, 26, 74, 274, 322, 44, 140, 52, 532, 164, 324, 644, 772, 56, 280, 168, 296, 200, 328, 688, 304, 784, 416, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_653, vertices_837, vertices_961, vertices_790, vertices_326, vertices_346, vertices_172, vertices_692, vertices_312, vertices_488, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_69, vertices_517, vertices_137, vertices_193, vertices_833, vertices_641, vertices_22, vertices_70, vertices_262, vertices_26, vertices_74, vertices_274, vertices_322, vertices_44, vertices_140, vertices_52, vertices_532, vertices_164, vertices_324, vertices_644, vertices_772, vertices_56, vertices_280, vertices_168, vertices_296, vertices_200, vertices_328, vertices_688, vertices_304, vertices_784, vertices_416, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_653), (false, vertices_837), (false, vertices_961), (true, vertices_262), (true, vertices_274), (true, vertices_322), (true, vertices_532), (true, vertices_164), (true, vertices_280), (true, vertices_168), (true, vertices_296), (true, vertices_328), (true, vertices_688), (true, vertices_304), (true, vertices_784), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 19 21 22 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_653) then 17 else
  if p.val = (false, vertices_837) then 23 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_688) then 20 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_416) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(true, vertices_688), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 7 8 790 22 3
cert_row_2 1 3 4 6 8 688
cert_row_4 2 0 2 3 5 7 346 26 3
cert_row_4 3 2 4 5 6 7 488 168 2
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 22 790 3
cert_coverFacet 1 326
cert_cover_2 1 1 0 5 7 70 326 3
cert_coverFacet 2 346
cert_cover_5 2 2 0 2 3 5 26 346 3
cert_coverFacet 3 172
cert_cover_2 3 2 1 4 6 44 172 3
cert_coverFacet 4 692
cert_cover_5 4 1 1 3 4 6 52 692 3
cert_coverFacet 5 312
cert_cover_2 5 3 2 4 7 56 312 3
cert_coverFacet 6 488
cert_cover_5 6 3 2 4 5 6 168 488 2
cert_coverFacet 7 944
cert_cover_5 7 1 3 4 6 7 688 944 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0362

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_one_six_0363.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0363

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 789, 325, 345, 654, 838, 962, 684, 564, 248, 944, 464, 7, 11, 67, 21, 69, 261, 25, 73, 273, 321, 14, 70, 518, 138, 194, 834, 642, 44, 652, 52, 532, 548, 324, 772, 56, 88, 168, 200, 176, 560, 208, 336, 400, 784, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_789, vertices_325, vertices_345, vertices_654, vertices_838, vertices_962, vertices_684, vertices_564, vertices_248, vertices_944, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_261, vertices_25, vertices_73, vertices_273, vertices_321, vertices_14, vertices_70, vertices_518, vertices_138, vertices_194, vertices_834, vertices_642, vertices_44, vertices_652, vertices_52, vertices_532, vertices_548, vertices_324, vertices_772, vertices_56, vertices_88, vertices_168, vertices_200, vertices_176, vertices_560, vertices_208, vertices_336, vertices_400, vertices_784, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_789), (false, vertices_325), (false, vertices_345), (true, vertices_518), (true, vertices_834), (true, vertices_642), (true, vertices_652), (true, vertices_548), (true, vertices_168), (true, vertices_176), (true, vertices_560), (true, vertices_208), (true, vertices_400), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_325) then 1 else
  if p.val = (false, vertices_345) then 21 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_834) then 15 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_652) then 19 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_448) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_325), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_834), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_652), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 5 7 8 834
cert_row_2 1 1 2 6 8 652
cert_row_4 2 2 3 4 5 6 248 56 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 1 0 1 2 6 14 654 3
cert_coverFacet 1 838
cert_cover_5 1 0 0 1 5 7 70 838 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 194 962 3
cert_coverFacet 3 684
cert_cover_5 3 1 1 2 4 6 44 684 3
cert_coverFacet 4 564
cert_cover_2 4 3 1 4 8 52 564 3
cert_coverFacet 5 248
cert_cover_5 5 2 2 3 4 5 56 248 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 176 944 3
cert_coverFacet 7 464
cert_cover_2 7 5 3 6 7 208 464 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0363

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_one_six_0364.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0364

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 789, 325, 345, 654, 838, 962, 684, 564, 312, 488, 944, 7, 11, 67, 21, 69, 261, 25, 73, 273, 321, 14, 70, 518, 138, 194, 834, 642, 44, 652, 52, 532, 548, 324, 772, 56, 280, 168, 296, 200, 328, 304, 560, 784, 416, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_789, vertices_325, vertices_345, vertices_654, vertices_838, vertices_962, vertices_684, vertices_564, vertices_312, vertices_488, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_261, vertices_25, vertices_73, vertices_273, vertices_321, vertices_14, vertices_70, vertices_518, vertices_138, vertices_194, vertices_834, vertices_642, vertices_44, vertices_652, vertices_52, vertices_532, vertices_548, vertices_324, vertices_772, vertices_56, vertices_280, vertices_168, vertices_296, vertices_200, vertices_328, vertices_304, vertices_560, vertices_784, vertices_416, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_789), (false, vertices_325), (false, vertices_345), (true, vertices_518), (true, vertices_834), (true, vertices_642), (true, vertices_652), (true, vertices_548), (true, vertices_168), (true, vertices_296), (true, vertices_304), (true, vertices_560), (true, vertices_416), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_325) then 1 else
  if p.val = (false, vertices_345) then 21 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_834) then 15 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_652) then 19 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_448) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_325), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_834), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_652), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 5 7 8 834
cert_row_2 1 1 2 6 8 652
cert_row_4 2 2 4 5 6 7 488 168 2
cert_row_4 3 3 4 6 7 8 944 304 2
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 1 0 1 2 6 14 654 3
cert_coverFacet 1 838
cert_cover_5 1 0 0 1 5 7 70 838 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 194 962 3
cert_coverFacet 3 684
cert_cover_5 3 1 1 2 4 6 44 684 3
cert_coverFacet 4 564
cert_cover_2 4 3 1 4 8 52 564 3
cert_coverFacet 5 312
cert_cover_2 5 3 2 4 7 56 312 3
cert_coverFacet 6 488
cert_cover_5 6 2 2 4 5 6 168 488 2
cert_coverFacet 7 944
cert_cover_5 7 3 3 4 6 7 304 944 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0364

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_one_six_0365.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0365

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 597, 409, 465, 654, 582, 962, 428, 564, 932, 312, 880, 7, 11, 67, 21, 69, 25, 137, 81, 401, 193, 14, 70, 518, 138, 194, 578, 642, 44, 140, 52, 532, 420, 548, 580, 644, 56, 280, 296, 392, 304, 560, 336, 592, 800, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_597, vertices_409, vertices_465, vertices_654, vertices_582, vertices_962, vertices_428, vertices_564, vertices_932, vertices_312, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_25, vertices_137, vertices_81, vertices_401, vertices_193, vertices_14, vertices_70, vertices_518, vertices_138, vertices_194, vertices_578, vertices_642, vertices_44, vertices_140, vertices_52, vertices_532, vertices_420, vertices_548, vertices_580, vertices_644, vertices_56, vertices_280, vertices_296, vertices_392, vertices_304, vertices_560, vertices_336, vertices_592, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_597), (false, vertices_409), (false, vertices_465), (true, vertices_518), (true, vertices_578), (true, vertices_642), (true, vertices_140), (true, vertices_420), (true, vertices_548), (true, vertices_644), (true, vertices_296), (true, vertices_304), (true, vertices_560), (true, vertices_800), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_597) then 17 else
  if p.val = (false, vertices_409) then 21 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_578) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_420) then 18 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_832) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_420), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 14 3
cert_row_2 1 1 4 6 7 420
cert_row_4 2 0 5 6 7 8 962 194 3
cert_row_4 3 3 4 5 7 8 880 304 2
cert_rows
cert_pivot_2 2 1 0 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 582
cert_cover_2 1 1 0 5 8 70 582 3
cert_coverFacet 2 962
cert_cover_5 2 2 0 5 6 7 194 962 3
cert_coverFacet 3 428
cert_cover_5 3 1 1 2 4 6 44 428 3
cert_coverFacet 4 564
cert_cover_2 4 3 1 4 8 52 564 3
cert_coverFacet 5 932
cert_cover_5 5 1 1 4 6 8 420 932 3
cert_coverFacet 6 312
cert_cover_2 6 3 2 4 7 56 312 3
cert_coverFacet 7 880
cert_cover_5 7 3 3 4 5 7 304 880 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0365

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_one_six_0366.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0366

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 277, 453, 297, 817, 78, 714, 604, 852, 696, 424, 992, 7, 11, 131, 21, 197, 261, 41, 265, 49, 273, 289, 385, 14, 70, 74, 138, 194, 28, 76, 596, 276, 324, 56, 536, 168, 296, 584, 392, 648, 560, 784, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_277, vertices_453, vertices_297, vertices_817, vertices_78, vertices_714, vertices_604, vertices_852, vertices_696, vertices_424, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_197, vertices_261, vertices_41, vertices_265, vertices_49, vertices_273, vertices_289, vertices_385, vertices_14, vertices_70, vertices_74, vertices_138, vertices_194, vertices_28, vertices_76, vertices_596, vertices_276, vertices_324, vertices_56, vertices_536, vertices_168, vertices_296, vertices_584, vertices_392, vertices_648, vertices_560, vertices_784, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_277), (false, vertices_453), (false, vertices_297), (false, vertices_817), (true, vertices_74), (true, vertices_76), (true, vertices_596), (true, vertices_536), (true, vertices_168), (true, vertices_584), (true, vertices_648), (true, vertices_416), (true, vertices_672), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 19 14 16 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 20 else
  if p.val = (false, vertices_395) then 13 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_453) then 21 else
  if p.val = (false, vertices_297) then 1 else
  if p.val = (false, vertices_817) then 17 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_596) then 18 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_704) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_297), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_596), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 5 8 596
cert_row_4 1 0 2 5 6 8 714 74 3
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 4 5 6 7 8 992 416 1
cert_rows
cert_pivot_2 1 0 2 4
cert_heightProof 4
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 714
cert_cover_5 1 1 0 2 5 6 74 714 3
cert_coverFacet 2 604
cert_cover_5 2 0 1 2 3 5 28 604 3
cert_coverFacet 3 852
cert_cover_5 3 0 1 3 5 7 596 852 3
cert_coverFacet 4 696
cert_cover_5 4 2 2 3 4 6 56 696 3
cert_coverFacet 5 424
cert_cover_2 5 4 2 6 7 168 424 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 416 992 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0366

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_one_six_0371.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0371

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 395, 707, 597, 297, 689, 417, 206, 796, 460, 836, 824, 992, 7, 11, 67, 131, 21, 69, 41, 265, 49, 529, 161, 289, 577, 385, 641, 14, 70, 138, 194, 28, 204, 268, 532, 324, 580, 772, 56, 792, 296, 392, 560, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_395, vertices_707, vertices_597, vertices_297, vertices_689, vertices_417, vertices_206, vertices_796, vertices_460, vertices_836, vertices_824, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_131, vertices_21, vertices_69, vertices_41, vertices_265, vertices_49, vertices_529, vertices_161, vertices_289, vertices_577, vertices_385, vertices_641, vertices_14, vertices_70, vertices_138, vertices_194, vertices_28, vertices_204, vertices_268, vertices_532, vertices_324, vertices_580, vertices_772, vertices_56, vertices_792, vertices_296, vertices_392, vertices_560, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_395), (false, vertices_707), (false, vertices_597), (false, vertices_297), (false, vertices_689), (false, vertices_417), (true, vertices_204), (true, vertices_268), (true, vertices_324), (true, vertices_772), (true, vertices_792), (true, vertices_800), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 16 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_395) then 10 else
  if p.val = (false, vertices_707) then 11 else
  if p.val = (false, vertices_597) then 14 else
  if p.val = (false, vertices_297) then 1 else
  if p.val = (false, vertices_689) then 19 else
  if p.val = (false, vertices_417) then 2 else
  if p.val = (true, vertices_204) then 15 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_324) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_792) then 17 else
  if p.val = (true, vertices_800) then 6 else
  if p.val = (true, vertices_448) then 7 else
  if p.val = (true, vertices_832) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_297), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_417), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(true, vertices_792), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 7 8 792
cert_row_2 1 1 2 5 6 204
cert_row_4 2 4 5 6 7 8 992 416 1
cert_rows_3
cert_pivot_3 1 3 4
cert_heightProof 3
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 14 206 3
cert_coverFacet 1 796
cert_cover_5 1 0 1 2 3 7 28 796 3
cert_coverFacet 2 460
cert_cover_5 2 1 1 2 5 7 204 460 3
cert_coverFacet 3 836
cert_cover_2 3 5 1 7 8 324 836 3
cert_coverFacet 4 824
cert_cover_5 4 0 2 3 4 7 56 824 3
cert_coverFacet 5 992
cert_cover_5 5 2 4 5 6 7 416 992 1
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0371

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_one_six_0374.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0374

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 323, 213, 617, 241, 833, 270, 454, 796, 916, 696, 992, 7, 11, 67, 259, 21, 69, 41, 521, 49, 209, 97, 321, 577, 769, 14, 70, 262, 266, 322, 28, 268, 148, 788, 196, 388, 56, 536, 552, 776, 176, 656, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_323, vertices_213, vertices_617, vertices_241, vertices_833, vertices_270, vertices_454, vertices_796, vertices_916, vertices_696, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_41, vertices_521, vertices_49, vertices_209, vertices_97, vertices_321, vertices_577, vertices_769, vertices_14, vertices_70, vertices_262, vertices_266, vertices_322, vertices_28, vertices_268, vertices_148, vertices_788, vertices_196, vertices_388, vertices_56, vertices_536, vertices_552, vertices_776, vertices_176, vertices_656, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_323), (false, vertices_213), (false, vertices_617), (false, vertices_241), (false, vertices_833), (true, vertices_262), (true, vertices_268), (true, vertices_788), (true, vertices_388), (true, vertices_536), (true, vertices_656), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 16 13 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 12 else
  if p.val = (false, vertices_323) then 1 else
  if p.val = (false, vertices_213) then 19 else
  if p.val = (false, vertices_617) then 15 else
  if p.val = (false, vertices_241) then 20 else
  if p.val = (false, vertices_833) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_788) then 17 else
  if p.val = (true, vertices_388) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_656) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_833), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(true, vertices_788), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 70 3
cert_row_2 1 1 3 7 8 788
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 796
cert_cover_5 2 1 1 2 3 7 28 796 3
cert_coverFacet 3 916
cert_cover_5 3 1 1 3 6 7 148 916 3
cert_coverFacet 4 696
cert_cover_5 4 2 2 3 4 6 56 696 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 224 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0374

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_one_six_0375.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0375

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 579, 213, 617, 241, 270, 454, 834, 796, 916, 696, 992, 7, 11, 67, 515, 21, 69, 41, 521, 49, 209, 97, 577, 14, 70, 262, 266, 322, 578, 770, 28, 268, 148, 788, 196, 388, 56, 536, 552, 776, 176, 656, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_579, vertices_213, vertices_617, vertices_241, vertices_270, vertices_454, vertices_834, vertices_796, vertices_916, vertices_696, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_515, vertices_21, vertices_69, vertices_41, vertices_521, vertices_49, vertices_209, vertices_97, vertices_577, vertices_14, vertices_70, vertices_262, vertices_266, vertices_322, vertices_578, vertices_770, vertices_28, vertices_268, vertices_148, vertices_788, vertices_196, vertices_388, vertices_56, vertices_536, vertices_552, vertices_776, vertices_176, vertices_656, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_579), (false, vertices_213), (false, vertices_617), (false, vertices_241), (true, vertices_262), (true, vertices_322), (true, vertices_268), (true, vertices_788), (true, vertices_388), (true, vertices_536), (true, vertices_656), (true, vertices_672), (true, vertices_448), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 17 14 19 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_579) then 1 else
  if p.val = (false, vertices_213) then 20 else
  if p.val = (false, vertices_617) then 16 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_788) then 18 else
  if p.val = (true, vertices_388) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_656) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_832) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_579), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(true, vertices_788), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 70 3
cert_row_2 1 1 3 7 8 788
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 834
cert_cover_2 2 5 0 7 8 322 834 3
cert_coverFacet 3 796
cert_cover_5 3 1 1 2 3 7 28 796 3
cert_coverFacet 4 916
cert_cover_5 4 1 1 3 6 7 148 916 3
cert_coverFacet 5 696
cert_cover_5 5 2 2 3 4 6 56 696 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0375

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_one_six_0376.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0376

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 267, 835, 213, 617, 777, 241, 270, 454, 796, 916, 696, 992, 7, 11, 67, 259, 21, 69, 41, 265, 521, 49, 209, 97, 577, 769, 14, 70, 262, 266, 322, 28, 268, 148, 788, 196, 388, 56, 536, 552, 776, 176, 656, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_267, vertices_835, vertices_213, vertices_617, vertices_777, vertices_241, vertices_270, vertices_454, vertices_796, vertices_916, vertices_696, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_41, vertices_265, vertices_521, vertices_49, vertices_209, vertices_97, vertices_577, vertices_769, vertices_14, vertices_70, vertices_262, vertices_266, vertices_322, vertices_28, vertices_268, vertices_148, vertices_788, vertices_196, vertices_388, vertices_56, vertices_536, vertices_552, vertices_776, vertices_176, vertices_656, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_267), (false, vertices_835), (false, vertices_213), (false, vertices_617), (false, vertices_777), (false, vertices_241), (true, vertices_262), (true, vertices_268), (true, vertices_788), (true, vertices_388), (true, vertices_536), (true, vertices_656), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 16 13 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_267) then 1 else
  if p.val = (false, vertices_835) then 12 else
  if p.val = (false, vertices_213) then 19 else
  if p.val = (false, vertices_617) then 15 else
  if p.val = (false, vertices_777) then 2 else
  if p.val = (false, vertices_241) then 20 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_788) then 17 else
  if p.val = (true, vertices_388) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_656) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(true, vertices_788), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 70 3
cert_row_2 1 1 3 7 8 788
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 796
cert_cover_5 2 1 1 2 3 7 28 796 3
cert_coverFacet 3 916
cert_cover_5 3 1 1 3 6 7 148 916 3
cert_coverFacet 4 696
cert_cover_5 4 2 2 3 4 6 56 696 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 224 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0376

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_one_six_0377.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0377

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 523, 835, 213, 617, 241, 270, 454, 778, 796, 916, 696, 992, 7, 11, 67, 515, 21, 69, 41, 521, 49, 209, 97, 577, 14, 70, 262, 266, 522, 322, 770, 28, 268, 148, 788, 196, 388, 56, 536, 552, 776, 176, 656, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_523, vertices_835, vertices_213, vertices_617, vertices_241, vertices_270, vertices_454, vertices_778, vertices_796, vertices_916, vertices_696, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_515, vertices_21, vertices_69, vertices_41, vertices_521, vertices_49, vertices_209, vertices_97, vertices_577, vertices_14, vertices_70, vertices_262, vertices_266, vertices_522, vertices_322, vertices_770, vertices_28, vertices_268, vertices_148, vertices_788, vertices_196, vertices_388, vertices_56, vertices_536, vertices_552, vertices_776, vertices_176, vertices_656, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_523), (false, vertices_835), (false, vertices_213), (false, vertices_617), (false, vertices_241), (true, vertices_262), (true, vertices_266), (true, vertices_268), (true, vertices_788), (true, vertices_388), (true, vertices_536), (true, vertices_776), (true, vertices_656), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 17 14 19 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_523) then 1 else
  if p.val = (false, vertices_835) then 13 else
  if p.val = (false, vertices_213) then 20 else
  if p.val = (false, vertices_617) then 16 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_788) then 18 else
  if p.val = (true, vertices_388) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_656) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_523), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(true, vertices_788), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 70 3
cert_row_2 1 1 3 7 8 788
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 796
cert_cover_5 3 1 1 2 3 7 28 796 3
cert_coverFacet 4 916
cert_cover_5 4 1 1 3 6 7 148 916 3
cert_coverFacet 5 696
cert_cover_5 5 2 2 3 4 6 56 696 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0377

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_one_six_0378.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0378

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 835, 85, 617, 241, 270, 454, 796, 212, 916, 696, 992, 7, 11, 67, 771, 21, 69, 41, 521, 49, 81, 97, 577, 14, 70, 262, 266, 322, 28, 268, 84, 148, 788, 196, 388, 56, 536, 552, 776, 176, 208, 656, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_835, vertices_85, vertices_617, vertices_241, vertices_270, vertices_454, vertices_796, vertices_212, vertices_916, vertices_696, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_771, vertices_21, vertices_69, vertices_41, vertices_521, vertices_49, vertices_81, vertices_97, vertices_577, vertices_14, vertices_70, vertices_262, vertices_266, vertices_322, vertices_28, vertices_268, vertices_84, vertices_148, vertices_788, vertices_196, vertices_388, vertices_56, vertices_536, vertices_552, vertices_776, vertices_176, vertices_208, vertices_656, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_835), (false, vertices_85), (false, vertices_617), (false, vertices_241), (true, vertices_262), (true, vertices_268), (true, vertices_148), (true, vertices_788), (true, vertices_196), (true, vertices_388), (true, vertices_536), (true, vertices_656), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_835) then 14 else
  if p.val = (false, vertices_85) then 1 else
  if p.val = (false, vertices_617) then 19 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_148) then 4 else
  if p.val = (true, vertices_788) then 17 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_656) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_85), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_788), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 70 3
cert_row_2 1 1 3 7 8 788
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 796
cert_cover_5 2 1 1 2 3 7 28 796 3
cert_coverFacet 3 212
cert_cover_2 3 3 1 5 6 84 212 3
cert_coverFacet 4 916
cert_cover_5 4 1 1 3 6 7 148 916 3
cert_coverFacet 5 696
cert_cover_5 5 2 2 3 4 6 56 696 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0378

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_one_six_0379.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0379

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 835, 149, 197, 617, 241, 270, 454, 796, 916, 696, 992, 7, 11, 67, 771, 21, 69, 133, 41, 521, 49, 145, 97, 193, 577, 14, 70, 262, 266, 322, 28, 268, 148, 788, 196, 388, 56, 536, 552, 776, 176, 656, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_835, vertices_149, vertices_197, vertices_617, vertices_241, vertices_270, vertices_454, vertices_796, vertices_916, vertices_696, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_771, vertices_21, vertices_69, vertices_133, vertices_41, vertices_521, vertices_49, vertices_145, vertices_97, vertices_193, vertices_577, vertices_14, vertices_70, vertices_262, vertices_266, vertices_322, vertices_28, vertices_268, vertices_148, vertices_788, vertices_196, vertices_388, vertices_56, vertices_536, vertices_552, vertices_776, vertices_176, vertices_656, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_835), (false, vertices_149), (false, vertices_197), (false, vertices_617), (false, vertices_241), (true, vertices_262), (true, vertices_268), (true, vertices_788), (true, vertices_388), (true, vertices_536), (true, vertices_656), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 12 else
  if p.val = (false, vertices_835) then 13 else
  if p.val = (false, vertices_149) then 1 else
  if p.val = (false, vertices_197) then 2 else
  if p.val = (false, vertices_617) then 18 else
  if p.val = (false, vertices_241) then 20 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_788) then 16 else
  if p.val = (true, vertices_388) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_656) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_197), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_788), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 70 3
cert_row_2 1 1 3 7 8 788
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 796
cert_cover_5 2 1 1 2 3 7 28 796 3
cert_coverFacet 3 916
cert_cover_5 3 1 1 3 6 7 148 916 3
cert_coverFacet 4 696
cert_cover_5 4 2 2 3 4 6 56 696 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 224 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0379

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_one_six_0380.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0380

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 835, 213, 617, 241, 270, 454, 796, 660, 900, 696, 992, 7, 11, 67, 771, 21, 69, 41, 521, 49, 209, 97, 577, 14, 70, 262, 266, 322, 28, 268, 148, 532, 196, 388, 644, 772, 56, 536, 552, 776, 176, 656, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_835, vertices_213, vertices_617, vertices_241, vertices_270, vertices_454, vertices_796, vertices_660, vertices_900, vertices_696, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_771, vertices_21, vertices_69, vertices_41, vertices_521, vertices_49, vertices_209, vertices_97, vertices_577, vertices_14, vertices_70, vertices_262, vertices_266, vertices_322, vertices_28, vertices_268, vertices_148, vertices_532, vertices_196, vertices_388, vertices_644, vertices_772, vertices_56, vertices_536, vertices_552, vertices_776, vertices_176, vertices_656, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_835), (false, vertices_213), (false, vertices_617), (false, vertices_241), (true, vertices_262), (true, vertices_268), (true, vertices_532), (true, vertices_388), (true, vertices_644), (true, vertices_772), (true, vertices_536), (true, vertices_656), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 19 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_835) then 14 else
  if p.val = (false, vertices_213) then 20 else
  if p.val = (false, vertices_617) then 18 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_772) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_656) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 70 3
cert_row_4 1 1 2 3 7 8 796 28 3
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 796
cert_cover_5 2 1 1 2 3 7 28 796 3
cert_coverFacet 3 660
cert_cover_2 3 3 1 6 8 148 660 3
cert_coverFacet 4 900
cert_cover_2 4 6 1 7 8 388 900 3
cert_coverFacet 5 696
cert_cover_5 5 2 2 3 4 6 56 696 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0380

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_one_six_0381.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0381

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 835, 213, 617, 241, 270, 454, 796, 404, 696, 912, 992, 7, 11, 67, 771, 21, 69, 41, 521, 49, 209, 97, 577, 14, 70, 262, 266, 322, 28, 268, 148, 276, 196, 388, 56, 536, 552, 776, 176, 400, 656, 784, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_835, vertices_213, vertices_617, vertices_241, vertices_270, vertices_454, vertices_796, vertices_404, vertices_696, vertices_912, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_771, vertices_21, vertices_69, vertices_41, vertices_521, vertices_49, vertices_209, vertices_97, vertices_577, vertices_14, vertices_70, vertices_262, vertices_266, vertices_322, vertices_28, vertices_268, vertices_148, vertices_276, vertices_196, vertices_388, vertices_56, vertices_536, vertices_552, vertices_776, vertices_176, vertices_400, vertices_656, vertices_784, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_835), (false, vertices_213), (false, vertices_617), (false, vertices_241), (true, vertices_262), (true, vertices_268), (true, vertices_276), (true, vertices_388), (true, vertices_536), (true, vertices_400), (true, vertices_656), (true, vertices_784), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 19 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_835) then 14 else
  if p.val = (false, vertices_213) then 20 else
  if p.val = (false, vertices_617) then 18 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_400) then 6 else
  if p.val = (true, vertices_656) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 70 3
cert_row_4 1 1 2 3 7 8 796 28 3
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 796
cert_cover_5 2 1 1 2 3 7 28 796 3
cert_coverFacet 3 404
cert_cover_2 3 3 1 6 7 148 404 3
cert_coverFacet 4 696
cert_cover_5 4 2 2 3 4 6 56 696 3
cert_coverFacet 5 912
cert_cover_2 5 6 3 7 8 400 912 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0381

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_one_six_0382.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0382

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 835, 213, 617, 241, 270, 454, 284, 916, 696, 792, 992, 7, 11, 67, 771, 21, 69, 41, 521, 49, 209, 97, 577, 14, 70, 262, 266, 322, 28, 268, 148, 276, 196, 388, 56, 280, 536, 552, 776, 176, 656, 784, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_835, vertices_213, vertices_617, vertices_241, vertices_270, vertices_454, vertices_284, vertices_916, vertices_696, vertices_792, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_771, vertices_21, vertices_69, vertices_41, vertices_521, vertices_49, vertices_209, vertices_97, vertices_577, vertices_14, vertices_70, vertices_262, vertices_266, vertices_322, vertices_28, vertices_268, vertices_148, vertices_276, vertices_196, vertices_388, vertices_56, vertices_280, vertices_536, vertices_552, vertices_776, vertices_176, vertices_656, vertices_784, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_835), (false, vertices_213), (false, vertices_617), (false, vertices_241), (true, vertices_262), (true, vertices_268), (true, vertices_276), (true, vertices_388), (true, vertices_280), (true, vertices_536), (true, vertices_656), (true, vertices_784), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 19 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_835) then 14 else
  if p.val = (false, vertices_213) then 20 else
  if p.val = (false, vertices_617) then 18 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_656) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 70 3
cert_row_4 1 1 3 6 7 8 916 148 3
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 284
cert_cover_2 2 2 1 3 7 28 284 3
cert_coverFacet 3 916
cert_cover_5 3 1 1 3 6 7 148 916 3
cert_coverFacet 4 696
cert_cover_5 4 2 2 3 4 6 56 696 3
cert_coverFacet 5 792
cert_cover_2 5 3 2 7 8 280 792 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0382

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_one_six_0383.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0383

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 835, 213, 617, 241, 270, 454, 540, 780, 916, 696, 992, 7, 11, 67, 771, 21, 69, 41, 521, 49, 209, 97, 577, 14, 70, 262, 266, 322, 28, 268, 524, 148, 532, 196, 388, 772, 56, 536, 552, 776, 176, 656, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_835, vertices_213, vertices_617, vertices_241, vertices_270, vertices_454, vertices_540, vertices_780, vertices_916, vertices_696, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_771, vertices_21, vertices_69, vertices_41, vertices_521, vertices_49, vertices_209, vertices_97, vertices_577, vertices_14, vertices_70, vertices_262, vertices_266, vertices_322, vertices_28, vertices_268, vertices_524, vertices_148, vertices_532, vertices_196, vertices_388, vertices_772, vertices_56, vertices_536, vertices_552, vertices_776, vertices_176, vertices_656, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_835), (false, vertices_213), (false, vertices_617), (false, vertices_241), (true, vertices_262), (true, vertices_268), (true, vertices_524), (true, vertices_532), (true, vertices_388), (true, vertices_772), (true, vertices_536), (true, vertices_656), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 19 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_835) then 14 else
  if p.val = (false, vertices_213) then 20 else
  if p.val = (false, vertices_617) then 18 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_388) then 5 else
  if p.val = (true, vertices_772) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_656) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 70 3
cert_row_4 1 1 3 6 7 8 916 148 3
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 540
cert_cover_2 2 2 1 3 8 28 540 3
cert_coverFacet 3 780
cert_cover_2 3 2 1 7 8 268 780 3
cert_coverFacet 4 916
cert_cover_5 4 1 1 3 6 7 148 916 3
cert_coverFacet 5 696
cert_cover_5 5 2 2 3 4 6 56 696 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0383

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_one_six_0384.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0384

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 269, 325, 214, 538, 914, 620, 844, 244, 696, 992, 7, 11, 67, 259, 13, 69, 261, 265, 321, 22, 70, 26, 522, 146, 530, 194, 386, 770, 44, 588, 268, 52, 212, 100, 324, 56, 536, 552, 776, 176, 656, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_269, vertices_325, vertices_214, vertices_538, vertices_914, vertices_620, vertices_844, vertices_244, vertices_696, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_69, vertices_261, vertices_265, vertices_321, vertices_22, vertices_70, vertices_26, vertices_522, vertices_146, vertices_530, vertices_194, vertices_386, vertices_770, vertices_44, vertices_588, vertices_268, vertices_52, vertices_212, vertices_100, vertices_324, vertices_56, vertices_536, vertices_552, vertices_776, vertices_176, vertices_656, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_269), (false, vertices_325), (true, vertices_146), (true, vertices_530), (true, vertices_588), (true, vertices_212), (true, vertices_100), (true, vertices_536), (true, vertices_552), (true, vertices_176), (true, vertices_656), (true, vertices_224), (true, vertices_608), (true, vertices_672), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 21 18 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 19 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_451) then 17 else
  if p.val = (false, vertices_269) then 1 else
  if p.val = (false, vertices_325) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_588) then 20 else
  if p.val = (true, vertices_212) then 22 else
  if p.val = (true, vertices_100) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_608) then 11 else
  if p.val = (true, vertices_672) then 12 else
  if p.val = (true, vertices_832) then 13 else
  if p.val = (true, vertices_896) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_269), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_325), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_588), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(true, vertices_212), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
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
cert_coverFacet 4 844
cert_cover_5 4 3 1 2 5 7 588 844 3
cert_coverFacet 5 244
cert_cover_5 5 4 1 3 4 5 52 244 3
cert_coverFacet 6 696
cert_cover_5 6 2 2 3 4 6 56 696 3
cert_coverFacet 7 992
cert_cover_5 7 1 4 5 6 7 224 992 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 5 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0384

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_one_six_0385.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0385

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 333, 214, 538, 914, 812, 244, 868, 696, 736, 960, 7, 11, 67, 259, 13, 69, 265, 321, 22, 70, 26, 522, 146, 530, 194, 386, 770, 44, 268, 52, 212, 100, 804, 324, 56, 536, 552, 776, 176, 656, 224, 608, 672, 448, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_333, vertices_214, vertices_538, vertices_914, vertices_812, vertices_244, vertices_868, vertices_696, vertices_736, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_69, vertices_265, vertices_321, vertices_22, vertices_70, vertices_26, vertices_522, vertices_146, vertices_530, vertices_194, vertices_386, vertices_770, vertices_44, vertices_268, vertices_52, vertices_212, vertices_100, vertices_804, vertices_324, vertices_56, vertices_536, vertices_552, vertices_776, vertices_176, vertices_656, vertices_224, vertices_608, vertices_672, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_333), (true, vertices_146), (true, vertices_530), (true, vertices_212), (true, vertices_100), (true, vertices_804), (true, vertices_536), (true, vertices_552), (true, vertices_176), (true, vertices_656), (true, vertices_224), (true, vertices_608), (true, vertices_672), (true, vertices_704), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 22 17 20 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_451) then 16 else
  if p.val = (false, vertices_333) then 19 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_212) then 21 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_804) then 23 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_656) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_832) then 12 else
  if p.val = (true, vertices_896) then 13 else
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
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(true, vertices_212), by decide +kernel⟩
  | 22 => Sum.inl 1
  | 23 => Sum.inr ⟨(true, vertices_804), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 5 6 212
cert_row_2 1 1 4 7 8 804
cert_row_4 2 0 3 6 7 8 914 146 3
cert_row_4 3 2 3 4 6 8 696 56 3
cert_rows
cert_pivot_2 5 1 0 2
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 5 22 214 3
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 914
cert_cover_5 2 2 0 3 6 7 146 914 3
cert_coverFacet 3 812
cert_cover_5 3 1 1 2 4 7 44 812 3
cert_coverFacet 4 244
cert_cover_5 4 0 1 3 4 5 52 244 3
cert_coverFacet 5 868
cert_cover_5 5 1 1 4 5 7 100 868 3
cert_coverFacet 6 696
cert_cover_5 6 3 2 3 4 6 56 696 3
cert_coverFacet 7 736
cert_cover_2 7 5 4 6 8 224 736 3
cert_coverFacet 8 960
cert_cover_2 8 6 5 7 8 448 960 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0385

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_one_six_0386.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0386

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 333, 214, 538, 914, 556, 780, 244, 868, 696, 992, 7, 11, 67, 259, 13, 69, 265, 321, 22, 70, 26, 522, 146, 530, 194, 386, 770, 44, 268, 524, 52, 212, 100, 548, 324, 772, 56, 536, 552, 776, 176, 656, 224, 864, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_333, vertices_214, vertices_538, vertices_914, vertices_556, vertices_780, vertices_244, vertices_868, vertices_696, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_69, vertices_265, vertices_321, vertices_22, vertices_70, vertices_26, vertices_522, vertices_146, vertices_530, vertices_194, vertices_386, vertices_770, vertices_44, vertices_268, vertices_524, vertices_52, vertices_212, vertices_100, vertices_548, vertices_324, vertices_772, vertices_56, vertices_536, vertices_552, vertices_776, vertices_176, vertices_656, vertices_224, vertices_864, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_333), (true, vertices_146), (true, vertices_530), (true, vertices_524), (true, vertices_212), (true, vertices_100), (true, vertices_548), (true, vertices_772), (true, vertices_536), (true, vertices_552), (true, vertices_176), (true, vertices_656), (true, vertices_224), (true, vertices_864), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_451) then 16 else
  if p.val = (false, vertices_333) then 19 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_212) then 20 else
  if p.val = (true, vertices_100) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_772) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_864) then 24 else
  if p.val = (true, vertices_672) then 12 else
  if p.val = (true, vertices_896) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_212), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(true, vertices_864), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 5 6 212
cert_row_2 1 4 5 7 8 864
cert_row_4 2 0 3 6 7 8 914 146 3
cert_row_4 3 2 3 4 6 8 696 56 3
cert_rows
cert_pivot_2 1 5 0 2
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 5 22 214 3
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 914
cert_cover_5 2 2 0 3 6 7 146 914 3
cert_coverFacet 3 556
cert_cover_2 3 2 1 4 8 44 556 3
cert_coverFacet 4 780
cert_cover_2 4 2 1 7 8 268 780 3
cert_coverFacet 5 244
cert_cover_5 5 0 1 3 4 5 52 244 3
cert_coverFacet 6 868
cert_cover_5 6 1 1 4 5 7 100 868 3
cert_coverFacet 7 696
cert_cover_5 7 3 2 3 4 6 56 696 3
cert_coverFacet 8 992
cert_cover_5 8 1 4 5 6 7 224 992 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0386

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_one_six_0387.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0387

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 333, 150, 198, 666, 898, 364, 628, 724, 824, 992, 7, 11, 67, 259, 13, 69, 265, 321, 22, 70, 134, 26, 522, 146, 194, 386, 642, 770, 44, 332, 52, 596, 148, 100, 196, 56, 536, 296, 776, 560, 656, 352, 608, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_333, vertices_150, vertices_198, vertices_666, vertices_898, vertices_364, vertices_628, vertices_724, vertices_824, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_69, vertices_265, vertices_321, vertices_22, vertices_70, vertices_134, vertices_26, vertices_522, vertices_146, vertices_194, vertices_386, vertices_642, vertices_770, vertices_44, vertices_332, vertices_52, vertices_596, vertices_148, vertices_100, vertices_196, vertices_56, vertices_536, vertices_296, vertices_776, vertices_560, vertices_656, vertices_352, vertices_608, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_333), (true, vertices_134), (true, vertices_146), (true, vertices_642), (true, vertices_596), (true, vertices_148), (true, vertices_100), (true, vertices_196), (true, vertices_536), (true, vertices_296), (true, vertices_560), (true, vertices_656), (true, vertices_352), (true, vertices_608), (true, vertices_800), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 23 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 20 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_451) then 18 else
  if p.val = (false, vertices_333) then 21 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_596) then 22 else
  if p.val = (true, vertices_148) then 4 else
  if p.val = (true, vertices_100) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_800) then 13 else
  if p.val = (true, vertices_704) then 14 else
  if p.val = (true, vertices_896) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_596), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 8 666 26 3
cert_row_4 1 4 5 6 7 8 992 352 2
cert_row_4 2 2 3 4 7 8 824 56 3
cert_row_2 3 1 3 5 8 596
cert_row_2 4 1 2 5 7 332
cert_rows_2
cert_pivot 0 6 4 3 1
cert_heightProof 5
cert_coverFacet 0 150
cert_cover_2 0 1 0 3 6 22 150 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 666
cert_cover_5 2 0 0 2 3 6 26 666 3
cert_coverFacet 3 898
cert_cover_2 3 6 0 7 8 386 898 3
cert_coverFacet 4 364
cert_cover_5 4 4 1 2 4 5 44 364 3
cert_coverFacet 5 628
cert_cover_5 5 3 1 3 4 5 52 628 3
cert_coverFacet 6 724
cert_cover_5 6 3 1 3 5 6 596 724 3
cert_coverFacet 7 824
cert_cover_5 7 2 2 3 4 7 56 824 3
cert_coverFacet 8 992
cert_cover_5 8 1 4 5 6 7 352 992 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 5 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0387

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_one_six_0388.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0388

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 213, 665, 897, 334, 364, 692, 740, 824, 864, 960, 7, 11, 67, 259, 21, 69, 25, 521, 145, 193, 385, 641, 769, 14, 70, 266, 322, 44, 332, 52, 148, 100, 676, 196, 56, 536, 296, 776, 560, 656, 352, 608, 800, 448, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_213, vertices_665, vertices_897, vertices_334, vertices_364, vertices_692, vertices_740, vertices_824, vertices_864, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_25, vertices_521, vertices_145, vertices_193, vertices_385, vertices_641, vertices_769, vertices_14, vertices_70, vertices_266, vertices_322, vertices_44, vertices_332, vertices_52, vertices_148, vertices_100, vertices_676, vertices_196, vertices_56, vertices_536, vertices_296, vertices_776, vertices_560, vertices_656, vertices_352, vertices_608, vertices_800, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_213), (false, vertices_665), (false, vertices_897), (true, vertices_332), (true, vertices_100), (true, vertices_676), (true, vertices_296), (true, vertices_560), (true, vertices_352), (true, vertices_608), (true, vertices_800), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 17 13 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 11 else
  if p.val = (false, vertices_451) then 12 else
  if p.val = (false, vertices_213) then 18 else
  if p.val = (false, vertices_665) then 15 else
  if p.val = (false, vertices_897) then 1 else
  if p.val = (true, vertices_332) then 16 else
  if p.val = (true, vertices_100) then 2 else
  if p.val = (true, vertices_676) then 19 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_560) then 4 else
  if p.val = (true, vertices_352) then 5 else
  if p.val = (true, vertices_608) then 6 else
  if p.val = (true, vertices_800) then 7 else
  if p.val = (true, vertices_704) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_332), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_676), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
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
cert_coverFacet 6 960
cert_cover_2 6 6 5 7 8 448 960 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0388

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_one_six_0389.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0389

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 331, 533, 553, 841, 689, 78, 454, 220, 916, 248, 616, 992, 7, 11, 259, 21, 517, 41, 329, 521, 49, 529, 545, 769, 14, 70, 262, 74, 322, 28, 76, 148, 532, 196, 388, 772, 56, 216, 104, 552, 584, 176, 656, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_331, vertices_533, vertices_553, vertices_841, vertices_689, vertices_78, vertices_454, vertices_220, vertices_916, vertices_248, vertices_616, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_259, vertices_21, vertices_517, vertices_41, vertices_329, vertices_521, vertices_49, vertices_529, vertices_545, vertices_769, vertices_14, vertices_70, vertices_262, vertices_74, vertices_322, vertices_28, vertices_76, vertices_148, vertices_532, vertices_196, vertices_388, vertices_772, vertices_56, vertices_216, vertices_104, vertices_552, vertices_584, vertices_176, vertices_656, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_331), (false, vertices_533), (false, vertices_553), (false, vertices_841), (false, vertices_689), (true, vertices_70), (true, vertices_76), (true, vertices_148), (true, vertices_196), (true, vertices_388), (true, vertices_216), (true, vertices_104), (true, vertices_224), (true, vertices_608), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 19 16 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_775) then 13 else
  if p.val = (false, vertices_331) then 20 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_553) then 1 else
  if p.val = (false, vertices_841) then 21 else
  if p.val = (false, vertices_689) then 17 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_148) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_216) then 18 else
  if p.val = (true, vertices_104) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_448) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 5 6 216
cert_row_4 1 0 1 5 6 7 454 70 3
cert_row_4 2 1 3 6 7 8 916 148 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 2 0 1 4
cert_heightProof 4
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 454
cert_cover_5 1 1 0 1 5 6 70 454 3
cert_coverFacet 2 220
cert_cover_5 2 0 1 2 3 5 28 220 3
cert_coverFacet 3 916
cert_cover_5 3 2 1 3 6 7 148 916 3
cert_coverFacet 4 248
cert_cover_5 4 0 2 3 4 5 56 248 3
cert_coverFacet 5 616
cert_cover_2 5 4 2 5 8 104 616 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0389

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_one_six_0390.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0390

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 589, 833, 86, 410, 210, 812, 692, 724, 440, 992, 7, 11, 67, 259, 13, 69, 521, 321, 577, 769, 22, 70, 26, 266, 82, 146, 194, 386, 44, 524, 52, 84, 660, 548, 580, 56, 408, 296, 776, 176, 208, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_589, vertices_833, vertices_86, vertices_410, vertices_210, vertices_812, vertices_692, vertices_724, vertices_440, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_69, vertices_521, vertices_321, vertices_577, vertices_769, vertices_22, vertices_70, vertices_26, vertices_266, vertices_82, vertices_146, vertices_194, vertices_386, vertices_44, vertices_524, vertices_52, vertices_84, vertices_660, vertices_548, vertices_580, vertices_56, vertices_408, vertices_296, vertices_776, vertices_176, vertices_208, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_589), (false, vertices_833), (true, vertices_82), (true, vertices_146), (true, vertices_84), (true, vertices_660), (true, vertices_548), (true, vertices_408), (true, vertices_296), (true, vertices_176), (true, vertices_208), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_451) then 15 else
  if p.val = (false, vertices_589) then 18 else
  if p.val = (false, vertices_833) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_660) then 19 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_408) then 21 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_800) then 11 else
  if p.val = (true, vertices_704) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_833), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_660), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 4 5 6 7 8 992 416 1
cert_row_4 1 1 2 4 7 8 812 44 3
cert_row_2 2 2 3 6 7 408
cert_row_2 3 1 3 6 8 660
cert_rows
cert_pivot_2 5 4 2 1
cert_heightProof 4
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 410
cert_cover_5 1 2 0 2 3 6 26 410 3
cert_coverFacet 2 210
cert_cover_2 2 3 0 5 6 82 210 3
cert_coverFacet 3 812
cert_cover_5 3 1 1 2 4 7 44 812 3
cert_coverFacet 4 692
cert_cover_5 4 3 1 3 4 6 52 692 3
cert_coverFacet 5 724
cert_cover_5 5 3 1 3 5 6 84 724 3
cert_coverFacet 6 440
cert_cover_5 6 2 2 3 4 6 56 440 3
cert_coverFacet 7 992
cert_cover_5 7 0 4 5 6 7 416 992 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0390

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_one_six_0391.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0391

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 589, 833, 214, 410, 812, 628, 440, 752, 928, 960, 7, 11, 67, 259, 13, 69, 521, 321, 577, 769, 22, 70, 26, 266, 146, 194, 386, 44, 524, 52, 84, 548, 580, 56, 408, 296, 776, 624, 176, 208, 416, 672, 800, 448, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_589, vertices_833, vertices_214, vertices_410, vertices_812, vertices_628, vertices_440, vertices_752, vertices_928, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_69, vertices_521, vertices_321, vertices_577, vertices_769, vertices_22, vertices_70, vertices_26, vertices_266, vertices_146, vertices_194, vertices_386, vertices_44, vertices_524, vertices_52, vertices_84, vertices_548, vertices_580, vertices_56, vertices_408, vertices_296, vertices_776, vertices_624, vertices_176, vertices_208, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_589), (false, vertices_833), (true, vertices_146), (true, vertices_84), (true, vertices_548), (true, vertices_408), (true, vertices_296), (true, vertices_624), (true, vertices_176), (true, vertices_208), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_451) then 15 else
  if p.val = (false, vertices_589) then 18 else
  if p.val = (false, vertices_833) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_408) then 20 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_624) then 22 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_833), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(true, vertices_624), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 6 214 22 3
cert_row_2 1 2 3 6 7 408
cert_row_2 2 3 4 5 8 624
cert_row_4 3 1 2 4 7 8 812 44 3
cert_rows
cert_pivot_2 0 6 3 1
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 5 22 214 3
cert_coverFacet 1 410
cert_cover_5 1 1 0 2 3 6 26 410 3
cert_coverFacet 2 812
cert_cover_5 2 3 1 2 4 7 44 812 3
cert_coverFacet 3 628
cert_cover_5 3 2 1 3 4 5 52 628 3
cert_coverFacet 4 440
cert_cover_5 4 1 2 3 4 6 56 440 3
cert_coverFacet 5 752
cert_cover_5 5 2 3 4 5 6 624 752 3
cert_coverFacet 6 928
cert_cover_2 6 6 4 7 8 416 928 3
cert_coverFacet 7 960
cert_cover_2 7 6 5 7 8 448 960 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0391

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_one_six_0392.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0392

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 589, 833, 214, 410, 812, 564, 596, 440, 752, 992, 7, 11, 67, 259, 13, 69, 521, 321, 577, 769, 22, 70, 26, 266, 146, 194, 386, 44, 524, 52, 84, 532, 548, 580, 56, 408, 296, 776, 176, 560, 208, 592, 736, 416, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_589, vertices_833, vertices_214, vertices_410, vertices_812, vertices_564, vertices_596, vertices_440, vertices_752, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_69, vertices_521, vertices_321, vertices_577, vertices_769, vertices_22, vertices_70, vertices_26, vertices_266, vertices_146, vertices_194, vertices_386, vertices_44, vertices_524, vertices_52, vertices_84, vertices_532, vertices_548, vertices_580, vertices_56, vertices_408, vertices_296, vertices_776, vertices_176, vertices_560, vertices_208, vertices_592, vertices_736, vertices_416, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_589), (false, vertices_833), (true, vertices_146), (true, vertices_84), (true, vertices_532), (true, vertices_548), (true, vertices_408), (true, vertices_296), (true, vertices_176), (true, vertices_560), (true, vertices_208), (true, vertices_592), (true, vertices_736), (true, vertices_416), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_451) then 15 else
  if p.val = (false, vertices_589) then 18 else
  if p.val = (false, vertices_833) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_408) then 20 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_736) then 23 else
  if p.val = (true, vertices_416) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_833), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(true, vertices_736), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 6 214 22 3
cert_row_2 1 4 5 6 8 736
cert_row_2 2 2 3 6 7 408
cert_row_4 3 1 2 4 7 8 812 44 3
cert_rows
cert_pivot_2 0 5 3 1
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 5 22 214 3
cert_coverFacet 1 410
cert_cover_5 1 2 0 2 3 6 26 410 3
cert_coverFacet 2 812
cert_cover_5 2 3 1 2 4 7 44 812 3
cert_coverFacet 3 564
cert_cover_2 3 3 1 4 8 52 564 3
cert_coverFacet 4 596
cert_cover_2 4 3 1 5 8 84 596 3
cert_coverFacet 5 440
cert_cover_5 5 2 2 3 4 6 56 440 3
cert_coverFacet 6 752
cert_cover_5 6 1 3 4 5 6 176 752 2
cert_coverFacet 7 992
cert_cover_5 7 1 4 5 6 7 736 992 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0392

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_one_six_0393.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0393

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 779, 451, 589, 833, 406, 198, 282, 620, 244, 696, 920, 992, 7, 11, 67, 259, 13, 69, 521, 321, 577, 769, 22, 70, 134, 26, 266, 274, 194, 386, 44, 588, 52, 148, 100, 196, 56, 664, 280, 552, 776, 176, 400, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_779, vertices_451, vertices_589, vertices_833, vertices_406, vertices_198, vertices_282, vertices_620, vertices_244, vertices_696, vertices_920, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_69, vertices_521, vertices_321, vertices_577, vertices_769, vertices_22, vertices_70, vertices_134, vertices_26, vertices_266, vertices_274, vertices_194, vertices_386, vertices_44, vertices_588, vertices_52, vertices_148, vertices_100, vertices_196, vertices_56, vertices_664, vertices_280, vertices_552, vertices_776, vertices_176, vertices_400, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_779), (false, vertices_451), (false, vertices_589), (false, vertices_833), (true, vertices_134), (true, vertices_274), (true, vertices_148), (true, vertices_100), (true, vertices_196), (true, vertices_664), (true, vertices_280), (true, vertices_552), (true, vertices_176), (true, vertices_400), (true, vertices_224), (true, vertices_608), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 19 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_451) then 17 else
  if p.val = (false, vertices_589) then 20 else
  if p.val = (false, vertices_833) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_148) then 4 else
  if p.val = (true, vertices_100) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_664) then 22 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_672) then 13 else
  if p.val = (true, vertices_896) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_833), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(true, vertices_664), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 7 406 22 3
cert_row_4 1 4 5 6 7 8 992 224 3
cert_row_4 2 1 3 4 5 6 244 52 3
cert_row_2 3 2 3 6 8 664
cert_row_2 4 1 2 5 8 588
cert_rows_2
cert_pivot 0 7 4 3 1
cert_heightProof 5
cert_coverFacet 0 406
cert_cover_5 0 0 0 1 3 6 22 406 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 620
cert_cover_5 3 4 1 2 4 5 44 620 3
cert_coverFacet 4 244
cert_cover_5 4 2 1 3 4 5 52 244 3
cert_coverFacet 5 696
cert_cover_5 5 3 2 3 4 6 56 696 3
cert_coverFacet 6 920
cert_cover_5 6 3 2 3 6 7 664 920 3
cert_coverFacet 7 992
cert_cover_5 7 1 4 5 6 7 224 992 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 5 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0393

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_0930 : Certifies 930 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0358.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0931 : Certifies 931 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0359.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0932 : Certifies 932 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0360.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0933 : Certifies 933 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0361.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0934 : Certifies 934 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0362.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0935 : Certifies 935 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0363.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0936 : Certifies 936 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0364.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0937 : Certifies 937 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0365.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0938 : Certifies 938 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0366.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0939 : Certifies 939 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0371.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0940 : Certifies 940 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0374.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0941 : Certifies 941 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0375.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0942 : Certifies 942 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0376.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0943 : Certifies 943 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0377.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0944 : Certifies 944 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0378.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0945 : Certifies 945 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0379.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0946 : Certifies 946 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0380.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0947 : Certifies 947 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0381.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0948 : Certifies 948 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0382.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0949 : Certifies 949 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0383.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0950 : Certifies 950 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0384.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0951 : Certifies 951 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0385.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0952 : Certifies 952 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0386.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0953 : Certifies 953 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0387.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0954 : Certifies 954 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0388.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0955 : Certifies 955 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0389.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0956 : Certifies 956 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0390.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0957 : Certifies 957 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0391.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0958 : Certifies 958 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0392.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0959 : Certifies 959 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0393.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B031 (j : Fin 30) :
    Certifies (930 + j.val) := by
  fin_cases j
  · exact projection_0930
  · exact projection_0931
  · exact projection_0932
  · exact projection_0933
  · exact projection_0934
  · exact projection_0935
  · exact projection_0936
  · exact projection_0937
  · exact projection_0938
  · exact projection_0939
  · exact projection_0940
  · exact projection_0941
  · exact projection_0942
  · exact projection_0943
  · exact projection_0944
  · exact projection_0945
  · exact projection_0946
  · exact projection_0947
  · exact projection_0948
  · exact projection_0949
  · exact projection_0950
  · exact projection_0951
  · exact projection_0952
  · exact projection_0953
  · exact projection_0954
  · exact projection_0955
  · exact projection_0956
  · exact projection_0957
  · exact projection_0958
  · exact projection_0959

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
