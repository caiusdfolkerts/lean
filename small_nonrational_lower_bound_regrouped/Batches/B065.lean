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
/- Source: ProjectionCertificates/R_one_six_1815.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1815

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 341, 793, 841, 422, 454, 682, 820, 568, 712, 992, 7, 11, 67, 21, 69, 25, 73, 777, 273, 321, 38, 70, 390, 42, 138, 162, 194, 52, 276, 292, 324, 56, 536, 552, 200, 584, 648, 560, 784, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_341, vertices_793, vertices_841, vertices_422, vertices_454, vertices_682, vertices_820, vertices_568, vertices_712, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_25, vertices_73, vertices_777, vertices_273, vertices_321, vertices_38, vertices_70, vertices_390, vertices_42, vertices_138, vertices_162, vertices_194, vertices_52, vertices_276, vertices_292, vertices_324, vertices_56, vertices_536, vertices_552, vertices_200, vertices_584, vertices_648, vertices_560, vertices_784, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_341), (false, vertices_793), (false, vertices_841), (true, vertices_390), (true, vertices_162), (true, vertices_292), (true, vertices_552), (true, vertices_648), (true, vertices_560), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 12 else
  if p.val = (false, vertices_341) then 16 else
  if p.val = (false, vertices_793) then 18 else
  if p.val = (false, vertices_841) then 19 else
  if p.val = (true, vertices_390) then 13 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_648) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_416) then 6 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_704) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 8 682 42 3
cert_row_2 1 0 1 6 7 390
cert_row_4 2 1 3 4 7 8 820 52 3
cert_row_4 3 4 5 6 7 8 992 416 1
cert_rows
cert_pivot_2 2 0 1 4
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 1 0 1 4 6 38 422 3
cert_coverFacet 1 454
cert_cover_5 1 1 0 1 5 6 70 454 3
cert_coverFacet 2 682
cert_cover_5 2 0 0 2 4 6 42 682 3
cert_coverFacet 3 820
cert_cover_5 3 2 1 3 4 7 52 820 3
cert_coverFacet 4 568
cert_cover_2 4 3 2 4 8 56 568 3
cert_coverFacet 5 712
cert_cover_2 5 5 2 6 8 200 712 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 416 992 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1815

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_one_six_1816.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1816

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 613, 681, 961, 342, 346, 692, 916, 836, 440, 456, 7, 11, 67, 37, 69, 41, 137, 545, 193, 577, 641, 22, 70, 26, 74, 338, 52, 660, 276, 548, 324, 580, 772, 56, 280, 168, 200, 328, 392, 176, 400, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_613, vertices_681, vertices_961, vertices_342, vertices_346, vertices_692, vertices_916, vertices_836, vertices_440, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_37, vertices_69, vertices_41, vertices_137, vertices_545, vertices_193, vertices_577, vertices_641, vertices_22, vertices_70, vertices_26, vertices_74, vertices_338, vertices_52, vertices_660, vertices_276, vertices_548, vertices_324, vertices_580, vertices_772, vertices_56, vertices_280, vertices_168, vertices_200, vertices_328, vertices_392, vertices_176, vertices_400, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_613), (false, vertices_681), (false, vertices_961), (true, vertices_338), (true, vertices_660), (true, vertices_276), (true, vertices_324), (true, vertices_772), (true, vertices_280), (true, vertices_328), (true, vertices_392), (true, vertices_176), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 16 18 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 10 else
  if p.val = (false, vertices_613) then 14 else
  if p.val = (false, vertices_681) then 17 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_338) then 11 else
  if p.val = (true, vertices_660) then 15 else
  if p.val = (true, vertices_276) then 1 else
  if p.val = (true, vertices_324) then 2 else
  if p.val = (true, vertices_772) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_400) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_338), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_660), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
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
cert_row_2 0 0 3 5 7 338
cert_row_2 1 1 3 6 8 660
cert_row_4 2 2 3 4 6 7 440 56 3
cert_rows_3
cert_pivot_3 1 0 2
cert_heightProof 3
cert_coverFacet 0 342
cert_cover_5 0 0 0 1 3 5 22 342 3
cert_coverFacet 1 346
cert_cover_5 1 0 0 2 3 5 26 346 3
cert_coverFacet 2 692
cert_cover_5 2 1 1 3 4 6 52 692 3
cert_coverFacet 3 916
cert_cover_5 3 1 1 3 6 7 660 916 3
cert_coverFacet 4 836
cert_cover_2 4 5 1 7 8 324 836 3
cert_coverFacet 5 440
cert_cover_5 5 2 2 3 4 6 56 440 3
cert_coverFacet 6 456
cert_cover_2 6 5 2 6 7 200 456 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1816

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_one_six_1817.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1817

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 549, 837, 169, 737, 342, 346, 692, 916, 440, 968, 7, 11, 67, 37, 69, 517, 41, 137, 161, 545, 193, 577, 22, 70, 26, 74, 338, 52, 660, 276, 548, 324, 772, 56, 280, 168, 200, 328, 392, 176, 400, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_549, vertices_837, vertices_169, vertices_737, vertices_342, vertices_346, vertices_692, vertices_916, vertices_440, vertices_968] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_37, vertices_69, vertices_517, vertices_41, vertices_137, vertices_161, vertices_545, vertices_193, vertices_577, vertices_22, vertices_70, vertices_26, vertices_74, vertices_338, vertices_52, vertices_660, vertices_276, vertices_548, vertices_324, vertices_772, vertices_56, vertices_280, vertices_168, vertices_200, vertices_328, vertices_392, vertices_176, vertices_400, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_549), (false, vertices_837), (false, vertices_169), (false, vertices_737), (true, vertices_338), (true, vertices_660), (true, vertices_276), (true, vertices_280), (true, vertices_328), (true, vertices_392), (true, vertices_176), (true, vertices_400), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 17 18 19 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 11 else
  if p.val = (false, vertices_549) then 1 else
  if p.val = (false, vertices_837) then 15 else
  if p.val = (false, vertices_169) then 2 else
  if p.val = (false, vertices_737) then 20 else
  if p.val = (true, vertices_338) then 12 else
  if p.val = (true, vertices_660) then 16 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_549), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_169), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_338), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_660), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 5 7 338
cert_row_2 1 1 3 6 8 660
cert_row_4 2 2 3 4 6 7 440 56 3
cert_row_4 3 2 5 6 7 8 968 200 3
cert_rows
cert_pivot_2 0 1 3 2
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 0 0 1 3 5 22 342 3
cert_coverFacet 1 346
cert_cover_5 1 0 0 2 3 5 26 346 3
cert_coverFacet 2 692
cert_cover_5 2 1 1 3 4 6 52 692 3
cert_coverFacet 3 916
cert_cover_5 3 1 1 3 6 7 660 916 3
cert_coverFacet 4 440
cert_cover_5 4 2 2 3 4 6 56 440 3
cert_coverFacet 5 968
cert_cover_5 5 3 2 5 6 7 200 968 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1817

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_one_six_1818.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1818

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 533, 837, 601, 358, 170, 482, 436, 916, 696, 968, 7, 11, 67, 21, 69, 517, 25, 73, 529, 577, 38, 70, 42, 138, 354, 162, 194, 52, 404, 532, 292, 324, 772, 56, 536, 168, 200, 584, 648, 176, 656, 416, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_533, vertices_837, vertices_601, vertices_358, vertices_170, vertices_482, vertices_436, vertices_916, vertices_696, vertices_968] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_517, vertices_25, vertices_73, vertices_529, vertices_577, vertices_38, vertices_70, vertices_42, vertices_138, vertices_354, vertices_162, vertices_194, vertices_52, vertices_404, vertices_532, vertices_292, vertices_324, vertices_772, vertices_56, vertices_536, vertices_168, vertices_200, vertices_584, vertices_648, vertices_176, vertices_656, vertices_416, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_533), (false, vertices_837), (false, vertices_601), (true, vertices_354), (true, vertices_162), (true, vertices_404), (true, vertices_292), (true, vertices_168), (true, vertices_648), (true, vertices_176), (true, vertices_656), (true, vertices_416), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 18 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 12 else
  if p.val = (false, vertices_533) then 1 else
  if p.val = (false, vertices_837) then 16 else
  if p.val = (false, vertices_601) then 19 else
  if p.val = (true, vertices_354) then 13 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_404) then 17 else
  if p.val = (true, vertices_292) then 3 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_176) then 6 else
  if p.val = (true, vertices_656) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_354), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_404), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 4 5 7 354
cert_row_2 1 1 3 6 7 404
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 2 5 6 7 8 968 200 3
cert_rows
cert_pivot_2 0 1 3 2
cert_heightProof 4
cert_coverFacet 0 358
cert_cover_5 0 0 0 1 4 5 38 358 3
cert_coverFacet 1 170
cert_cover_2 1 2 0 4 6 42 170 3
cert_coverFacet 2 482
cert_cover_5 2 0 0 4 5 6 354 482 3
cert_coverFacet 3 436
cert_cover_5 3 1 1 3 4 6 52 436 3
cert_coverFacet 4 916
cert_cover_5 4 1 1 3 6 8 404 916 3
cert_coverFacet 5 696
cert_cover_5 5 2 2 3 4 6 56 696 3
cert_coverFacet 6 968
cert_cover_5 6 3 2 5 6 7 200 968 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1818

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_one_six_1819.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1819

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 357, 425, 961, 534, 838, 602, 436, 916, 184, 728, 7, 11, 67, 37, 69, 41, 137, 289, 193, 321, 385, 22, 70, 518, 26, 74, 530, 578, 52, 404, 532, 292, 324, 772, 56, 600, 152, 168, 200, 176, 656, 416, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_357, vertices_425, vertices_961, vertices_534, vertices_838, vertices_602, vertices_436, vertices_916, vertices_184, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_37, vertices_69, vertices_41, vertices_137, vertices_289, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_518, vertices_26, vertices_74, vertices_530, vertices_578, vertices_52, vertices_404, vertices_532, vertices_292, vertices_324, vertices_772, vertices_56, vertices_600, vertices_152, vertices_168, vertices_200, vertices_176, vertices_656, vertices_416, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_357), (false, vertices_425), (false, vertices_961), (true, vertices_518), (true, vertices_530), (true, vertices_578), (true, vertices_404), (true, vertices_532), (true, vertices_772), (true, vertices_600), (true, vertices_152), (true, vertices_176), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 11 15 18 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 10 else
  if p.val = (false, vertices_357) then 13 else
  if p.val = (false, vertices_425) then 16 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_404) then 14 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_600) then 17 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_656) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_404), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_600), by decide +kernel⟩
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
cert_row_2 0 2 3 5 8 600
cert_row_2 1 1 3 6 7 404
cert_row_4 2 0 1 5 7 8 838 70 3
cert_rows_3
cert_pivot_3 3 2 0
cert_heightProof 3
cert_coverFacet 0 534
cert_cover_2 0 1 0 3 8 22 534 3
cert_coverFacet 1 838
cert_cover_5 1 2 0 1 5 7 70 838 3
cert_coverFacet 2 602
cert_cover_5 2 0 0 2 3 5 26 602 3
cert_coverFacet 3 436
cert_cover_5 3 1 1 3 4 6 52 436 3
cert_coverFacet 4 916
cert_cover_5 4 1 1 3 6 8 404 916 3
cert_coverFacet 5 184
cert_cover_2 5 3 2 4 6 56 184 3
cert_coverFacet 6 728
cert_cover_5 6 0 2 3 5 6 600 728 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1819

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_one_six_1820.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1820

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 357, 425, 961, 534, 838, 602, 692, 932, 184, 728, 7, 11, 67, 37, 69, 41, 137, 289, 193, 321, 385, 22, 70, 518, 26, 74, 530, 578, 52, 532, 676, 292, 324, 772, 56, 600, 152, 168, 200, 176, 656, 416, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_357, vertices_425, vertices_961, vertices_534, vertices_838, vertices_602, vertices_692, vertices_932, vertices_184, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_37, vertices_69, vertices_41, vertices_137, vertices_289, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_518, vertices_26, vertices_74, vertices_530, vertices_578, vertices_52, vertices_532, vertices_676, vertices_292, vertices_324, vertices_772, vertices_56, vertices_600, vertices_152, vertices_168, vertices_200, vertices_176, vertices_656, vertices_416, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_357), (false, vertices_425), (false, vertices_961), (true, vertices_518), (true, vertices_530), (true, vertices_578), (true, vertices_532), (true, vertices_676), (true, vertices_772), (true, vertices_600), (true, vertices_152), (true, vertices_176), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 15 11 18 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 10 else
  if p.val = (false, vertices_357) then 16 else
  if p.val = (false, vertices_425) then 13 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_676) then 17 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_600) then 14 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_656) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 11 => Sum.inl 2
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_600), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_676), by decide +kernel⟩
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
cert_row_2 0 2 3 5 8 600
cert_row_2 1 1 4 6 8 676
cert_row_4 2 0 1 5 7 8 838 70 3
cert_rows_3
cert_pivot_3 4 2 0
cert_heightProof 3
cert_coverFacet 0 534
cert_cover_2 0 1 0 3 8 22 534 3
cert_coverFacet 1 838
cert_cover_5 1 2 0 1 5 7 70 838 3
cert_coverFacet 2 602
cert_cover_5 2 0 0 2 3 5 26 602 3
cert_coverFacet 3 692
cert_cover_5 3 1 1 3 4 6 52 692 3
cert_coverFacet 4 932
cert_cover_5 4 1 1 4 6 7 676 932 3
cert_coverFacet 5 184
cert_cover_2 5 3 2 4 6 56 184 3
cert_coverFacet 6 728
cert_cover_5 6 0 2 3 5 6 600 728 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1820

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_one_six_1821.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1821

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 357, 425, 961, 534, 838, 602, 820, 184, 728, 944, 7, 11, 67, 37, 69, 41, 137, 289, 193, 321, 385, 22, 70, 518, 26, 74, 530, 578, 52, 532, 292, 324, 772, 56, 600, 152, 168, 200, 176, 816, 656, 416, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_357, vertices_425, vertices_961, vertices_534, vertices_838, vertices_602, vertices_820, vertices_184, vertices_728, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_37, vertices_69, vertices_41, vertices_137, vertices_289, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_518, vertices_26, vertices_74, vertices_530, vertices_578, vertices_52, vertices_532, vertices_292, vertices_324, vertices_772, vertices_56, vertices_600, vertices_152, vertices_168, vertices_200, vertices_176, vertices_816, vertices_656, vertices_416, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_357), (false, vertices_425), (false, vertices_961), (true, vertices_518), (true, vertices_530), (true, vertices_578), (true, vertices_532), (true, vertices_772), (true, vertices_600), (true, vertices_152), (true, vertices_176), (true, vertices_816), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 11 14 17 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 10 else
  if p.val = (false, vertices_357) then 13 else
  if p.val = (false, vertices_425) then 15 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_600) then 16 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_816) then 18 else
  if p.val = (true, vertices_656) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_600), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 5 8 600
cert_row_2 1 3 4 7 8 816
cert_row_4 2 0 1 5 7 8 838 70 3
cert_rows_3
cert_pivot_3 3 2 0
cert_heightProof 3
cert_coverFacet 0 534
cert_cover_2 0 1 0 3 8 22 534 3
cert_coverFacet 1 838
cert_cover_5 1 2 0 1 5 7 70 838 3
cert_coverFacet 2 602
cert_cover_5 2 0 0 2 3 5 26 602 3
cert_coverFacet 3 820
cert_cover_5 3 1 1 3 4 7 52 820 3
cert_coverFacet 4 184
cert_cover_2 4 3 2 4 6 56 184 3
cert_coverFacet 5 728
cert_cover_5 5 0 2 3 5 6 600 728 3
cert_coverFacet 6 944
cert_cover_5 6 1 3 4 6 7 176 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1821

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_one_six_1822.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1822

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 357, 425, 961, 534, 838, 602, 820, 440, 728, 912, 7, 11, 67, 37, 69, 41, 137, 289, 193, 321, 385, 22, 70, 518, 26, 74, 530, 578, 52, 532, 292, 324, 772, 56, 600, 152, 424, 200, 304, 400, 656, 784, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_357, vertices_425, vertices_961, vertices_534, vertices_838, vertices_602, vertices_820, vertices_440, vertices_728, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_37, vertices_69, vertices_41, vertices_137, vertices_289, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_518, vertices_26, vertices_74, vertices_530, vertices_578, vertices_52, vertices_532, vertices_292, vertices_324, vertices_772, vertices_56, vertices_600, vertices_152, vertices_424, vertices_200, vertices_304, vertices_400, vertices_656, vertices_784, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_357), (false, vertices_425), (false, vertices_961), (true, vertices_518), (true, vertices_530), (true, vertices_578), (true, vertices_532), (true, vertices_772), (true, vertices_600), (true, vertices_152), (true, vertices_304), (true, vertices_400), (true, vertices_656), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 19 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 12 else
  if p.val = (false, vertices_357) then 15 else
  if p.val = (false, vertices_425) then 17 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_600) then 18 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_784) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_600), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 4 6 7 424
cert_row_2 1 2 3 5 8 600
cert_row_4 2 0 1 5 7 8 838 70 3
cert_row_4 3 1 3 4 7 8 820 52 3
cert_rows
cert_pivot_2 6 2 0 1
cert_heightProof 4
cert_coverFacet 0 534
cert_cover_2 0 1 0 3 8 22 534 3
cert_coverFacet 1 838
cert_cover_5 1 2 0 1 5 7 70 838 3
cert_coverFacet 2 602
cert_cover_5 2 1 0 2 3 5 26 602 3
cert_coverFacet 3 820
cert_cover_5 3 3 1 3 4 7 52 820 3
cert_coverFacet 4 440
cert_cover_5 4 0 2 3 4 6 56 440 3
cert_coverFacet 5 728
cert_cover_5 5 1 2 3 5 6 600 728 3
cert_coverFacet 6 912
cert_cover_2 6 6 3 7 8 400 912 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1822

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_one_six_1823.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1823

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 789, 837, 601, 358, 426, 962, 308, 696, 712, 944, 7, 11, 67, 21, 69, 773, 25, 73, 529, 577, 38, 70, 42, 138, 290, 194, 322, 386, 52, 276, 292, 324, 56, 536, 168, 200, 584, 648, 688, 304, 784, 416, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_789, vertices_837, vertices_601, vertices_358, vertices_426, vertices_962, vertices_308, vertices_696, vertices_712, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_773, vertices_25, vertices_73, vertices_529, vertices_577, vertices_38, vertices_70, vertices_42, vertices_138, vertices_290, vertices_194, vertices_322, vertices_386, vertices_52, vertices_276, vertices_292, vertices_324, vertices_56, vertices_536, vertices_168, vertices_200, vertices_584, vertices_648, vertices_688, vertices_304, vertices_784, vertices_416, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_789), (false, vertices_837), (false, vertices_601), (true, vertices_290), (true, vertices_322), (true, vertices_386), (true, vertices_292), (true, vertices_168), (true, vertices_648), (true, vertices_688), (true, vertices_304), (true, vertices_416), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 12 else
  if p.val = (false, vertices_789) then 15 else
  if p.val = (false, vertices_837) then 16 else
  if p.val = (false, vertices_601) then 18 else
  if p.val = (true, vertices_290) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_688) then 20 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 19 => Sum.inl 3
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
cert_row_4 1 0 1 4 5 7 358 38 3
cert_row_4 2 0 2 4 6 7 426 42 3
cert_row_4 3 0 5 6 7 8 962 194 3
cert_rows
cert_pivot_2 3 1 2 0
cert_heightProof 4
cert_coverFacet 0 358
cert_cover_5 0 1 0 1 4 5 38 358 3
cert_coverFacet 1 426
cert_cover_5 1 2 0 2 4 6 42 426 3
cert_coverFacet 2 962
cert_cover_5 2 3 0 5 6 7 194 962 3
cert_coverFacet 3 308
cert_cover_2 3 3 1 4 7 52 308 3
cert_coverFacet 4 696
cert_cover_5 4 0 2 3 4 6 56 696 3
cert_coverFacet 5 712
cert_cover_2 5 5 2 6 8 200 712 3
cert_coverFacet 6 944
cert_cover_5 6 0 3 4 6 7 688 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1823

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_one_six_1824.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1824

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 789, 837, 601, 422, 454, 682, 308, 824, 712, 992, 7, 11, 67, 21, 69, 773, 25, 73, 529, 577, 38, 70, 390, 42, 138, 162, 194, 52, 276, 292, 324, 56, 536, 552, 200, 584, 648, 304, 784, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_789, vertices_837, vertices_601, vertices_422, vertices_454, vertices_682, vertices_308, vertices_824, vertices_712, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_773, vertices_25, vertices_73, vertices_529, vertices_577, vertices_38, vertices_70, vertices_390, vertices_42, vertices_138, vertices_162, vertices_194, vertices_52, vertices_276, vertices_292, vertices_324, vertices_56, vertices_536, vertices_552, vertices_200, vertices_584, vertices_648, vertices_304, vertices_784, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_789), (false, vertices_837), (false, vertices_601), (true, vertices_390), (true, vertices_162), (true, vertices_292), (true, vertices_552), (true, vertices_648), (true, vertices_304), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 18 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 12 else
  if p.val = (false, vertices_789) then 16 else
  if p.val = (false, vertices_837) then 17 else
  if p.val = (false, vertices_601) then 19 else
  if p.val = (true, vertices_390) then 13 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_648) then 4 else
  if p.val = (true, vertices_304) then 5 else
  if p.val = (true, vertices_416) then 6 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_704) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 7 390
cert_row_4 1 0 2 4 6 8 682 42 3
cert_row_4 2 2 3 4 7 8 824 56 3
cert_row_4 3 4 5 6 7 8 992 416 1
cert_rows
cert_pivot_2 1 0 2 4
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 0 0 1 4 6 38 422 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 682
cert_cover_5 2 1 0 2 4 6 42 682 3
cert_coverFacet 3 308
cert_cover_2 3 3 1 4 7 52 308 3
cert_coverFacet 4 824
cert_cover_5 4 2 2 3 4 7 56 824 3
cert_coverFacet 5 712
cert_cover_2 5 5 2 6 8 200 712 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 416 992 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1824

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_one_six_1825.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1825

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 789, 837, 601, 230, 682, 436, 452, 568, 968, 944, 7, 11, 67, 21, 69, 773, 25, 73, 529, 577, 38, 70, 42, 138, 162, 194, 52, 276, 164, 196, 324, 388, 56, 536, 552, 200, 584, 648, 432, 560, 784, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_789, vertices_837, vertices_601, vertices_230, vertices_682, vertices_436, vertices_452, vertices_568, vertices_968, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_773, vertices_25, vertices_73, vertices_529, vertices_577, vertices_38, vertices_70, vertices_42, vertices_138, vertices_162, vertices_194, vertices_52, vertices_276, vertices_164, vertices_196, vertices_324, vertices_388, vertices_56, vertices_536, vertices_552, vertices_200, vertices_584, vertices_648, vertices_432, vertices_560, vertices_784, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_789), (false, vertices_837), (false, vertices_601), (true, vertices_162), (true, vertices_164), (true, vertices_196), (true, vertices_388), (true, vertices_552), (true, vertices_648), (true, vertices_432), (true, vertices_560), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 12 else
  if p.val = (false, vertices_789) then 15 else
  if p.val = (false, vertices_837) then 16 else
  if p.val = (false, vertices_601) then 18 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_196) then 3 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_432) then 20 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(true, vertices_432), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 6 7 432
cert_row_4 1 0 1 4 5 6 230 38 3
cert_row_4 2 0 2 4 6 8 682 42 3
cert_row_4 3 2 5 6 7 8 968 200 3
cert_rows
cert_pivot_2 3 1 0 2
cert_heightProof 4
cert_coverFacet 0 230
cert_cover_5 0 1 0 1 4 5 38 230 3
cert_coverFacet 1 682
cert_cover_5 1 2 0 2 4 6 42 682 3
cert_coverFacet 2 436
cert_cover_5 2 0 1 3 4 6 52 436 3
cert_coverFacet 3 452
cert_cover_2 3 5 1 6 7 196 452 3
cert_coverFacet 4 568
cert_cover_2 4 3 2 4 8 56 568 3
cert_coverFacet 5 968
cert_cover_5 5 3 2 5 6 7 200 968 3
cert_coverFacet 6 944
cert_cover_5 6 0 3 4 6 8 432 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1825

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_one_six_1826.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1826

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 661, 709, 409, 358, 426, 450, 564, 868, 824, 976, 7, 11, 67, 21, 69, 645, 25, 137, 145, 193, 38, 70, 42, 138, 290, 194, 322, 386, 52, 532, 356, 548, 580, 56, 280, 296, 392, 560, 400, 656, 784, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_661, vertices_709, vertices_409, vertices_358, vertices_426, vertices_450, vertices_564, vertices_868, vertices_824, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_645, vertices_25, vertices_137, vertices_145, vertices_193, vertices_38, vertices_70, vertices_42, vertices_138, vertices_290, vertices_194, vertices_322, vertices_386, vertices_52, vertices_532, vertices_356, vertices_548, vertices_580, vertices_56, vertices_280, vertices_296, vertices_392, vertices_560, vertices_400, vertices_656, vertices_784, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_661), (false, vertices_709), (false, vertices_409), (true, vertices_290), (true, vertices_322), (true, vertices_386), (true, vertices_356), (true, vertices_548), (true, vertices_296), (true, vertices_560), (true, vertices_784), (true, vertices_800), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 16 13 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 12 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_709) then 18 else
  if p.val = (false, vertices_409) then 15 else
  if p.val = (true, vertices_290) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_356) then 19 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_356), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 5 7 356
cert_row_4 1 0 2 4 6 7 426 42 3
cert_row_4 2 2 3 4 7 8 824 56 3
cert_row_4 3 3 5 6 7 8 976 400 1
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 358
cert_cover_5 0 0 0 1 4 5 38 358 3
cert_coverFacet 1 426
cert_cover_5 1 1 0 2 4 6 42 426 3
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
cert_coverFacet 3 564
cert_cover_2 3 3 1 4 8 52 564 3
cert_coverFacet 4 868
cert_cover_5 4 0 1 4 5 8 356 868 3
cert_coverFacet 5 824
cert_cover_5 5 2 2 3 4 7 56 824 3
cert_coverFacet 6 976
cert_cover_5 6 3 3 5 6 7 400 976 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1826

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_one_six_1827.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1827

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 357, 425, 961, 214, 410, 564, 724, 868, 824, 912, 7, 11, 67, 37, 69, 41, 137, 289, 193, 321, 385, 22, 70, 26, 138, 146, 194, 52, 212, 532, 356, 548, 580, 56, 280, 296, 392, 560, 400, 656, 784, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_357, vertices_425, vertices_961, vertices_214, vertices_410, vertices_564, vertices_724, vertices_868, vertices_824, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_37, vertices_69, vertices_41, vertices_137, vertices_289, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_138, vertices_146, vertices_194, vertices_52, vertices_212, vertices_532, vertices_356, vertices_548, vertices_580, vertices_56, vertices_280, vertices_296, vertices_392, vertices_560, vertices_400, vertices_656, vertices_784, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_357), (false, vertices_425), (false, vertices_961), (true, vertices_146), (true, vertices_212), (true, vertices_532), (true, vertices_548), (true, vertices_580), (true, vertices_280), (true, vertices_560), (true, vertices_400), (true, vertices_656), (true, vertices_784), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 17 19 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 12 else
  if p.val = (false, vertices_357) then 15 else
  if p.val = (false, vertices_425) then 18 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_212) then 16 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_580) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_400) then 7 else
  if p.val = (true, vertices_656) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_212), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 7 410 26 3
cert_row_2 1 1 3 5 6 212
cert_row_2 2 1 4 5 7 356
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 1 0 1 3 5 22 214 3
cert_coverFacet 1 410
cert_cover_5 1 0 0 2 3 6 26 410 3
cert_coverFacet 2 564
cert_cover_2 2 3 1 4 8 52 564 3
cert_coverFacet 3 724
cert_cover_5 3 1 1 3 5 8 212 724 3
cert_coverFacet 4 868
cert_cover_5 4 2 1 4 5 8 356 868 3
cert_coverFacet 5 824
cert_cover_5 5 3 2 3 4 7 56 824 3
cert_coverFacet 6 912
cert_cover_2 6 6 3 7 8 400 912 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1827

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_one_six_1828.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1828

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 597, 409, 721, 358, 426, 962, 564, 868, 824, 912, 7, 11, 67, 21, 69, 25, 137, 593, 145, 193, 38, 70, 42, 138, 290, 194, 322, 386, 52, 532, 356, 548, 580, 56, 280, 296, 392, 560, 400, 656, 784, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_597, vertices_409, vertices_721, vertices_358, vertices_426, vertices_962, vertices_564, vertices_868, vertices_824, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_25, vertices_137, vertices_593, vertices_145, vertices_193, vertices_38, vertices_70, vertices_42, vertices_138, vertices_290, vertices_194, vertices_322, vertices_386, vertices_52, vertices_532, vertices_356, vertices_548, vertices_580, vertices_56, vertices_280, vertices_296, vertices_392, vertices_560, vertices_400, vertices_656, vertices_784, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_597), (false, vertices_409), (false, vertices_721), (true, vertices_290), (true, vertices_322), (true, vertices_386), (true, vertices_356), (true, vertices_548), (true, vertices_296), (true, vertices_560), (true, vertices_784), (true, vertices_800), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 12 else
  if p.val = (false, vertices_597) then 19 else
  if p.val = (false, vertices_409) then 17 else
  if p.val = (false, vertices_721) then 20 else
  if p.val = (true, vertices_290) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_356) then 15 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_832) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_356), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 5 7 356
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 0 2 4 6 7 426 42 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 1 5 0 2
cert_heightProof 4
cert_coverFacet 0 358
cert_cover_5 0 0 0 1 4 5 38 358 3
cert_coverFacet 1 426
cert_cover_5 1 2 0 2 4 6 42 426 3
cert_coverFacet 2 962
cert_cover_5 2 1 0 5 6 7 194 962 3
cert_coverFacet 3 564
cert_cover_2 3 3 1 4 8 52 564 3
cert_coverFacet 4 868
cert_cover_5 4 0 1 4 5 8 356 868 3
cert_coverFacet 5 824
cert_cover_5 5 3 2 3 4 7 56 824 3
cert_coverFacet 6 912
cert_cover_2 6 6 3 7 8 400 912 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1828

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_one_six_1829.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1829

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 213, 409, 614, 426, 866, 450, 564, 916, 964, 824, 7, 11, 67, 21, 69, 25, 137, 145, 193, 38, 70, 42, 138, 610, 290, 194, 322, 386, 52, 148, 532, 548, 196, 580, 900, 56, 280, 296, 392, 560, 400, 784, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_213, vertices_409, vertices_614, vertices_426, vertices_866, vertices_450, vertices_564, vertices_916, vertices_964, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_25, vertices_137, vertices_145, vertices_193, vertices_38, vertices_70, vertices_42, vertices_138, vertices_610, vertices_290, vertices_194, vertices_322, vertices_386, vertices_52, vertices_148, vertices_532, vertices_548, vertices_196, vertices_580, vertices_900, vertices_56, vertices_280, vertices_296, vertices_392, vertices_560, vertices_400, vertices_784, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_213), (false, vertices_409), (true, vertices_610), (true, vertices_290), (true, vertices_322), (true, vertices_386), (true, vertices_532), (true, vertices_548), (true, vertices_580), (true, vertices_900), (true, vertices_296), (true, vertices_560), (true, vertices_784), (true, vertices_800), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_213) then 18 else
  if p.val = (false, vertices_409) then 21 else
  if p.val = (true, vertices_610) then 15 else
  if p.val = (true, vertices_290) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_580) then 6 else
  if p.val = (true, vertices_900) then 19 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_448) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_610), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_900), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 6 7 8 900
cert_row_2 1 0 4 5 8 610
cert_row_4 2 0 2 4 6 7 426 42 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 1 5 0 2
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_5 0 1 0 1 4 5 38 614 3
cert_coverFacet 1 426
cert_cover_5 1 2 0 2 4 6 42 426 3
cert_coverFacet 2 866
cert_cover_5 2 1 0 4 5 7 610 866 3
cert_coverFacet 3 450
cert_cover_2 3 5 0 6 7 194 450 3
cert_coverFacet 4 564
cert_cover_2 4 3 1 4 8 52 564 3
cert_coverFacet 5 916
cert_cover_5 5 0 1 3 6 7 148 916 3
cert_coverFacet 6 964
cert_cover_5 6 0 1 5 6 7 196 964 3
cert_coverFacet 7 824
cert_cover_5 7 3 2 3 4 7 56 824 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1829

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_one_six_1830.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1830

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 613, 681, 961, 214, 410, 820, 468, 836, 824, 904, 7, 11, 67, 37, 69, 41, 137, 545, 193, 577, 641, 22, 70, 26, 138, 146, 194, 52, 212, 276, 548, 324, 580, 772, 56, 280, 552, 392, 648, 776, 816, 400, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_613, vertices_681, vertices_961, vertices_214, vertices_410, vertices_820, vertices_468, vertices_836, vertices_824, vertices_904] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_37, vertices_69, vertices_41, vertices_137, vertices_545, vertices_193, vertices_577, vertices_641, vertices_22, vertices_70, vertices_26, vertices_138, vertices_146, vertices_194, vertices_52, vertices_212, vertices_276, vertices_548, vertices_324, vertices_580, vertices_772, vertices_56, vertices_280, vertices_552, vertices_392, vertices_648, vertices_776, vertices_816, vertices_400, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_613), (false, vertices_681), (false, vertices_961), (true, vertices_146), (true, vertices_212), (true, vertices_276), (true, vertices_324), (true, vertices_772), (true, vertices_280), (true, vertices_392), (true, vertices_776), (true, vertices_816), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 11 15 17 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 10 else
  if p.val = (false, vertices_613) then 13 else
  if p.val = (false, vertices_681) then 16 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_212) then 14 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_324) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_816) then 18 else
  if p.val = (true, vertices_400) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_212), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 7 8 816
cert_row_2 1 1 3 5 6 212
cert_row_4 2 0 2 3 6 7 410 26 3
cert_rows_3
cert_pivot_3 1 4 0
cert_heightProof 3
cert_coverFacet 0 214
cert_cover_5 0 1 0 1 3 5 22 214 3
cert_coverFacet 1 410
cert_cover_5 1 2 0 2 3 6 26 410 3
cert_coverFacet 2 820
cert_cover_5 2 0 1 3 4 7 52 820 3
cert_coverFacet 3 468
cert_cover_5 3 1 1 3 5 7 212 468 3
cert_coverFacet 4 836
cert_cover_2 4 5 1 7 8 324 836 3
cert_coverFacet 5 824
cert_cover_5 5 0 2 3 4 7 56 824 3
cert_coverFacet 6 904
cert_cover_2 6 6 2 7 8 392 904 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1830

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_prism_completion_next_oneprism_m13e11q3_models_0001.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_completion_next_oneprism_m13e11q3_models_0001

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [95, 527, 339, 803, 357, 677, 410, 778, 220, 652, 228, 936, 496, 15, 83, 259, 515, 37, 69, 517, 289, 545, 321, 26, 266, 522, 274, 770, 92, 140, 524, 100, 164, 196, 644, 152, 392, 648, 776, 208, 336, 400, 224, 352, 416, 672, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_95, vertices_527, vertices_339, vertices_803, vertices_357, vertices_677, vertices_410, vertices_778, vertices_220, vertices_652, vertices_228, vertices_936, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_15, vertices_83, vertices_259, vertices_515, vertices_37, vertices_69, vertices_517, vertices_289, vertices_545, vertices_321, vertices_26, vertices_266, vertices_522, vertices_274, vertices_770, vertices_92, vertices_140, vertices_524, vertices_100, vertices_164, vertices_196, vertices_644, vertices_152, vertices_392, vertices_648, vertices_776, vertices_208, vertices_336, vertices_400, vertices_224, vertices_352, vertices_416, vertices_672, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_95), (false, vertices_527), (false, vertices_339), (false, vertices_803), (false, vertices_357), (false, vertices_677), (true, vertices_266), (true, vertices_140), (true, vertices_196), (true, vertices_152), (true, vertices_392), (true, vertices_648), (true, vertices_776), (true, vertices_208), (true, vertices_400), (true, vertices_224), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 11 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_95) then 14 else
  if p.val = (false, vertices_527) then 12 else
  if p.val = (false, vertices_339) then 15 else
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_357) then 18 else
  if p.val = (false, vertices_677) then 19 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_196) then 2 else
  if p.val = (true, vertices_152) then 3 else
  if p.val = (true, vertices_392) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_416) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inl 2
  | 12 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_95), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 5 92
cert_row_4 1 0 2 3 6 7 410 26 3
cert_row_4 2 2 4 6 7 8 936 392 1
cert_row_4 3 3 4 5 6 7 496 208 1
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 410
cert_cover_5 0 1 0 2 3 6 26 410 3
cert_coverFacet 1 778
cert_cover_2 1 2 0 7 8 266 778 3
cert_coverFacet 2 220
cert_cover_5 2 0 1 2 3 6 92 220 3
cert_coverFacet 3 652
cert_cover_2 3 2 1 6 8 140 652 3
cert_coverFacet 4 228
cert_cover_2 4 4 1 5 6 100 228 3
cert_coverFacet 5 936
cert_cover_5 5 2 2 4 6 7 392 936 1
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 208 496 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_completion_next_oneprism_m13e11q3_models_0001

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_prism_completion_next_oneprism_m13e11q3_models_0002.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_completion_next_oneprism_m13e11q3_models_0002

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [95, 595, 285, 613, 421, 817, 206, 794, 650, 738, 396, 228, 936, 83, 29, 37, 69, 261, 273, 529, 289, 545, 577, 78, 26, 138, 522, 530, 194, 578, 642, 140, 268, 100, 164, 196, 388, 280, 392, 648, 776, 784, 224, 608, 416, 672, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_95, vertices_595, vertices_285, vertices_613, vertices_421, vertices_817, vertices_206, vertices_794, vertices_650, vertices_738, vertices_396, vertices_228, vertices_936] (by decide +kernel)
  polygons := literalFinset [vertices_83, vertices_29, vertices_37, vertices_69, vertices_261, vertices_273, vertices_529, vertices_289, vertices_545, vertices_577, vertices_78, vertices_26, vertices_138, vertices_522, vertices_530, vertices_194, vertices_578, vertices_642, vertices_140, vertices_268, vertices_100, vertices_164, vertices_196, vertices_388, vertices_280, vertices_392, vertices_648, vertices_776, vertices_784, vertices_224, vertices_608, vertices_416, vertices_672, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_95), (false, vertices_595), (false, vertices_285), (false, vertices_613), (false, vertices_421), (false, vertices_817), (true, vertices_138), (true, vertices_522), (true, vertices_194), (true, vertices_642), (true, vertices_140), (true, vertices_196), (true, vertices_392), (true, vertices_648), (true, vertices_776), (true, vertices_224), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 16 13 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_95) then 14 else
  if p.val = (false, vertices_595) then 12 else
  if p.val = (false, vertices_285) then 15 else
  if p.val = (false, vertices_613) then 17 else
  if p.val = (false, vertices_421) then 18 else
  if p.val = (false, vertices_817) then 20 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_672) then 10 else
  0
cert_priority
cert_nodeAtPriority_59 0 138 2 522 1 194 642 140 196 392 648 776 224 672 595 95 285 613 421 817
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 2 3 7 8 794 26 3
cert_row_4 2 0 4 5 6 8 738 194 1
cert_row_4 3 2 4 6 7 8 936 392 1
cert_rows
cert_pivot_2 1 3 0 2
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 6 78 206 3
cert_coverFacet 1 794
cert_cover_5 1 1 0 2 3 7 26 794 3
cert_coverFacet 2 650
cert_cover_2 2 2 0 6 8 138 650 3
cert_coverFacet 3 738
cert_cover_5 3 2 0 4 5 6 194 738 1
cert_coverFacet 4 396
cert_cover_2 4 2 1 6 7 140 396 3
cert_coverFacet 5 228
cert_cover_2 5 4 1 5 6 100 228 3
cert_coverFacet 6 936
cert_cover_5 6 3 2 4 6 7 392 936 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_completion_next_oneprism_m13e11q3_models_0002

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_prism_completion_next_oneprism_m13e11q3_models_0004.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_completion_next_oneprism_m13e11q3_models_0004

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [111, 551, 213, 901, 121, 689, 334, 774, 314, 930, 452, 472, 432, 39, 69, 133, 517, 105, 49, 81, 145, 545, 641, 78, 262, 518, 42, 266, 290, 546, 770, 196, 324, 388, 772, 56, 88, 280, 328, 176, 304, 208, 400, 416, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_111, vertices_551, vertices_213, vertices_901, vertices_121, vertices_689, vertices_334, vertices_774, vertices_314, vertices_930, vertices_452, vertices_472, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_39, vertices_69, vertices_133, vertices_517, vertices_105, vertices_49, vertices_81, vertices_145, vertices_545, vertices_641, vertices_78, vertices_262, vertices_518, vertices_42, vertices_266, vertices_290, vertices_546, vertices_770, vertices_196, vertices_324, vertices_388, vertices_772, vertices_56, vertices_88, vertices_280, vertices_328, vertices_176, vertices_304, vertices_208, vertices_400, vertices_416, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_111), (false, vertices_551), (false, vertices_213), (false, vertices_901), (false, vertices_121), (false, vertices_689), (true, vertices_262), (true, vertices_266), (true, vertices_290), (true, vertices_770), (true, vertices_324), (true, vertices_280), (true, vertices_328), (true, vertices_304), (true, vertices_400), (true, vertices_416), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_111) then 17 else
  if p.val = (false, vertices_551) then 12 else
  if p.val = (false, vertices_213) then 14 else
  if p.val = (false, vertices_901) then 15 else
  if p.val = (false, vertices_121) then 18 else
  if p.val = (false, vertices_689) then 20 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_324) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_448) then 10 else
  0
cert_priority
cert_nodeAtPriority_59 0 262 1 266 2 290 770 324 280 328 304 400 416 448 551 213 901 111 121 689
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 4 6 7 8 930 290 2
cert_row_4 2 0 2 3 4 7 314 42 2
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 7 78 334 3
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 314
cert_cover_5 2 2 0 2 3 4 42 314 2
cert_coverFacet 3 930
cert_cover_5 3 1 0 4 6 7 290 930 2
cert_coverFacet 4 452
cert_cover_2 4 5 1 6 7 196 452 3
cert_coverFacet 5 472
cert_cover_5 5 3 2 3 5 6 88 472 3
cert_coverFacet 6 432
cert_cover_2 6 4 3 6 7 176 432 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_completion_next_oneprism_m13e11q3_models_0004

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_prism_completion_next_oneprism_m13e11q3_models_0005.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_completion_next_oneprism_m13e11q3_models_0005

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 677, 293, 453, 841, 721, 126, 302, 602, 778, 690, 332, 244, 37, 133, 261, 289, 545, 193, 321, 577, 641, 769, 46, 90, 266, 522, 50, 530, 290, 546, 770, 76, 268, 116, 164, 292, 196, 324, 328, 584, 776, 176, 208, 592, 656, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_677, vertices_293, vertices_453, vertices_841, vertices_721, vertices_126, vertices_302, vertices_602, vertices_778, vertices_690, vertices_332, vertices_244] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_46, vertices_90, vertices_266, vertices_522, vertices_50, vertices_530, vertices_290, vertices_546, vertices_770, vertices_76, vertices_268, vertices_116, vertices_164, vertices_292, vertices_196, vertices_324, vertices_328, vertices_584, vertices_776, vertices_176, vertices_208, vertices_592, vertices_656, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_677), (false, vertices_293), (false, vertices_453), (false, vertices_841), (false, vertices_721), (true, vertices_46), (true, vertices_90), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_530), (true, vertices_76), (true, vertices_268), (true, vertices_116), (true, vertices_176)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 12 16 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 9 else
  if p.val = (false, vertices_677) then 13 else
  if p.val = (false, vertices_293) then 0 else
  if p.val = (false, vertices_453) then 14 else
  if p.val = (false, vertices_841) then 17 else
  if p.val = (false, vertices_721) then 19 else
  if p.val = (true, vertices_46) then 10 else
  if p.val = (true, vertices_90) then 11 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_116) then 15 else
  if p.val = (true, vertices_176) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_46), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_90), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_116), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 5 126 46 3
cert_row_4 1 0 1 2 3 4 126 46 3
cert_row_4 2 0 3 4 6 8 690 50 3
cert_rows_3
cert_pivot_3 1 5 0
cert_heightProof 3
cert_coverFacet 0 126
cert_cover_2 0 1 0 2 3 46 126 3
cert_coverFacet 1 302
cert_cover 1 2 1 0 1 3 0 7 2 46 302 46 46 126 3
cert_coverFacet 2 602
cert_cover 2 3 1 0 2 3 0 8 2 90 602 90 46 126 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 690
cert_cover_5 4 2 0 3 4 6 50 690 3
cert_coverFacet 5 332
cert_cover_2 5 2 1 5 7 76 332 3
cert_coverFacet 6 244
cert_cover 6 4 1 1 3 3 0 6 2 116 244 116 46 126 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_completion_next_oneprism_m13e11q3_models_0005

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_prism_completion_next_oneprism_m13e11q3_models_0006.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_completion_next_oneprism_m13e11q3_models_0006

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [295, 115, 403, 397, 629, 661, 362, 850, 620, 300, 652, 920, 840, 19, 35, 259, 533, 37, 133, 261, 113, 145, 385, 82, 274, 98, 290, 322, 44, 140, 268, 524, 612, 292, 644, 104, 296, 328, 584, 392, 648, 776, 592, 400, 656, 784, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_115, vertices_403, vertices_397, vertices_629, vertices_661, vertices_362, vertices_850, vertices_620, vertices_300, vertices_652, vertices_920, vertices_840] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_259, vertices_533, vertices_37, vertices_133, vertices_261, vertices_113, vertices_145, vertices_385, vertices_82, vertices_274, vertices_98, vertices_290, vertices_322, vertices_44, vertices_140, vertices_268, vertices_524, vertices_612, vertices_292, vertices_644, vertices_104, vertices_296, vertices_328, vertices_584, vertices_392, vertices_648, vertices_776, vertices_592, vertices_400, vertices_656, vertices_784, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_115), (false, vertices_403), (false, vertices_397), (false, vertices_629), (false, vertices_661), (true, vertices_322), (true, vertices_44), (true, vertices_524), (true, vertices_104), (true, vertices_296), (true, vertices_328), (true, vertices_584), (true, vertices_648), (true, vertices_776), (true, vertices_784), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 12 else
  if p.val = (false, vertices_115) then 19 else
  if p.val = (false, vertices_403) then 13 else
  if p.val = (false, vertices_397) then 15 else
  if p.val = (false, vertices_629) then 20 else
  if p.val = (false, vertices_661) then 16 else
  if p.val = (true, vertices_322) then 0 else
  if p.val = (true, vertices_44) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_104) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
cert_nodeAtPriority_35 322 44 524 104 296 328 584 648 776 784 832 295 403 397 661 115 629
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 5 8 612
cert_row_4 1 0 2 4 5 7 362 98 1
cert_row_4 2 0 3 5 7 8 850 82 3
cert_row_4 3 2 3 6 7 8 920 392 1
cert_rows
cert_pivot_2 1 4 0 2
cert_heightProof 4
cert_coverFacet 0 362
cert_cover_5 0 1 0 2 4 5 98 362 1
cert_coverFacet 1 850
cert_cover_5 1 2 0 3 5 7 82 850 3
cert_coverFacet 2 620
cert_cover_5 2 0 1 2 4 5 44 620 3
cert_coverFacet 3 300
cert_cover_2 3 2 1 4 7 44 300 3
cert_coverFacet 4 652
cert_cover_2 4 2 1 6 8 140 652 3
cert_coverFacet 5 920
cert_cover_5 5 3 2 3 6 7 392 920 1
cert_coverFacet 6 840
cert_cover_2 6 5 2 7 8 328 840 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_completion_next_oneprism_m13e11q3_models_0006

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_prism_completion_next_oneprism_m13e11q3_models_0007.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_completion_next_oneprism_m13e11q3_models_0007

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 61, 421, 345, 809, 574, 678, 454, 602, 338, 706, 968, 928, 21, 37, 261, 25, 41, 265, 273, 289, 22, 550, 134, 262, 538, 82, 274, 194, 322, 578, 642, 60, 164, 388, 88, 552, 328, 584, 776, 336, 416, 672, 800, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_61, vertices_421, vertices_345, vertices_809, vertices_574, vertices_678, vertices_454, vertices_602, vertices_338, vertices_706, vertices_968, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_261, vertices_25, vertices_41, vertices_265, vertices_273, vertices_289, vertices_22, vertices_550, vertices_134, vertices_262, vertices_538, vertices_82, vertices_274, vertices_194, vertices_322, vertices_578, vertices_642, vertices_60, vertices_164, vertices_388, vertices_88, vertices_552, vertices_328, vertices_584, vertices_776, vertices_336, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_61), (false, vertices_421), (false, vertices_345), (false, vertices_809), (true, vertices_550), (true, vertices_134), (true, vertices_538), (true, vertices_82), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_642), (true, vertices_584), (true, vertices_672), (true, vertices_448), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 15 18 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 12 else
  if p.val = (false, vertices_61) then 16 else
  if p.val = (false, vertices_421) then 17 else
  if p.val = (false, vertices_345) then 19 else
  if p.val = (false, vertices_809) then 20 else
  if p.val = (true, vertices_550) then 13 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_538) then 14 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_279), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_550), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_538), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_61), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 4 574 22 2
cert_row_4 1 0 1 2 3 8 574 22 2
cert_row_4 2 0 1 5 6 7 454 134 2
cert_row_4 3 2 5 6 7 8 968 328 2
cert_rows
cert_pivot_2 4 3 0 2
cert_heightProof 4
cert_coverFacet 0 574
cert_cover_2 0 1 0 2 3 22 574 2
cert_coverFacet 1 678
cert_cover 1 4 1 0 1 2 0 6 2 550 678 550 22 574 3
cert_coverFacet 2 454
cert_cover_5 2 2 0 1 5 6 134 454 2
cert_coverFacet 3 602
cert_cover 3 3 1 0 2 2 0 5 2 538 602 538 22 574 3
cert_coverFacet 4 338
cert_cover_2 4 3 0 5 7 82 338 3
cert_coverFacet 5 706
cert_cover_2 5 5 0 6 8 194 706 3
cert_coverFacet 6 968
cert_cover_5 6 3 2 5 6 7 328 968 2
cert_coverFacet 7 928
cert_cover_2 7 6 4 7 8 416 928 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_completion_next_oneprism_m13e11q3_models_0007

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_prism_completion_next_oneprism_m13e11q3_models_0009.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_completion_next_oneprism_m13e11q3_models_0009

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 539, 205, 181, 841, 721, 302, 778, 690, 866, 332, 740, 356, 27, 13, 53, 133, 73, 521, 145, 529, 193, 577, 46, 266, 522, 50, 530, 290, 546, 770, 76, 268, 100, 164, 292, 196, 324, 328, 776, 176, 656, 352, 608, 672, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_539, vertices_205, vertices_181, vertices_841, vertices_721, vertices_302, vertices_778, vertices_690, vertices_866, vertices_332, vertices_740, vertices_356] (by decide +kernel)
  polygons := literalFinset [vertices_27, vertices_13, vertices_53, vertices_133, vertices_73, vertices_521, vertices_145, vertices_529, vertices_193, vertices_577, vertices_46, vertices_266, vertices_522, vertices_50, vertices_530, vertices_290, vertices_546, vertices_770, vertices_76, vertices_268, vertices_100, vertices_164, vertices_292, vertices_196, vertices_324, vertices_328, vertices_776, vertices_176, vertices_656, vertices_352, vertices_608, vertices_672, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_539), (false, vertices_205), (false, vertices_181), (false, vertices_841), (false, vertices_721), (true, vertices_266), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_268), (true, vertices_100), (true, vertices_292), (true, vertices_324), (true, vertices_352), (true, vertices_608), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_539) then 12 else
  if p.val = (false, vertices_205) then 15 else
  if p.val = (false, vertices_181) then 16 else
  if p.val = (false, vertices_841) then 18 else
  if p.val = (false, vertices_721) then 20 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_290) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_100) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_352) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_672) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 4 46
cert_row_4 1 0 3 4 6 8 690 50 3
cert_row_4 2 0 4 5 7 8 866 290 2
cert_row_4 3 1 4 5 6 8 740 100 3
cert_rows
cert_pivot_2 2 3 0 1
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 0 0 1 2 7 46 302 3
cert_coverFacet 1 778
cert_cover_2 1 2 0 7 8 266 778 3
cert_coverFacet 2 690
cert_cover_5 2 1 0 3 4 6 50 690 3
cert_coverFacet 3 866
cert_cover_5 3 2 0 4 5 7 290 866 2
cert_coverFacet 4 332
cert_cover_2 4 2 1 5 7 76 332 3
cert_coverFacet 5 740
cert_cover_5 5 3 1 4 5 6 100 740 3
cert_coverFacet 6 356
cert_cover_2 6 4 1 5 7 100 356 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_completion_next_oneprism_m13e11q3_models_0009

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_prism_completion_next_oneprism_m13e11q3_models_0010.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_completion_next_oneprism_m13e11q3_models_0010

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [111, 527, 341, 901, 121, 793, 230, 646, 570, 930, 452, 496, 816, 15, 69, 261, 517, 25, 105, 521, 81, 273, 769, 102, 134, 518, 42, 522, 162, 546, 642, 196, 324, 388, 644, 56, 536, 112, 304, 560, 336, 784, 224, 416, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_111, vertices_527, vertices_341, vertices_901, vertices_121, vertices_793, vertices_230, vertices_646, vertices_570, vertices_930, vertices_452, vertices_496, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_15, vertices_69, vertices_261, vertices_517, vertices_25, vertices_105, vertices_521, vertices_81, vertices_273, vertices_769, vertices_102, vertices_134, vertices_518, vertices_42, vertices_522, vertices_162, vertices_546, vertices_642, vertices_196, vertices_324, vertices_388, vertices_644, vertices_56, vertices_536, vertices_112, vertices_304, vertices_560, vertices_336, vertices_784, vertices_224, vertices_416, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_111), (false, vertices_527), (false, vertices_341), (false, vertices_901), (false, vertices_121), (false, vertices_793), (true, vertices_134), (true, vertices_162), (true, vertices_546), (true, vertices_642), (true, vertices_196), (true, vertices_304), (true, vertices_560), (true, vertices_224), (true, vertices_416), (true, vertices_800), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_111) then 17 else
  if p.val = (false, vertices_527) then 12 else
  if p.val = (false, vertices_341) then 14 else
  if p.val = (false, vertices_901) then 15 else
  if p.val = (false, vertices_121) then 18 else
  if p.val = (false, vertices_793) then 19 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_304) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_224) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_448) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_111), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 4 5 102
cert_row_4 1 0 2 3 4 8 570 42 2
cert_row_4 2 0 4 6 7 8 930 162 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 230
cert_cover_5 0 0 0 1 4 6 102 230 3
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 570
cert_cover_5 2 1 0 2 3 4 42 570 2
cert_coverFacet 3 930
cert_cover_5 3 2 0 4 6 7 162 930 3
cert_coverFacet 4 452
cert_cover_2 4 5 1 6 7 196 452 3
cert_coverFacet 5 496
cert_cover_5 5 3 3 4 5 6 112 496 3
cert_coverFacet 6 816
cert_cover_2 6 4 3 7 8 304 816 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_completion_next_oneprism_m13e11q3_models_0010

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_prism_completion_next_oneprism_m13e11q3_models_0011.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_completion_next_oneprism_m13e11q3_models_0011

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 341, 233, 209, 353, 929, 574, 790, 218, 682, 898, 124, 868, 81, 145, 273, 97, 161, 289, 193, 321, 385, 534, 26, 554, 138, 146, 274, 386, 642, 770, 60, 84, 276, 100, 548, 324, 772, 88, 104, 168, 200, 208, 352, 672, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_341, vertices_233, vertices_209, vertices_353, vertices_929, vertices_574, vertices_790, vertices_218, vertices_682, vertices_898, vertices_124, vertices_868] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_145, vertices_273, vertices_97, vertices_161, vertices_289, vertices_193, vertices_321, vertices_385, vertices_534, vertices_26, vertices_554, vertices_138, vertices_146, vertices_274, vertices_386, vertices_642, vertices_770, vertices_60, vertices_84, vertices_276, vertices_100, vertices_548, vertices_324, vertices_772, vertices_88, vertices_104, vertices_168, vertices_200, vertices_208, vertices_352, vertices_672, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_341), (false, vertices_233), (false, vertices_209), (false, vertices_353), (false, vertices_929), (true, vertices_534), (true, vertices_26), (true, vertices_554), (true, vertices_138), (true, vertices_642), (true, vertices_770), (true, vertices_60), (true, vertices_100), (true, vertices_548), (true, vertices_772), (true, vertices_88)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 14 17 19 20 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 11 else
  if p.val = (false, vertices_341) then 15 else
  if p.val = (false, vertices_233) then 18 else
  if p.val = (false, vertices_209) then 0 else
  if p.val = (false, vertices_353) then 1 else
  if p.val = (false, vertices_929) then 21 else
  if p.val = (true, vertices_534) then 12 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_554) then 13 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_60) then 16 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_88) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_209), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_353), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_534), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_554), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_60), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 6 218 26 3
cert_row_4 1 1 4 5 7 8 868 100 3
cert_row_4 2 0 1 2 3 4 574 534 2
cert_row_4 3 0 1 2 3 8 574 534 2
cert_rows
cert_pivot_2 6 5 4 0
cert_heightProof 4
cert_coverFacet 0 574
cert_cover_2 0 1 0 2 3 534 574 2
cert_coverFacet 1 790
cert_cover 1 3 1 0 1 2 0 7 2 534 790 534 534 574 3
cert_coverFacet 2 218
cert_cover_5 2 0 0 2 3 5 26 218 3
cert_coverFacet 3 682
cert_cover 3 4 1 0 2 2 0 6 2 554 682 554 534 574 3
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 124
cert_cover 5 3 1 1 2 2 0 5 2 60 124 60 534 574 3
cert_coverFacet 6 868
cert_cover_5 6 1 1 4 5 7 100 868 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_completion_next_oneprism_m13e11q3_models_0011

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_prism_completion_next_oneprism_m14e11q3_models_0000.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_completion_next_oneprism_m14e11q3_models_0000

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [355, 675, 579, 837, 905, 433, 126, 590, 570, 412, 780, 372, 664, 688, 35, 67, 515, 161, 289, 321, 577, 385, 641, 769, 78, 58, 522, 98, 546, 578, 28, 268, 524, 116, 276, 324, 580, 772, 152, 536, 392, 648, 776, 176, 304, 560, 400, 656, 352, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_355, vertices_675, vertices_579, vertices_837, vertices_905, vertices_433, vertices_126, vertices_590, vertices_570, vertices_412, vertices_780, vertices_372, vertices_664, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_515, vertices_161, vertices_289, vertices_321, vertices_577, vertices_385, vertices_641, vertices_769, vertices_78, vertices_58, vertices_522, vertices_98, vertices_546, vertices_578, vertices_28, vertices_268, vertices_524, vertices_116, vertices_276, vertices_324, vertices_580, vertices_772, vertices_152, vertices_536, vertices_392, vertices_648, vertices_776, vertices_176, vertices_304, vertices_560, vertices_400, vertices_656, vertices_352, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_355), (false, vertices_675), (false, vertices_579), (false, vertices_837), (false, vertices_905), (false, vertices_433), (true, vertices_78), (true, vertices_58), (true, vertices_522), (true, vertices_28), (true, vertices_268), (true, vertices_524), (true, vertices_116), (true, vertices_276), (true, vertices_152), (true, vertices_536), (true, vertices_560), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 10 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_355) then 15 else
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_579) then 0 else
  if p.val = (false, vertices_837) then 18 else
  if p.val = (false, vertices_905) then 11 else
  if p.val = (false, vertices_433) then 21 else
  if p.val = (true, vertices_78) then 12 else
  if p.val = (true, vertices_58) then 13 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_116) then 19 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_656) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_579), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inl 2
  | 11 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_78), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_58), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_116), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 4 126 78 3
cert_row_4 1 0 1 2 3 5 126 78 3
cert_row_4 2 1 2 3 6 7 412 28 3
cert_rows_3
cert_pivot_3 0 4 1
cert_heightProof 3
cert_coverFacet 0 126
cert_cover_2 0 1 0 2 3 78 126 3
cert_coverFacet 1 590
cert_cover 1 2 1 0 1 3 0 8 2 78 590 78 78 126 3
cert_coverFacet 2 570
cert_cover 2 3 1 0 2 3 0 8 2 58 570 58 78 126 3
cert_coverFacet 3 412
cert_cover_5 3 2 1 2 3 6 28 412 3
cert_coverFacet 4 780
cert_cover_2 4 2 1 7 8 268 780 3
cert_coverFacet 5 372
cert_cover 5 4 1 1 3 3 0 7 2 116 372 116 78 126 3
cert_coverFacet 6 664
cert_cover_2 6 3 2 6 8 152 664 3
cert_coverFacet 7 688
cert_cover_2 7 4 3 6 8 176 688 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_completion_next_oneprism_m14e11q3_models_0000

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_prism_completion_next_oneprism_m14e11q3_models_0001.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_completion_next_oneprism_m14e11q3_models_0001

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [543, 775, 171, 355, 157, 229, 325, 794, 298, 724, 836, 248, 312, 880, 519, 11, 35, 259, 29, 69, 133, 261, 137, 97, 161, 321, 538, 42, 266, 290, 770, 148, 532, 196, 324, 580, 772, 56, 152, 280, 168, 296, 112, 304, 208, 592, 784, 224, 352, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_543, vertices_775, vertices_171, vertices_355, vertices_157, vertices_229, vertices_325, vertices_794, vertices_298, vertices_724, vertices_836, vertices_248, vertices_312, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_519, vertices_11, vertices_35, vertices_259, vertices_29, vertices_69, vertices_133, vertices_261, vertices_137, vertices_97, vertices_161, vertices_321, vertices_538, vertices_42, vertices_266, vertices_290, vertices_770, vertices_148, vertices_532, vertices_196, vertices_324, vertices_580, vertices_772, vertices_56, vertices_152, vertices_280, vertices_168, vertices_296, vertices_112, vertices_304, vertices_208, vertices_592, vertices_784, vertices_224, vertices_352, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_543), (false, vertices_775), (false, vertices_171), (false, vertices_355), (false, vertices_157), (false, vertices_229), (false, vertices_325), (true, vertices_266), (true, vertices_580), (true, vertices_56), (true, vertices_280), (true, vertices_296), (true, vertices_112), (true, vertices_304), (true, vertices_208), (true, vertices_592), (true, vertices_784), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 12 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_543) then 16 else
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_171) then 13 else
  if p.val = (false, vertices_355) then 18 else
  if p.val = (false, vertices_157) then 14 else
  if p.val = (false, vertices_229) then 20 else
  if p.val = (false, vertices_325) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_580) then 2 else
  if p.val = (true, vertices_56) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_832) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_325), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inl 2
  | 13 => Sum.inr ⟨(false, vertices_171), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_543), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 8 538
cert_row_4 1 1 3 5 6 8 724 148 2
cert_row_4 2 2 3 4 5 6 248 56 3
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 794
cert_cover_5 0 0 0 2 3 7 538 794 3
cert_coverFacet 1 298
cert_cover_2 1 2 0 4 7 42 298 3
cert_coverFacet 2 724
cert_cover_5 2 1 1 3 5 6 148 724 2
cert_coverFacet 3 836
cert_cover_2 3 5 1 7 8 324 836 3
cert_coverFacet 4 248
cert_cover_5 4 2 2 3 4 5 56 248 3
cert_coverFacet 5 312
cert_cover_2 5 3 2 4 7 56 312 3
cert_coverFacet 6 880
cert_cover_5 6 3 3 4 5 7 112 880 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_completion_next_oneprism_m14e11q3_models_0001

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_prism_completion_next_oneprism_m14e11q3_models_0002.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_completion_next_oneprism_m14e11q3_models_0002

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 837, 425, 553, 649, 465, 705, 126, 558, 342, 774, 434, 716, 248, 41, 137, 521, 289, 545, 193, 321, 577, 385, 641, 769, 46, 86, 262, 518, 50, 274, 290, 546, 770, 76, 524, 324, 580, 772, 120, 168, 552, 200, 648, 176, 208, 336, 400, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_837, vertices_425, vertices_553, vertices_649, vertices_465, vertices_705, vertices_126, vertices_558, vertices_342, vertices_774, vertices_434, vertices_716, vertices_248] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_137, vertices_521, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_641, vertices_769, vertices_46, vertices_86, vertices_262, vertices_518, vertices_50, vertices_274, vertices_290, vertices_546, vertices_770, vertices_76, vertices_524, vertices_324, vertices_580, vertices_772, vertices_120, vertices_168, vertices_552, vertices_200, vertices_648, vertices_176, vertices_208, vertices_336, vertices_400, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_837), (false, vertices_425), (false, vertices_553), (false, vertices_649), (false, vertices_465), (false, vertices_705), (true, vertices_46), (true, vertices_86), (true, vertices_262), (true, vertices_518), (true, vertices_50), (true, vertices_274), (true, vertices_76), (true, vertices_524), (true, vertices_120), (true, vertices_200), (true, vertices_176)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 15 17 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 12 else
  if p.val = (false, vertices_837) then 16 else
  if p.val = (false, vertices_425) then 18 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_649) then 1 else
  if p.val = (false, vertices_465) then 21 else
  if p.val = (false, vertices_705) then 2 else
  if p.val = (true, vertices_46) then 13 else
  if p.val = (true, vertices_86) then 14 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_120) then 19 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_176) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_649), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_705), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_46), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_86), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_120), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 6 7 434 50 3
cert_row_4 1 0 1 2 3 4 126 46 3
cert_row_4 2 0 1 2 3 5 126 46 3
cert_row_4 3 1 2 5 6 8 716 76 3
cert_rows
cert_pivot_2 7 4 0 1
cert_heightProof 4
cert_coverFacet 0 126
cert_cover_2 0 1 0 2 3 46 126 3
cert_coverFacet 1 558
cert_cover 1 2 1 0 1 3 0 8 2 46 558 46 46 126 3
cert_coverFacet 2 342
cert_cover 2 3 1 0 1 3 0 7 2 86 342 86 46 126 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 434
cert_cover_5 4 0 0 3 4 6 50 434 3
cert_coverFacet 5 716
cert_cover_5 5 3 1 2 5 6 76 716 3
cert_coverFacet 6 248
cert_cover 6 4 1 2 3 3 0 6 2 120 248 120 46 126 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_completion_next_oneprism_m14e11q3_models_0002

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_prism_completion_next_oneprism_m14e11q3_models_0003.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_completion_next_oneprism_m14e11q3_models_0003

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 565, 617, 241, 913, 246, 406, 358, 842, 898, 796, 300, 556, 360, 49, 145, 529, 97, 545, 193, 577, 641, 150, 102, 262, 194, 322, 578, 386, 642, 770, 44, 268, 524, 52, 276, 532, 292, 548, 104, 296, 552, 328, 584, 776, 240, 400, 784, 352, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_565, vertices_617, vertices_241, vertices_913, vertices_246, vertices_406, vertices_358, vertices_842, vertices_898, vertices_796, vertices_300, vertices_556, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_145, vertices_529, vertices_97, vertices_545, vertices_193, vertices_577, vertices_641, vertices_150, vertices_102, vertices_262, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_44, vertices_268, vertices_524, vertices_52, vertices_276, vertices_532, vertices_292, vertices_548, vertices_104, vertices_296, vertices_552, vertices_328, vertices_584, vertices_776, vertices_240, vertices_400, vertices_784, vertices_352, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_565), (false, vertices_617), (false, vertices_241), (false, vertices_913), (true, vertices_150), (true, vertices_102), (true, vertices_262), (true, vertices_322), (true, vertices_386), (true, vertices_770), (true, vertices_44), (true, vertices_268), (true, vertices_524), (true, vertices_276), (true, vertices_292), (true, vertices_296), (true, vertices_328), (true, vertices_776), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 19 21 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 14 else
  if p.val = (false, vertices_565) then 18 else
  if p.val = (false, vertices_617) then 20 else
  if p.val = (false, vertices_241) then 22 else
  if p.val = (false, vertices_913) then 23 else
  if p.val = (true, vertices_150) then 15 else
  if p.val = (true, vertices_102) then 16 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_352) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_150), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_102), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 6 246 150 3
cert_row_4 1 0 1 3 4 5 246 150 3
cert_row_4 2 0 2 5 7 8 842 322 1
cert_row_4 3 1 2 3 7 8 796 268 2
cert_rows
cert_pivot_2 6 4 0 1
cert_heightProof 4
cert_coverFacet 0 246
cert_cover_2 0 1 0 3 4 150 246 3
cert_coverFacet 1 406
cert_cover 1 3 1 0 1 3 0 7 3 150 406 150 150 246 4
cert_coverFacet 2 358
cert_cover 2 4 1 0 1 3 0 7 3 102 358 102 150 246 4
cert_coverFacet 3 842
cert_cover_5 3 2 0 2 5 7 322 842 1
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 796
cert_cover_5 5 3 1 2 3 7 268 796 2
cert_coverFacet 6 300
cert_cover_2 6 2 1 4 7 44 300 3
cert_coverFacet 7 556
cert_cover_2 7 2 1 4 8 44 556 3
cert_coverFacet 8 360
cert_cover_2 8 4 2 5 7 104 360 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_completion_next_oneprism_m14e11q3_models_0003

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_prism_completion_next_oneprism_m14e11q3_models_0004.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_completion_next_oneprism_m14e11q3_models_0004

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [211, 301, 121, 409, 737, 417, 126, 542, 614, 914, 706, 780, 932, 792, 25, 41, 265, 81, 145, 97, 161, 289, 193, 385, 30, 102, 518, 82, 146, 530, 194, 578, 642, 44, 268, 524, 292, 548, 772, 120, 280, 536, 776, 400, 784, 608, 416, 672, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_211, vertices_301, vertices_121, vertices_409, vertices_737, vertices_417, vertices_126, vertices_542, vertices_614, vertices_914, vertices_706, vertices_780, vertices_932, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_265, vertices_81, vertices_145, vertices_97, vertices_161, vertices_289, vertices_193, vertices_385, vertices_30, vertices_102, vertices_518, vertices_82, vertices_146, vertices_530, vertices_194, vertices_578, vertices_642, vertices_44, vertices_268, vertices_524, vertices_292, vertices_548, vertices_772, vertices_120, vertices_280, vertices_536, vertices_776, vertices_400, vertices_784, vertices_608, vertices_416, vertices_672, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_211), (false, vertices_301), (false, vertices_121), (false, vertices_409), (false, vertices_737), (false, vertices_417), (true, vertices_30), (true, vertices_102), (true, vertices_518), (true, vertices_530), (true, vertices_578), (true, vertices_642), (true, vertices_524), (true, vertices_548), (true, vertices_772), (true, vertices_536), (true, vertices_776), (true, vertices_784), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 16 18 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_211) then 13 else
  if p.val = (false, vertices_301) then 17 else
  if p.val = (false, vertices_121) then 19 else
  if p.val = (false, vertices_409) then 20 else
  if p.val = (false, vertices_737) then 23 else
  if p.val = (false, vertices_417) then 0 else
  if p.val = (true, vertices_30) then 14 else
  if p.val = (true, vertices_102) then 15 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_776) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_417), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_30), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_102), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 5 126 30 3
cert_row_4 1 0 1 2 4 3 126 30 3
cert_row_4 2 0 3 6 7 8 914 146 3
cert_row_4 3 1 4 6 7 8 932 292 2
cert_rows
cert_pivot_2 5 2 0 1
cert_heightProof 4
cert_coverFacet 0 126
cert_cover_2 0 1 0 2 4 30 126 3
cert_coverFacet 1 542
cert_cover 1 2 1 0 1 3 0 8 2 30 542 30 30 126 4
cert_coverFacet 2 614
cert_cover 2 4 1 0 1 3 0 8 2 102 614 102 30 126 4
cert_coverFacet 3 914
cert_cover_5 3 2 0 3 6 7 146 914 3
cert_coverFacet 4 706
cert_cover_2 4 5 0 6 8 194 706 3
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 932
cert_cover_5 6 3 1 4 6 7 292 932 2
cert_coverFacet 7 792
cert_cover_2 7 3 2 7 8 280 792 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_completion_next_oneprism_m14e11q3_models_0004

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_1950 : Certifies 1950 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1815.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1951 : Certifies 1951 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1816.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1952 : Certifies 1952 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1817.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1953 : Certifies 1953 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1818.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1954 : Certifies 1954 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1819.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1955 : Certifies 1955 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1820.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1956 : Certifies 1956 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1821.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1957 : Certifies 1957 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1822.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1958 : Certifies 1958 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1823.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1959 : Certifies 1959 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1824.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1960 : Certifies 1960 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1825.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1961 : Certifies 1961 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1826.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1962 : Certifies 1962 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1827.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1963 : Certifies 1963 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1828.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1964 : Certifies 1964 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1829.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1965 : Certifies 1965 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1830.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1966 : Certifies 1966 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_completion_next_oneprism_m13e11q3_models_0001.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1967 : Certifies 1967 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_completion_next_oneprism_m13e11q3_models_0002.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1968 : Certifies 1968 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_completion_next_oneprism_m13e11q3_models_0004.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1969 : Certifies 1969 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_completion_next_oneprism_m13e11q3_models_0005.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1970 : Certifies 1970 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_completion_next_oneprism_m13e11q3_models_0006.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1971 : Certifies 1971 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_completion_next_oneprism_m13e11q3_models_0007.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1972 : Certifies 1972 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_completion_next_oneprism_m13e11q3_models_0009.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1973 : Certifies 1973 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_completion_next_oneprism_m13e11q3_models_0010.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1974 : Certifies 1974 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_completion_next_oneprism_m13e11q3_models_0011.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1975 : Certifies 1975 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_completion_next_oneprism_m14e11q3_models_0000.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1976 : Certifies 1976 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_completion_next_oneprism_m14e11q3_models_0001.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1977 : Certifies 1977 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_completion_next_oneprism_m14e11q3_models_0002.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1978 : Certifies 1978 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_completion_next_oneprism_m14e11q3_models_0003.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1979 : Certifies 1979 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_prism_completion_next_oneprism_m14e11q3_models_0004.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B065 (j : Fin 30) :
    Certifies (1950 + j.val) := by
  fin_cases j
  · exact projection_1950
  · exact projection_1951
  · exact projection_1952
  · exact projection_1953
  · exact projection_1954
  · exact projection_1955
  · exact projection_1956
  · exact projection_1957
  · exact projection_1958
  · exact projection_1959
  · exact projection_1960
  · exact projection_1961
  · exact projection_1962
  · exact projection_1963
  · exact projection_1964
  · exact projection_1965
  · exact projection_1966
  · exact projection_1967
  · exact projection_1968
  · exact projection_1969
  · exact projection_1970
  · exact projection_1971
  · exact projection_1972
  · exact projection_1973
  · exact projection_1974
  · exact projection_1975
  · exact projection_1976
  · exact projection_1977
  · exact projection_1978
  · exact projection_1979

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
