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
/- Source: ProjectionCertificates/R_one_six_0722.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0722

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 203, 387, 533, 121, 721, 897, 398, 364, 820, 968, 880, 7, 11, 131, 259, 21, 517, 57, 73, 81, 529, 193, 385, 641, 769, 14, 262, 138, 386, 44, 268, 52, 532, 292, 772, 104, 200, 328, 392, 112, 816, 592, 352, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_203, vertices_387, vertices_533, vertices_121, vertices_721, vertices_897, vertices_398, vertices_364, vertices_820, vertices_968, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_21, vertices_517, vertices_57, vertices_73, vertices_81, vertices_529, vertices_193, vertices_385, vertices_641, vertices_769, vertices_14, vertices_262, vertices_138, vertices_386, vertices_44, vertices_268, vertices_52, vertices_532, vertices_292, vertices_772, vertices_104, vertices_200, vertices_328, vertices_392, vertices_112, vertices_816, vertices_592, vertices_352, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_203), (false, vertices_387), (false, vertices_533), (false, vertices_121), (false, vertices_721), (false, vertices_897), (true, vertices_268), (true, vertices_292), (true, vertices_328), (true, vertices_392), (true, vertices_816), (true, vertices_352), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 13 16 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_775) then 10 else
  if p.val = (false, vertices_203) then 11 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_533) then 1 else
  if p.val = (false, vertices_121) then 15 else
  if p.val = (false, vertices_721) then 17 else
  if p.val = (false, vertices_897) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_816) then 18 else
  if p.val = (true, vertices_352) then 7 else
  if p.val = (true, vertices_832) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 7 8 816
cert_row_4 1 0 1 2 6 7 398 14 3
cert_row_4 2 1 2 4 5 7 364 44 3
cert_row_4 3 2 5 6 7 8 968 200 3
cert_rows
cert_pivot_2 3 0 1 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 1 0 1 2 6 14 398 3
cert_coverFacet 1 364
cert_cover_5 1 2 1 2 4 5 44 364 3
cert_coverFacet 2 820
cert_cover_5 2 0 1 3 4 7 52 820 3
cert_coverFacet 3 968
cert_cover_5 3 3 2 5 6 7 200 968 3
cert_coverFacet 4 880
cert_cover_5 4 0 3 4 5 7 112 880 3
cert_coveringFacets_3
cert_coveringProof_7
cert_certificate 4 5
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0722

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_one_six_0723.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0723

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 203, 387, 597, 121, 961, 398, 812, 564, 232, 936, 752, 7, 11, 131, 259, 21, 517, 57, 73, 81, 193, 577, 385, 769, 14, 262, 138, 386, 44, 268, 52, 532, 548, 772, 104, 168, 808, 200, 392, 112, 560, 592, 224, 672, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_203, vertices_387, vertices_597, vertices_121, vertices_961, vertices_398, vertices_812, vertices_564, vertices_232, vertices_936, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_21, vertices_517, vertices_57, vertices_73, vertices_81, vertices_193, vertices_577, vertices_385, vertices_769, vertices_14, vertices_262, vertices_138, vertices_386, vertices_44, vertices_268, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_168, vertices_808, vertices_200, vertices_392, vertices_112, vertices_560, vertices_592, vertices_224, vertices_672, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_203), (false, vertices_387), (false, vertices_597), (false, vertices_121), (false, vertices_961), (true, vertices_268), (true, vertices_548), (true, vertices_168), (true, vertices_808), (true, vertices_392), (true, vertices_560), (true, vertices_224), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 16 13 18 19 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_775) then 9 else
  if p.val = (false, vertices_203) then 10 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_597) then 12 else
  if p.val = (false, vertices_121) then 15 else
  if p.val = (false, vertices_961) then 20 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_168) then 3 else
  if p.val = (true, vertices_808) then 17 else
  if p.val = (true, vertices_392) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_224) then 6 else
  if p.val = (true, vertices_672) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 13 => Sum.inl 3
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(true, vertices_808), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 14 3
cert_row_2 1 2 4 7 8 808
cert_row_4 2 3 4 5 6 8 752 112 3
cert_rows_3
cert_pivot_3 2 0 3
cert_heightProof 3
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 812
cert_cover_5 1 1 1 2 4 7 44 812 3
cert_coverFacet 2 564
cert_cover_2 2 3 1 4 8 52 564 3
cert_coverFacet 3 232
cert_cover_2 3 4 2 5 6 104 232 3
cert_coverFacet 4 936
cert_cover_5 4 1 2 4 6 7 168 936 3
cert_coverFacet 5 752
cert_cover_5 5 2 3 4 5 6 112 752 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0723

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_one_six_0724.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0724

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 203, 387, 597, 121, 961, 398, 300, 820, 744, 936, 624, 7, 11, 131, 259, 21, 517, 57, 73, 81, 193, 577, 385, 769, 14, 262, 138, 386, 44, 268, 52, 532, 292, 772, 104, 680, 296, 200, 392, 112, 560, 592, 608, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_203, vertices_387, vertices_597, vertices_121, vertices_961, vertices_398, vertices_300, vertices_820, vertices_744, vertices_936, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_21, vertices_517, vertices_57, vertices_73, vertices_81, vertices_193, vertices_577, vertices_385, vertices_769, vertices_14, vertices_262, vertices_138, vertices_386, vertices_44, vertices_268, vertices_52, vertices_532, vertices_292, vertices_772, vertices_104, vertices_680, vertices_296, vertices_200, vertices_392, vertices_112, vertices_560, vertices_592, vertices_608, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_203), (false, vertices_387), (false, vertices_597), (false, vertices_121), (false, vertices_961), (true, vertices_268), (true, vertices_292), (true, vertices_680), (true, vertices_296), (true, vertices_392), (true, vertices_560), (true, vertices_608), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 16 13 18 19 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_775) then 9 else
  if p.val = (false, vertices_203) then 10 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_597) then 12 else
  if p.val = (false, vertices_121) then 15 else
  if p.val = (false, vertices_961) then 20 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_680) then 17 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_392) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_608) then 6 else
  if p.val = (true, vertices_800) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 13 => Sum.inl 3
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(true, vertices_680), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 14 3
cert_row_2 1 2 4 6 8 680
cert_row_4 2 1 3 4 7 8 820 52 3
cert_rows_3
cert_pivot_3 2 0 1
cert_heightProof 3
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 300
cert_cover_2 1 2 1 4 7 44 300 3
cert_coverFacet 2 820
cert_cover_5 2 2 1 3 4 7 52 820 3
cert_coverFacet 3 744
cert_cover_5 3 1 2 4 5 6 104 744 3
cert_coverFacet 4 936
cert_cover_5 4 1 2 4 6 7 680 936 3
cert_coverFacet 5 624
cert_cover_2 5 4 3 5 8 112 624 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0724

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_one_six_0725.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0725

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 203, 387, 597, 121, 961, 398, 428, 820, 232, 752, 928, 7, 11, 131, 259, 21, 517, 57, 73, 81, 193, 577, 385, 769, 14, 262, 138, 386, 44, 396, 52, 532, 292, 772, 104, 168, 200, 112, 560, 592, 224, 416, 672, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_203, vertices_387, vertices_597, vertices_121, vertices_961, vertices_398, vertices_428, vertices_820, vertices_232, vertices_752, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_21, vertices_517, vertices_57, vertices_73, vertices_81, vertices_193, vertices_577, vertices_385, vertices_769, vertices_14, vertices_262, vertices_138, vertices_386, vertices_44, vertices_396, vertices_52, vertices_532, vertices_292, vertices_772, vertices_104, vertices_168, vertices_200, vertices_112, vertices_560, vertices_592, vertices_224, vertices_416, vertices_672, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_203), (false, vertices_387), (false, vertices_597), (false, vertices_121), (false, vertices_961), (true, vertices_396), (true, vertices_292), (true, vertices_168), (true, vertices_560), (true, vertices_224), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 14 17 18 19 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_775) then 9 else
  if p.val = (false, vertices_203) then 10 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_597) then 12 else
  if p.val = (false, vertices_121) then 16 else
  if p.val = (false, vertices_961) then 20 else
  if p.val = (true, vertices_396) then 13 else
  if p.val = (true, vertices_292) then 1 else
  if p.val = (true, vertices_168) then 2 else
  if p.val = (true, vertices_560) then 3 else
  if p.val = (true, vertices_224) then 4 else
  if p.val = (true, vertices_416) then 5 else
  if p.val = (true, vertices_672) then 6 else
  if p.val = (true, vertices_800) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
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
cert_row_2 0 1 2 6 7 396
cert_row_4 1 1 3 4 7 8 820 52 3
cert_row_4 2 3 4 5 6 8 752 112 3
cert_rows_3
cert_pivot_3 1 2 3
cert_heightProof 3
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 428
cert_cover_5 1 0 1 2 4 6 44 428 3
cert_coverFacet 2 820
cert_cover_5 2 1 1 3 4 7 52 820 3
cert_coverFacet 3 232
cert_cover_2 3 4 2 5 6 104 232 3
cert_coverFacet 4 752
cert_cover_5 4 2 3 4 5 6 112 752 3
cert_coverFacet 5 928
cert_cover_2 5 6 4 7 8 416 928 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0725

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_one_six_0726.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0726

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 203, 387, 597, 121, 961, 398, 428, 820, 232, 496, 848, 7, 11, 131, 259, 21, 517, 57, 73, 81, 193, 577, 385, 769, 14, 262, 138, 386, 44, 396, 52, 532, 292, 772, 104, 168, 200, 112, 304, 336, 592, 784, 224, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_203, vertices_387, vertices_597, vertices_121, vertices_961, vertices_398, vertices_428, vertices_820, vertices_232, vertices_496, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_21, vertices_517, vertices_57, vertices_73, vertices_81, vertices_193, vertices_577, vertices_385, vertices_769, vertices_14, vertices_262, vertices_138, vertices_386, vertices_44, vertices_396, vertices_52, vertices_532, vertices_292, vertices_772, vertices_104, vertices_168, vertices_200, vertices_112, vertices_304, vertices_336, vertices_592, vertices_784, vertices_224, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_203), (false, vertices_387), (false, vertices_597), (false, vertices_121), (false, vertices_961), (true, vertices_396), (true, vertices_292), (true, vertices_168), (true, vertices_304), (true, vertices_336), (true, vertices_784), (true, vertices_224), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 14 17 18 19 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_775) then 9 else
  if p.val = (false, vertices_203) then 10 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_597) then 12 else
  if p.val = (false, vertices_121) then 16 else
  if p.val = (false, vertices_961) then 20 else
  if p.val = (true, vertices_396) then 13 else
  if p.val = (true, vertices_292) then 1 else
  if p.val = (true, vertices_168) then 2 else
  if p.val = (true, vertices_304) then 3 else
  if p.val = (true, vertices_336) then 4 else
  if p.val = (true, vertices_784) then 5 else
  if p.val = (true, vertices_224) then 6 else
  if p.val = (true, vertices_416) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
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
cert_row_2 0 1 2 6 7 396
cert_row_4 1 1 3 4 7 8 820 52 3
cert_row_4 2 3 4 5 6 7 496 112 3
cert_rows_3
cert_pivot_3 1 2 3
cert_heightProof 3
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 428
cert_cover_5 1 0 1 2 4 6 44 428 3
cert_coverFacet 2 820
cert_cover_5 2 1 1 3 4 7 52 820 3
cert_coverFacet 3 232
cert_cover_2 3 4 2 5 6 104 232 3
cert_coverFacet 4 496
cert_cover_5 4 2 3 4 5 6 112 496 3
cert_coverFacet 5 848
cert_cover_2 5 5 3 7 8 336 848 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0726

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_one_six_0727.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0727

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 203, 387, 597, 121, 961, 398, 428, 820, 744, 624, 928, 7, 11, 131, 259, 21, 517, 57, 73, 81, 193, 577, 385, 769, 14, 262, 138, 386, 44, 396, 52, 532, 292, 772, 104, 168, 200, 112, 560, 592, 608, 416, 672, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_203, vertices_387, vertices_597, vertices_121, vertices_961, vertices_398, vertices_428, vertices_820, vertices_744, vertices_624, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_21, vertices_517, vertices_57, vertices_73, vertices_81, vertices_193, vertices_577, vertices_385, vertices_769, vertices_14, vertices_262, vertices_138, vertices_386, vertices_44, vertices_396, vertices_52, vertices_532, vertices_292, vertices_772, vertices_104, vertices_168, vertices_200, vertices_112, vertices_560, vertices_592, vertices_608, vertices_416, vertices_672, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_203), (false, vertices_387), (false, vertices_597), (false, vertices_121), (false, vertices_961), (true, vertices_396), (true, vertices_292), (true, vertices_168), (true, vertices_560), (true, vertices_608), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 14 17 18 19 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_775) then 9 else
  if p.val = (false, vertices_203) then 10 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_597) then 12 else
  if p.val = (false, vertices_121) then 16 else
  if p.val = (false, vertices_961) then 20 else
  if p.val = (true, vertices_396) then 13 else
  if p.val = (true, vertices_292) then 1 else
  if p.val = (true, vertices_168) then 2 else
  if p.val = (true, vertices_560) then 3 else
  if p.val = (true, vertices_608) then 4 else
  if p.val = (true, vertices_416) then 5 else
  if p.val = (true, vertices_672) then 6 else
  if p.val = (true, vertices_800) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
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
cert_row_4 0 1 3 4 7 8 820 52 3
cert_row_2 1 1 2 6 7 396
cert_row_4 2 2 4 5 6 8 744 104 3
cert_rows_3
cert_pivot_3 1 3 2
cert_heightProof 3
cert_coverFacet 0 398
cert_cover_5 0 1 0 1 2 6 14 398 3
cert_coverFacet 1 428
cert_cover_5 1 1 1 2 4 6 44 428 3
cert_coverFacet 2 820
cert_cover_5 2 0 1 3 4 7 52 820 3
cert_coverFacet 3 744
cert_cover_5 3 2 2 4 5 6 104 744 3
cert_coverFacet 4 624
cert_cover_2 4 4 3 5 8 112 624 3
cert_coverFacet 5 928
cert_cover_2 5 6 4 7 8 416 928 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0727

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_one_six_0728.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0728

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 203, 387, 277, 121, 465, 654, 898, 812, 372, 744, 992, 7, 11, 131, 259, 21, 261, 57, 73, 81, 273, 193, 385, 14, 518, 138, 386, 642, 770, 44, 524, 52, 276, 292, 772, 104, 552, 200, 648, 112, 336, 736, 352, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_203, vertices_387, vertices_277, vertices_121, vertices_465, vertices_654, vertices_898, vertices_812, vertices_372, vertices_744, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_193, vertices_385, vertices_14, vertices_518, vertices_138, vertices_386, vertices_642, vertices_770, vertices_44, vertices_524, vertices_52, vertices_276, vertices_292, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_112, vertices_336, vertices_736, vertices_352, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_203), (false, vertices_387), (false, vertices_277), (false, vertices_121), (false, vertices_465), (true, vertices_642), (true, vertices_524), (true, vertices_292), (true, vertices_552), (true, vertices_648), (true, vertices_736), (true, vertices_352), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 14 17 19 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_775) then 11 else
  if p.val = (false, vertices_203) then 12 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_277) then 1 else
  if p.val = (false, vertices_121) then 16 else
  if p.val = (false, vertices_465) then 18 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_736) then 20 else
  if p.val = (true, vertices_352) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inr ⟨(true, vertices_736), by decide +kernel⟩
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 14 3
cert_row_2 1 4 5 6 8 736
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 1 3 4 5 7 372 52 3
cert_rows
cert_pivot_2 0 6 2 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 898
cert_cover_2 1 6 0 7 8 386 898 3
cert_coverFacet 2 812
cert_cover_5 2 2 1 2 4 7 44 812 3
cert_coverFacet 3 372
cert_cover_5 3 3 1 3 4 5 52 372 3
cert_coverFacet 4 744
cert_cover_5 4 1 2 4 5 6 104 744 3
cert_coverFacet 5 992
cert_cover_5 5 1 4 5 6 7 736 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0728

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_one_six_0729.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0729

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 203, 387, 277, 121, 465, 654, 898, 620, 820, 968, 880, 7, 11, 131, 259, 21, 261, 57, 73, 81, 273, 193, 385, 14, 518, 138, 386, 642, 770, 44, 524, 52, 276, 548, 772, 104, 200, 584, 648, 112, 816, 336, 608, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_203, vertices_387, vertices_277, vertices_121, vertices_465, vertices_654, vertices_898, vertices_620, vertices_820, vertices_968, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_193, vertices_385, vertices_14, vertices_518, vertices_138, vertices_386, vertices_642, vertices_770, vertices_44, vertices_524, vertices_52, vertices_276, vertices_548, vertices_772, vertices_104, vertices_200, vertices_584, vertices_648, vertices_112, vertices_816, vertices_336, vertices_608, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_203), (false, vertices_387), (false, vertices_277), (false, vertices_121), (false, vertices_465), (true, vertices_642), (true, vertices_524), (true, vertices_548), (true, vertices_584), (true, vertices_648), (true, vertices_816), (true, vertices_608), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 14 17 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_775) then 11 else
  if p.val = (false, vertices_203) then 12 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_277) then 1 else
  if p.val = (false, vertices_121) then 16 else
  if p.val = (false, vertices_465) then 18 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_816) then 19 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_832) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 7 8 816
cert_row_4 1 0 1 2 6 8 654 14 3
cert_row_4 2 1 2 4 5 8 620 44 3
cert_row_4 3 2 5 6 7 8 968 200 3
cert_rows
cert_pivot_2 3 0 1 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 1 0 1 2 6 14 654 3
cert_coverFacet 1 898
cert_cover_2 1 6 0 7 8 386 898 3
cert_coverFacet 2 620
cert_cover_5 2 2 1 2 4 5 44 620 3
cert_coverFacet 3 820
cert_cover_5 3 0 1 3 4 7 52 820 3
cert_coverFacet 4 968
cert_cover_5 4 3 2 5 6 7 200 968 3
cert_coverFacet 5 880
cert_cover_5 5 0 3 4 5 7 112 880 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0729

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_one_six_0730.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0730

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 775, 203, 387, 789, 121, 465, 654, 898, 620, 564, 968, 880, 7, 11, 131, 259, 21, 773, 57, 73, 81, 273, 193, 385, 14, 518, 138, 386, 642, 770, 44, 524, 52, 532, 548, 104, 200, 584, 648, 112, 560, 336, 784, 608, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_775, vertices_203, vertices_387, vertices_789, vertices_121, vertices_465, vertices_654, vertices_898, vertices_620, vertices_564, vertices_968, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_21, vertices_773, vertices_57, vertices_73, vertices_81, vertices_273, vertices_193, vertices_385, vertices_14, vertices_518, vertices_138, vertices_386, vertices_642, vertices_770, vertices_44, vertices_524, vertices_52, vertices_532, vertices_548, vertices_104, vertices_200, vertices_584, vertices_648, vertices_112, vertices_560, vertices_336, vertices_784, vertices_608, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_775), (false, vertices_203), (false, vertices_387), (false, vertices_789), (false, vertices_121), (false, vertices_465), (true, vertices_642), (true, vertices_524), (true, vertices_548), (true, vertices_584), (true, vertices_648), (true, vertices_560), (true, vertices_608), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 15 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_775) then 13 else
  if p.val = (false, vertices_203) then 11 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_789) then 14 else
  if p.val = (false, vertices_121) then 17 else
  if p.val = (false, vertices_465) then 19 else
  if p.val = (true, vertices_642) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_584) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_832) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 14 3
cert_row_4 1 1 2 4 5 8 620 44 3
cert_row_4 2 2 5 6 7 8 968 200 3
cert_row_4 3 3 4 5 7 8 880 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 14 654 3
cert_coverFacet 1 898
cert_cover_2 1 6 0 7 8 386 898 3
cert_coverFacet 2 620
cert_cover_5 2 1 1 2 4 5 44 620 3
cert_coverFacet 3 564
cert_cover_2 3 3 1 4 8 52 564 3
cert_coverFacet 4 968
cert_cover_5 4 2 2 5 6 7 200 968 3
cert_coverFacet 5 880
cert_cover_5 5 3 3 4 5 7 112 880 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0730

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_one_six_0734.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0734

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 213, 121, 270, 906, 812, 436, 616, 712, 880, 976, 7, 11, 131, 21, 133, 57, 73, 81, 193, 14, 262, 138, 266, 386, 44, 268, 52, 148, 292, 388, 104, 552, 200, 584, 648, 776, 112, 304, 208, 848, 400, 608, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_213, vertices_121, vertices_270, vertices_906, vertices_812, vertices_436, vertices_616, vertices_712, vertices_880, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_133, vertices_57, vertices_73, vertices_81, vertices_193, vertices_14, vertices_262, vertices_138, vertices_266, vertices_386, vertices_44, vertices_268, vertices_52, vertices_148, vertices_292, vertices_388, vertices_104, vertices_552, vertices_200, vertices_584, vertices_648, vertices_776, vertices_112, vertices_304, vertices_208, vertices_848, vertices_400, vertices_608, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_213), (false, vertices_121), (true, vertices_266), (true, vertices_268), (true, vertices_292), (true, vertices_552), (true, vertices_584), (true, vertices_648), (true, vertices_776), (true, vertices_304), (true, vertices_848), (true, vertices_400), (true, vertices_608), (true, vertices_800), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 19 else
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_203) then 15 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_121) then 20 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_584) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_848) then 22 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(true, vertices_848), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 5 7 8 848
cert_row_4 1 0 2 6 7 8 906 138 3
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 1 3 4 6 7 436 52 3
cert_rows
cert_pivot_2 5 0 2 1
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 906
cert_cover_5 1 1 0 2 6 7 138 906 3
cert_coverFacet 2 812
cert_cover_5 2 2 1 2 4 7 44 812 3
cert_coverFacet 3 436
cert_cover_5 3 3 1 3 4 6 52 436 3
cert_coverFacet 4 616
cert_cover_2 4 4 2 5 8 104 616 3
cert_coverFacet 5 712
cert_cover_2 5 5 2 6 8 200 712 3
cert_coverFacet 6 880
cert_cover_5 6 0 3 4 5 7 112 880 3
cert_coverFacet 7 976
cert_cover_5 7 0 3 5 6 7 208 976 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0734

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_one_six_0735.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0735

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 213, 121, 270, 906, 300, 820, 916, 872, 712, 752, 7, 11, 131, 21, 133, 57, 73, 81, 193, 14, 262, 138, 266, 386, 44, 268, 52, 148, 788, 292, 388, 104, 296, 200, 584, 648, 776, 112, 560, 208, 656, 608, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_213, vertices_121, vertices_270, vertices_906, vertices_300, vertices_820, vertices_916, vertices_872, vertices_712, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_133, vertices_57, vertices_73, vertices_81, vertices_193, vertices_14, vertices_262, vertices_138, vertices_266, vertices_386, vertices_44, vertices_268, vertices_52, vertices_148, vertices_788, vertices_292, vertices_388, vertices_104, vertices_296, vertices_200, vertices_584, vertices_648, vertices_776, vertices_112, vertices_560, vertices_208, vertices_656, vertices_608, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_213), (false, vertices_121), (true, vertices_266), (true, vertices_268), (true, vertices_788), (true, vertices_292), (true, vertices_296), (true, vertices_584), (true, vertices_648), (true, vertices_776), (true, vertices_560), (true, vertices_656), (true, vertices_608), (true, vertices_800), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 19 16 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_203) then 15 else
  if p.val = (false, vertices_213) then 20 else
  if p.val = (false, vertices_121) then 18 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_788) then 21 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_584) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_656) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_788), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 7 8 788
cert_row_4 1 0 2 6 7 8 906 138 3
cert_row_4 2 2 4 5 7 8 872 104 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 906
cert_cover_5 1 1 0 2 6 7 138 906 3
cert_coverFacet 2 300
cert_cover_2 2 2 1 4 7 44 300 3
cert_coverFacet 3 820
cert_cover_5 3 0 1 3 4 7 52 820 3
cert_coverFacet 4 916
cert_cover_5 4 0 1 3 6 7 148 916 3
cert_coverFacet 5 872
cert_cover_5 5 2 2 4 5 7 104 872 3
cert_coverFacet 6 712
cert_cover_2 6 5 2 6 8 200 712 3
cert_coverFacet 7 752
cert_cover_5 7 3 3 4 5 6 112 752 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0735

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_one_six_0736.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0736

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 661, 121, 721, 270, 906, 300, 628, 932, 872, 712, 7, 11, 131, 21, 133, 57, 73, 81, 657, 193, 14, 262, 138, 266, 386, 44, 268, 52, 532, 292, 548, 388, 644, 104, 296, 200, 584, 648, 776, 112, 592, 608, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_661, vertices_121, vertices_721, vertices_270, vertices_906, vertices_300, vertices_628, vertices_932, vertices_872, vertices_712] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_133, vertices_57, vertices_73, vertices_81, vertices_657, vertices_193, vertices_14, vertices_262, vertices_138, vertices_266, vertices_386, vertices_44, vertices_268, vertices_52, vertices_532, vertices_292, vertices_548, vertices_388, vertices_644, vertices_104, vertices_296, vertices_200, vertices_584, vertices_648, vertices_776, vertices_112, vertices_592, vertices_608, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_661), (false, vertices_121), (false, vertices_721), (true, vertices_266), (true, vertices_268), (true, vertices_292), (true, vertices_548), (true, vertices_296), (true, vertices_584), (true, vertices_648), (true, vertices_776), (true, vertices_608), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 15 18 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_203) then 13 else
  if p.val = (false, vertices_661) then 19 else
  if p.val = (false, vertices_121) then 17 else
  if p.val = (false, vertices_721) then 20 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 6 7 8 906 138 3
cert_row_4 1 1 3 4 5 8 628 52 3
cert_row_4 2 1 4 6 7 8 932 292 2
cert_row_4 3 2 4 5 7 8 872 104 3
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 300
cert_cover_2 2 2 1 4 7 44 300 3
cert_coverFacet 3 628
cert_cover_5 3 1 1 3 4 5 52 628 3
cert_coverFacet 4 932
cert_cover_5 4 2 1 4 6 7 292 932 2
cert_coverFacet 5 872
cert_cover_5 5 3 2 4 5 7 104 872 3
cert_coverFacet 6 712
cert_cover_2 6 5 2 6 8 200 712 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0736

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_one_six_0737.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0737

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 267, 899, 117, 809, 737, 398, 220, 312, 472, 880, 960, 7, 11, 131, 259, 53, 69, 41, 265, 97, 545, 193, 641, 769, 14, 134, 266, 386, 28, 140, 84, 196, 56, 216, 280, 296, 392, 112, 304, 336, 608, 800, 448, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_267, vertices_899, vertices_117, vertices_809, vertices_737, vertices_398, vertices_220, vertices_312, vertices_472, vertices_880, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_53, vertices_69, vertices_41, vertices_265, vertices_97, vertices_545, vertices_193, vertices_641, vertices_769, vertices_14, vertices_134, vertices_266, vertices_386, vertices_28, vertices_140, vertices_84, vertices_196, vertices_56, vertices_216, vertices_280, vertices_296, vertices_392, vertices_112, vertices_304, vertices_336, vertices_608, vertices_800, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_267), (false, vertices_899), (false, vertices_117), (false, vertices_809), (false, vertices_737), (true, vertices_140), (true, vertices_216), (true, vertices_280), (true, vertices_392), (true, vertices_304), (true, vertices_336), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 14 17 18 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_199) then 9 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_899) then 10 else
  if p.val = (false, vertices_117) then 13 else
  if p.val = (false, vertices_809) then 15 else
  if p.val = (false, vertices_737) then 19 else
  if p.val = (true, vertices_140) then 1 else
  if p.val = (true, vertices_216) then 16 else
  if p.val = (true, vertices_280) then 2 else
  if p.val = (true, vertices_392) then 3 else
  if p.val = (true, vertices_304) then 4 else
  if p.val = (true, vertices_336) then 5 else
  if p.val = (true, vertices_448) then 6 else
  if p.val = (true, vertices_832) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inl 4
  | 19 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 14 3
cert_row_2 1 2 3 5 6 216
cert_row_4 2 3 4 5 7 8 880 112 3
cert_rows_3
cert_pivot_3 2 0 3
cert_heightProof 3
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 220
cert_cover_5 1 1 1 2 3 5 28 220 3
cert_coverFacet 2 312
cert_cover_2 2 3 2 4 7 56 312 3
cert_coverFacet 3 472
cert_cover_5 3 1 2 3 5 7 216 472 3
cert_coverFacet 4 880
cert_cover_5 4 2 3 4 5 7 112 880 3
cert_coverFacet 5 960
cert_cover_2 5 6 5 7 8 448 960 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0737

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_one_six_0738.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0738

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 213, 121, 270, 906, 812, 308, 404, 744, 880, 976, 7, 11, 131, 21, 133, 57, 73, 81, 193, 14, 262, 138, 266, 386, 44, 268, 52, 148, 276, 292, 388, 104, 552, 200, 648, 776, 112, 304, 208, 848, 400, 608, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_213, vertices_121, vertices_270, vertices_906, vertices_812, vertices_308, vertices_404, vertices_744, vertices_880, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_133, vertices_57, vertices_73, vertices_81, vertices_193, vertices_14, vertices_262, vertices_138, vertices_266, vertices_386, vertices_44, vertices_268, vertices_52, vertices_148, vertices_276, vertices_292, vertices_388, vertices_104, vertices_552, vertices_200, vertices_648, vertices_776, vertices_112, vertices_304, vertices_208, vertices_848, vertices_400, vertices_608, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_213), (false, vertices_121), (true, vertices_266), (true, vertices_268), (true, vertices_276), (true, vertices_292), (true, vertices_552), (true, vertices_648), (true, vertices_776), (true, vertices_304), (true, vertices_848), (true, vertices_400), (true, vertices_608), (true, vertices_800), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 19 else
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_203) then 15 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_121) then 20 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_292) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_848) then 22 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(true, vertices_848), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 5 7 8 848
cert_row_4 1 0 2 6 7 8 906 138 3
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 3 0 1 2
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 906
cert_cover_5 1 1 0 2 6 7 138 906 3
cert_coverFacet 2 812
cert_cover_5 2 2 1 2 4 7 44 812 3
cert_coverFacet 3 308
cert_cover_2 3 3 1 4 7 52 308 3
cert_coverFacet 4 404
cert_cover_2 4 3 1 6 7 148 404 3
cert_coverFacet 5 744
cert_cover_5 5 3 2 4 5 6 104 744 3
cert_coverFacet 6 880
cert_cover_5 6 0 3 4 5 7 112 880 3
cert_coverFacet 7 976
cert_cover_5 7 0 3 5 6 7 208 976 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0738

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_one_six_0739.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0739

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 213, 121, 270, 906, 812, 820, 404, 744, 624, 976, 7, 11, 131, 21, 133, 57, 73, 81, 193, 14, 262, 138, 266, 386, 44, 268, 52, 148, 276, 804, 388, 104, 552, 200, 648, 776, 112, 560, 208, 592, 400, 784, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_213, vertices_121, vertices_270, vertices_906, vertices_812, vertices_820, vertices_404, vertices_744, vertices_624, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_133, vertices_57, vertices_73, vertices_81, vertices_193, vertices_14, vertices_262, vertices_138, vertices_266, vertices_386, vertices_44, vertices_268, vertices_52, vertices_148, vertices_276, vertices_804, vertices_388, vertices_104, vertices_552, vertices_200, vertices_648, vertices_776, vertices_112, vertices_560, vertices_208, vertices_592, vertices_400, vertices_784, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_213), (false, vertices_121), (true, vertices_266), (true, vertices_268), (true, vertices_276), (true, vertices_804), (true, vertices_552), (true, vertices_648), (true, vertices_776), (true, vertices_560), (true, vertices_592), (true, vertices_400), (true, vertices_784), (true, vertices_608), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 20 else
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_203) then 15 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_121) then 21 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_804) then 18 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_648) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_804), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 7 8 804
cert_row_4 1 0 2 6 7 8 906 138 3
cert_row_4 2 2 4 5 6 8 744 104 3
cert_row_4 3 3 5 6 7 8 976 208 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 906
cert_cover_5 1 1 0 2 6 7 138 906 3
cert_coverFacet 2 812
cert_cover_5 2 0 1 2 4 7 44 812 3
cert_coverFacet 3 820
cert_cover_5 3 0 1 3 4 7 52 820 3
cert_coverFacet 4 404
cert_cover_2 4 3 1 6 7 148 404 3
cert_coverFacet 5 744
cert_cover_5 5 2 2 4 5 6 104 744 3
cert_coverFacet 6 624
cert_cover_2 6 4 3 5 8 112 624 3
cert_coverFacet 7 976
cert_cover_5 7 3 3 5 6 7 208 976 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0739

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_one_six_0740.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0740

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 213, 121, 782, 906, 556, 820, 404, 744, 624, 976, 7, 11, 131, 21, 133, 57, 73, 81, 193, 14, 262, 138, 778, 386, 44, 524, 52, 148, 276, 548, 388, 772, 104, 552, 200, 648, 112, 560, 208, 592, 400, 784, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_213, vertices_121, vertices_782, vertices_906, vertices_556, vertices_820, vertices_404, vertices_744, vertices_624, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_133, vertices_57, vertices_73, vertices_81, vertices_193, vertices_14, vertices_262, vertices_138, vertices_778, vertices_386, vertices_44, vertices_524, vertices_52, vertices_148, vertices_276, vertices_548, vertices_388, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_112, vertices_560, vertices_208, vertices_592, vertices_400, vertices_784, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_213), (false, vertices_121), (true, vertices_778), (true, vertices_524), (true, vertices_276), (true, vertices_548), (true, vertices_772), (true, vertices_552), (true, vertices_648), (true, vertices_560), (true, vertices_592), (true, vertices_400), (true, vertices_784), (true, vertices_608), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 13 22 16 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_203) then 20 else
  if p.val = (false, vertices_213) then 15 else
  if p.val = (false, vertices_121) then 18 else
  if p.val = (true, vertices_778) then 21 else
  if p.val = (true, vertices_524) then 0 else
  if p.val = (true, vertices_276) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_772) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 7 8 778
cert_row_4 1 1 3 4 7 8 820 52 3
cert_row_4 2 2 4 5 6 8 744 104 3
cert_row_4 3 3 5 6 7 8 976 208 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 820
cert_cover_5 3 1 1 3 4 7 52 820 3
cert_coverFacet 4 404
cert_cover_2 4 3 1 6 7 148 404 3
cert_coverFacet 5 744
cert_cover_5 5 2 2 4 5 6 104 744 3
cert_coverFacet 6 624
cert_cover_2 6 4 3 5 8 112 624 3
cert_coverFacet 7 976
cert_cover_5 7 3 3 5 6 7 208 976 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0740

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_one_six_0741.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0741

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 213, 121, 782, 906, 556, 820, 404, 744, 496, 928, 7, 11, 131, 21, 133, 57, 73, 81, 193, 14, 262, 138, 778, 386, 44, 524, 52, 148, 276, 548, 388, 772, 104, 552, 200, 648, 112, 304, 208, 400, 224, 416, 672, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_213, vertices_121, vertices_782, vertices_906, vertices_556, vertices_820, vertices_404, vertices_744, vertices_496, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_133, vertices_57, vertices_73, vertices_81, vertices_193, vertices_14, vertices_262, vertices_138, vertices_778, vertices_386, vertices_44, vertices_524, vertices_52, vertices_148, vertices_276, vertices_548, vertices_388, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_112, vertices_304, vertices_208, vertices_400, vertices_224, vertices_416, vertices_672, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_213), (false, vertices_121), (true, vertices_778), (true, vertices_524), (true, vertices_276), (true, vertices_548), (true, vertices_772), (true, vertices_552), (true, vertices_648), (true, vertices_304), (true, vertices_400), (true, vertices_224), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 13 22 16 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_391) then 14 else
  if p.val = (false, vertices_203) then 20 else
  if p.val = (false, vertices_213) then 15 else
  if p.val = (false, vertices_121) then 18 else
  if p.val = (true, vertices_778) then 21 else
  if p.val = (true, vertices_524) then 0 else
  if p.val = (true, vertices_276) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_772) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_400) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_800) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 7 8 778
cert_row_4 1 1 3 4 7 8 820 52 3
cert_row_4 2 2 4 5 6 8 744 104 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 820
cert_cover_5 3 1 1 3 4 7 52 820 3
cert_coverFacet 4 404
cert_cover_2 4 3 1 6 7 148 404 3
cert_coverFacet 5 744
cert_cover_5 5 2 2 4 5 6 104 744 3
cert_coverFacet 6 496
cert_cover_5 6 3 3 4 5 6 112 496 3
cert_coverFacet 7 928
cert_cover_2 7 6 4 7 8 416 928 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0741

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_one_six_0742.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0742

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 789, 121, 465, 270, 906, 812, 628, 616, 712, 976, 7, 11, 131, 21, 261, 57, 73, 81, 273, 193, 385, 14, 262, 138, 266, 386, 44, 268, 52, 532, 548, 772, 104, 552, 200, 584, 648, 776, 112, 464, 592, 784, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_789, vertices_121, vertices_465, vertices_270, vertices_906, vertices_812, vertices_628, vertices_616, vertices_712, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_193, vertices_385, vertices_14, vertices_262, vertices_138, vertices_266, vertices_386, vertices_44, vertices_268, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_584, vertices_648, vertices_776, vertices_112, vertices_464, vertices_592, vertices_784, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_789), (false, vertices_121), (false, vertices_465), (true, vertices_266), (true, vertices_268), (true, vertices_548), (true, vertices_552), (true, vertices_584), (true, vertices_648), (true, vertices_776), (true, vertices_592), (true, vertices_608), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 16 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_203) then 13 else
  if p.val = (false, vertices_789) then 15 else
  if p.val = (false, vertices_121) then 18 else
  if p.val = (false, vertices_465) then 20 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_584) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 6 7 8 906 138 3
cert_row_2 1 3 5 6 7 464
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 0 6 2 1
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 812
cert_cover_5 2 2 1 2 4 7 44 812 3
cert_coverFacet 3 628
cert_cover_5 3 3 1 3 4 5 52 628 3
cert_coverFacet 4 616
cert_cover_2 4 4 2 5 8 104 616 3
cert_coverFacet 5 712
cert_cover_2 5 5 2 6 8 200 712 3
cert_coverFacet 6 976
cert_cover_5 6 1 3 5 6 8 464 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0742

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_one_six_0743.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0743

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 789, 121, 465, 270, 906, 556, 780, 628, 744, 976, 7, 11, 131, 21, 261, 57, 73, 81, 273, 193, 385, 14, 262, 138, 266, 386, 44, 268, 524, 52, 532, 548, 772, 104, 552, 200, 648, 776, 112, 464, 592, 784, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_789, vertices_121, vertices_465, vertices_270, vertices_906, vertices_556, vertices_780, vertices_628, vertices_744, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_193, vertices_385, vertices_14, vertices_262, vertices_138, vertices_266, vertices_386, vertices_44, vertices_268, vertices_524, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_776, vertices_112, vertices_464, vertices_592, vertices_784, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_789), (false, vertices_121), (false, vertices_465), (true, vertices_266), (true, vertices_268), (true, vertices_524), (true, vertices_548), (true, vertices_552), (true, vertices_648), (true, vertices_776), (true, vertices_592), (true, vertices_608), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 16 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_203) then 13 else
  if p.val = (false, vertices_789) then 15 else
  if p.val = (false, vertices_121) then 18 else
  if p.val = (false, vertices_465) then 20 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 6 7 8 906 138 3
cert_row_2 1 3 5 6 7 464
cert_row_4 2 1 3 4 5 8 628 52 3
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 780
cert_cover_2 3 2 1 7 8 268 780 3
cert_coverFacet 4 628
cert_cover_5 4 2 1 3 4 5 52 628 3
cert_coverFacet 5 744
cert_cover_5 5 3 2 4 5 6 104 744 3
cert_coverFacet 6 976
cert_cover_5 6 1 3 5 6 8 464 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0743

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_one_six_0744.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0744

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 341, 121, 961, 270, 906, 556, 780, 820, 744, 880, 7, 11, 131, 21, 261, 57, 73, 81, 193, 321, 385, 14, 262, 138, 266, 386, 44, 268, 524, 52, 276, 548, 772, 104, 552, 200, 648, 776, 112, 816, 336, 608, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_341, vertices_121, vertices_961, vertices_270, vertices_906, vertices_556, vertices_780, vertices_820, vertices_744, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_193, vertices_321, vertices_385, vertices_14, vertices_262, vertices_138, vertices_266, vertices_386, vertices_44, vertices_268, vertices_524, vertices_52, vertices_276, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_776, vertices_112, vertices_816, vertices_336, vertices_608, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_341), (false, vertices_121), (false, vertices_961), (true, vertices_266), (true, vertices_268), (true, vertices_524), (true, vertices_548), (true, vertices_772), (true, vertices_552), (true, vertices_648), (true, vertices_776), (true, vertices_816), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 14 17 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 10 else
  if p.val = (false, vertices_203) then 11 else
  if p.val = (false, vertices_341) then 13 else
  if p.val = (false, vertices_121) then 16 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_524) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_816) then 18 else
  if p.val = (true, vertices_608) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
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
cert_row_4 1 0 2 6 7 8 906 138 3
cert_row_4 2 2 4 5 6 8 744 104 3
cert_rows_3
cert_pivot_3 0 3 2
cert_heightProof 3
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 906
cert_cover_5 1 1 0 2 6 7 138 906 3
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 780
cert_cover_2 3 2 1 7 8 268 780 3
cert_coverFacet 4 820
cert_cover_5 4 0 1 3 4 7 52 820 3
cert_coverFacet 5 744
cert_cover_5 5 2 2 4 5 6 104 744 3
cert_coverFacet 6 880
cert_cover_5 6 0 3 4 5 7 112 880 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0744

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_one_six_0745.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0745

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 269, 905, 278, 122, 722, 914, 812, 308, 744, 880, 7, 11, 131, 13, 261, 137, 265, 385, 22, 262, 58, 74, 82, 658, 274, 194, 386, 44, 268, 52, 276, 292, 104, 552, 200, 648, 776, 112, 304, 592, 784, 608, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_269, vertices_905, vertices_278, vertices_122, vertices_722, vertices_914, vertices_812, vertices_308, vertices_744, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_13, vertices_261, vertices_137, vertices_265, vertices_385, vertices_22, vertices_262, vertices_58, vertices_74, vertices_82, vertices_658, vertices_274, vertices_194, vertices_386, vertices_44, vertices_268, vertices_52, vertices_276, vertices_292, vertices_104, vertices_552, vertices_200, vertices_648, vertices_776, vertices_112, vertices_304, vertices_592, vertices_784, vertices_608, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_269), (false, vertices_905), (true, vertices_82), (true, vertices_658), (true, vertices_274), (true, vertices_276), (true, vertices_292), (true, vertices_104), (true, vertices_552), (true, vertices_112), (true, vertices_304), (true, vertices_592), (true, vertices_784), (true, vertices_608), (true, vertices_800), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 14 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_391) then 15 else
  if p.val = (false, vertices_203) then 18 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_905) then 21 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_658) then 19 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_104) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_608) then 11 else
  if p.val = (true, vertices_800) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_269), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_658), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 4 7 8 812 44 3
cert_row_4 1 3 4 5 7 8 880 112 3
cert_row_4 2 2 4 5 6 8 744 104 3
cert_row_2 3 0 3 6 8 658
cert_row_2 4 0 2 3 4 58
cert_rows_2
cert_pivot 1 7 5 6 0
cert_heightProof 5
cert_coverFacet 0 278
cert_cover_2 0 1 0 3 7 22 278 3
cert_coverFacet 1 122
cert_cover_5 1 4 0 2 3 5 58 122 3
cert_coverFacet 2 722
cert_cover_5 2 3 0 3 5 6 82 722 3
cert_coverFacet 3 914
cert_cover_5 3 3 0 3 6 7 658 914 3
cert_coverFacet 4 812
cert_cover_5 4 0 1 2 4 7 44 812 3
cert_coverFacet 5 308
cert_cover_2 5 3 1 4 7 52 308 3
cert_coverFacet 6 744
cert_cover_5 6 2 2 4 5 6 104 744 3
cert_coverFacet 7 880
cert_cover_5 7 1 3 4 5 7 112 880 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 5 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0745

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_one_six_0746.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0746

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 341, 121, 961, 270, 906, 812, 564, 852, 744, 624, 7, 11, 131, 21, 261, 57, 73, 81, 193, 321, 385, 14, 262, 138, 266, 386, 44, 268, 52, 340, 532, 548, 772, 104, 552, 200, 648, 776, 112, 560, 592, 608, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_341, vertices_121, vertices_961, vertices_270, vertices_906, vertices_812, vertices_564, vertices_852, vertices_744, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_193, vertices_321, vertices_385, vertices_14, vertices_262, vertices_138, vertices_266, vertices_386, vertices_44, vertices_268, vertices_52, vertices_340, vertices_532, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_776, vertices_112, vertices_560, vertices_592, vertices_608, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_341), (false, vertices_121), (false, vertices_961), (true, vertices_266), (true, vertices_268), (true, vertices_532), (true, vertices_548), (true, vertices_772), (true, vertices_552), (true, vertices_648), (true, vertices_776), (true, vertices_560), (true, vertices_592), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 16 19 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_203) then 13 else
  if p.val = (false, vertices_341) then 15 else
  if p.val = (false, vertices_121) then 18 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_608) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
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
cert_row_2 0 1 3 5 7 340
cert_row_4 1 0 2 6 7 8 906 138 3
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 3 0 1 2
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 906
cert_cover_5 1 1 0 2 6 7 138 906 3
cert_coverFacet 2 812
cert_cover_5 2 2 1 2 4 7 44 812 3
cert_coverFacet 3 564
cert_cover_2 3 3 1 4 8 52 564 3
cert_coverFacet 4 852
cert_cover_5 4 0 1 3 5 8 340 852 3
cert_coverFacet 5 744
cert_cover_5 5 3 2 4 5 6 104 744 3
cert_coverFacet 6 624
cert_cover_2 6 4 3 5 8 112 624 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0746

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_one_six_0747.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0747

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 789, 121, 465, 270, 906, 812, 564, 744, 624, 976, 7, 11, 131, 21, 261, 57, 73, 81, 273, 193, 385, 14, 262, 138, 266, 386, 44, 268, 52, 532, 548, 772, 104, 552, 200, 648, 776, 112, 560, 464, 592, 784, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_789, vertices_121, vertices_465, vertices_270, vertices_906, vertices_812, vertices_564, vertices_744, vertices_624, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_193, vertices_385, vertices_14, vertices_262, vertices_138, vertices_266, vertices_386, vertices_44, vertices_268, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_776, vertices_112, vertices_560, vertices_464, vertices_592, vertices_784, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_789), (false, vertices_121), (false, vertices_465), (true, vertices_266), (true, vertices_268), (true, vertices_548), (true, vertices_552), (true, vertices_648), (true, vertices_776), (true, vertices_560), (true, vertices_592), (true, vertices_608), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 16 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_203) then 13 else
  if p.val = (false, vertices_789) then 15 else
  if p.val = (false, vertices_121) then 18 else
  if p.val = (false, vertices_465) then 20 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_648) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 5 6 7 464
cert_row_4 1 0 2 6 7 8 906 138 3
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 3 0 1 2
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 906
cert_cover_5 1 1 0 2 6 7 138 906 3
cert_coverFacet 2 812
cert_cover_5 2 2 1 2 4 7 44 812 3
cert_coverFacet 3 564
cert_cover_2 3 3 1 4 8 52 564 3
cert_coverFacet 4 744
cert_cover_5 4 3 2 4 5 6 104 744 3
cert_coverFacet 5 624
cert_cover_2 5 4 3 5 8 112 624 3
cert_coverFacet 6 976
cert_cover_5 6 0 3 5 6 8 464 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0747

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_one_six_0748.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0748

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 269, 905, 278, 122, 722, 914, 812, 628, 788, 744, 7, 11, 131, 13, 261, 137, 265, 385, 22, 262, 58, 74, 82, 658, 274, 194, 386, 44, 268, 52, 276, 532, 548, 772, 104, 552, 200, 648, 776, 112, 592, 784, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_269, vertices_905, vertices_278, vertices_122, vertices_722, vertices_914, vertices_812, vertices_628, vertices_788, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_13, vertices_261, vertices_137, vertices_265, vertices_385, vertices_22, vertices_262, vertices_58, vertices_74, vertices_82, vertices_658, vertices_274, vertices_194, vertices_386, vertices_44, vertices_268, vertices_52, vertices_276, vertices_532, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_776, vertices_112, vertices_592, vertices_784, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_269), (false, vertices_905), (true, vertices_82), (true, vertices_658), (true, vertices_274), (true, vertices_276), (true, vertices_532), (true, vertices_548), (true, vertices_772), (true, vertices_104), (true, vertices_552), (true, vertices_112), (true, vertices_592), (true, vertices_784), (true, vertices_608), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 14 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_391) then 15 else
  if p.val = (false, vertices_203) then 18 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_905) then 21 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_658) then 19 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_772) then 6 else
  if p.val = (true, vertices_104) then 7 else
  if p.val = (true, vertices_552) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_269), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_658), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 4 7 8 812 44 3
cert_row_4 1 1 3 4 5 8 628 52 3
cert_row_4 2 2 4 5 6 8 744 104 3
cert_row_2 3 0 3 6 8 658
cert_row_2 4 0 2 3 4 58
cert_rows_2
cert_pivot 7 1 5 6 0
cert_heightProof 5
cert_coverFacet 0 278
cert_cover_2 0 1 0 3 7 22 278 3
cert_coverFacet 1 122
cert_cover_5 1 4 0 2 3 5 58 122 3
cert_coverFacet 2 722
cert_cover_5 2 3 0 3 5 6 82 722 3
cert_coverFacet 3 914
cert_cover_5 3 3 0 3 6 7 658 914 3
cert_coverFacet 4 812
cert_cover_5 4 0 1 2 4 7 44 812 3
cert_coverFacet 5 628
cert_cover_5 5 1 1 3 4 5 52 628 3
cert_coverFacet 6 788
cert_cover_2 6 3 1 7 8 276 788 3
cert_coverFacet 7 744
cert_cover_5 7 2 2 4 5 6 104 744 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 5 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0748

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_one_six_0749.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0749

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 277, 121, 849, 961, 270, 906, 812, 628, 788, 744, 7, 11, 131, 21, 261, 57, 73, 81, 273, 193, 833, 385, 14, 262, 138, 266, 386, 44, 268, 52, 276, 532, 548, 772, 104, 552, 200, 648, 776, 112, 592, 784, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_277, vertices_121, vertices_849, vertices_961, vertices_270, vertices_906, vertices_812, vertices_628, vertices_788, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_193, vertices_833, vertices_385, vertices_14, vertices_262, vertices_138, vertices_266, vertices_386, vertices_44, vertices_268, vertices_52, vertices_276, vertices_532, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_776, vertices_112, vertices_592, vertices_784, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_277), (false, vertices_121), (false, vertices_849), (false, vertices_961), (true, vertices_266), (true, vertices_268), (true, vertices_532), (true, vertices_548), (true, vertices_772), (true, vertices_552), (true, vertices_648), (true, vertices_776), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 14 17 18 19 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_203) then 12 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_121) then 16 else
  if p.val = (false, vertices_849) then 20 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_608) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 6 7 8 906 138 3
cert_row_4 1 1 2 4 7 8 812 44 3
cert_row_4 2 1 3 4 5 8 628 52 3
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 906
cert_cover_5 1 0 0 2 6 7 138 906 3
cert_coverFacet 2 812
cert_cover_5 2 1 1 2 4 7 44 812 3
cert_coverFacet 3 628
cert_cover_5 3 2 1 3 4 5 52 628 3
cert_coverFacet 4 788
cert_cover_2 4 3 1 7 8 276 788 3
cert_coverFacet 5 744
cert_cover_5 5 3 2 4 5 6 104 744 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0749

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_one_six_0750.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0750

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 267, 899, 117, 809, 737, 398, 284, 468, 632, 792, 976, 7, 11, 131, 259, 53, 69, 41, 265, 97, 545, 193, 641, 769, 14, 134, 266, 386, 28, 268, 84, 276, 196, 388, 56, 280, 536, 552, 776, 112, 464, 592, 784, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_267, vertices_899, vertices_117, vertices_809, vertices_737, vertices_398, vertices_284, vertices_468, vertices_632, vertices_792, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_53, vertices_69, vertices_41, vertices_265, vertices_97, vertices_545, vertices_193, vertices_641, vertices_769, vertices_14, vertices_134, vertices_266, vertices_386, vertices_28, vertices_268, vertices_84, vertices_276, vertices_196, vertices_388, vertices_56, vertices_280, vertices_536, vertices_552, vertices_776, vertices_112, vertices_464, vertices_592, vertices_784, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_267), (false, vertices_899), (false, vertices_117), (false, vertices_809), (false, vertices_737), (true, vertices_268), (true, vertices_276), (true, vertices_388), (true, vertices_280), (true, vertices_536), (true, vertices_464), (true, vertices_592), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 14 16 18 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_199) then 9 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_899) then 10 else
  if p.val = (false, vertices_117) then 13 else
  if p.val = (false, vertices_809) then 15 else
  if p.val = (false, vertices_737) then 19 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_388) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_464) then 17 else
  if p.val = (true, vertices_592) then 6 else
  if p.val = (true, vertices_784) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(true, vertices_464), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 14 3
cert_row_2 1 3 5 6 7 464
cert_row_4 2 2 3 4 5 8 632 56 3
cert_rows_3
cert_pivot_3 6 0 2
cert_heightProof 3
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 284
cert_cover_2 1 2 1 3 7 28 284 3
cert_coverFacet 2 468
cert_cover_5 2 1 1 3 5 6 84 468 3
cert_coverFacet 3 632
cert_cover_5 3 2 2 3 4 5 56 632 3
cert_coverFacet 4 792
cert_cover_2 4 3 2 7 8 280 792 3
cert_coverFacet 5 976
cert_cover_5 5 1 3 5 6 8 464 976 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0750

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_one_six_0751.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0751

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 269, 905, 790, 122, 850, 450, 812, 628, 744, 960, 7, 11, 131, 13, 261, 137, 265, 385, 22, 262, 58, 74, 82, 786, 194, 322, 386, 44, 268, 52, 532, 548, 772, 104, 552, 200, 648, 776, 112, 592, 608, 448, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_269, vertices_905, vertices_790, vertices_122, vertices_850, vertices_450, vertices_812, vertices_628, vertices_744, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_13, vertices_261, vertices_137, vertices_265, vertices_385, vertices_22, vertices_262, vertices_58, vertices_74, vertices_82, vertices_786, vertices_194, vertices_322, vertices_386, vertices_44, vertices_268, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_776, vertices_112, vertices_592, vertices_608, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_269), (false, vertices_905), (true, vertices_82), (true, vertices_786), (true, vertices_322), (true, vertices_532), (true, vertices_548), (true, vertices_772), (true, vertices_104), (true, vertices_552), (true, vertices_112), (true, vertices_592), (true, vertices_608), (true, vertices_448), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 14 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_391) then 15 else
  if p.val = (false, vertices_203) then 18 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_905) then 21 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_786) then 19 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_448) then 11 else
  if p.val = (true, vertices_704) then 12 else
  if p.val = (true, vertices_832) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_269), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_786), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 4 5 6 8 744 104 3
cert_row_4 1 1 3 4 5 8 628 52 3
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_2 3 0 3 7 8 786
cert_row_2 4 0 2 3 4 58
cert_rows_2
cert_pivot 6 5 1 7 0
cert_heightProof 5
cert_coverFacet 0 790
cert_cover_5 0 3 0 1 3 7 22 790 3
cert_coverFacet 1 122
cert_cover_5 1 4 0 2 3 5 58 122 3
cert_coverFacet 2 850
cert_cover_5 2 3 0 3 5 7 82 850 3
cert_coverFacet 3 450
cert_cover_2 3 5 0 6 7 194 450 3
cert_coverFacet 4 812
cert_cover_5 4 2 1 2 4 7 44 812 3
cert_coverFacet 5 628
cert_cover_5 5 1 1 3 4 5 52 628 3
cert_coverFacet 6 744
cert_cover_5 6 0 2 4 5 6 104 744 3
cert_coverFacet 7 960
cert_cover_2 7 6 5 7 8 448 960 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 5 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0751

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_one_six_0752.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0752

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 269, 905, 790, 122, 210, 914, 812, 628, 744, 720, 7, 11, 131, 13, 261, 137, 265, 385, 22, 262, 58, 74, 82, 146, 786, 194, 386, 44, 268, 52, 532, 548, 772, 104, 552, 200, 648, 776, 112, 208, 592, 656, 608, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_269, vertices_905, vertices_790, vertices_122, vertices_210, vertices_914, vertices_812, vertices_628, vertices_744, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_13, vertices_261, vertices_137, vertices_265, vertices_385, vertices_22, vertices_262, vertices_58, vertices_74, vertices_82, vertices_146, vertices_786, vertices_194, vertices_386, vertices_44, vertices_268, vertices_52, vertices_532, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_776, vertices_112, vertices_208, vertices_592, vertices_656, vertices_608, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_269), (false, vertices_905), (true, vertices_82), (true, vertices_146), (true, vertices_786), (true, vertices_532), (true, vertices_548), (true, vertices_772), (true, vertices_104), (true, vertices_552), (true, vertices_112), (true, vertices_208), (true, vertices_592), (true, vertices_656), (true, vertices_608), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 14 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_391) then 15 else
  if p.val = (false, vertices_203) then 18 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_905) then 21 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_786) then 19 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_656) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_269), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_786), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 4 5 6 8 744 104 3
cert_row_4 1 1 3 4 5 8 628 52 3
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_2 3 0 3 7 8 786
cert_row_2 4 0 2 3 4 58
cert_rows_2
cert_pivot 6 5 1 7 0
cert_heightProof 5
cert_coverFacet 0 790
cert_cover_5 0 3 0 1 3 7 22 790 3
cert_coverFacet 1 122
cert_cover_5 1 4 0 2 3 5 58 122 3
cert_coverFacet 2 210
cert_cover_2 2 3 0 5 6 82 210 3
cert_coverFacet 3 914
cert_cover_5 3 3 0 3 6 7 146 914 3
cert_coverFacet 4 812
cert_cover_5 4 2 1 2 4 7 44 812 3
cert_coverFacet 5 628
cert_cover_5 5 1 1 3 4 5 52 628 3
cert_coverFacet 6 744
cert_cover_5 6 0 2 4 5 6 104 744 3
cert_coverFacet 7 720
cert_cover_2 7 5 3 6 8 208 720 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 5 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0752

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_one_six_0753.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0753

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 277, 121, 465, 270, 906, 812, 628, 852, 744, 960, 7, 11, 131, 21, 261, 57, 73, 81, 273, 193, 385, 14, 262, 138, 266, 386, 44, 268, 52, 596, 276, 548, 772, 104, 552, 200, 648, 776, 112, 336, 608, 448, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_277, vertices_121, vertices_465, vertices_270, vertices_906, vertices_812, vertices_628, vertices_852, vertices_744, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_193, vertices_385, vertices_14, vertices_262, vertices_138, vertices_266, vertices_386, vertices_44, vertices_268, vertices_52, vertices_596, vertices_276, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_776, vertices_112, vertices_336, vertices_608, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_277), (false, vertices_121), (false, vertices_465), (true, vertices_266), (true, vertices_268), (true, vertices_596), (true, vertices_548), (true, vertices_772), (true, vertices_552), (true, vertices_648), (true, vertices_776), (true, vertices_608), (true, vertices_704), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_391) then 13 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_121) then 19 else
  if p.val = (false, vertices_465) then 21 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_596) then 16 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_832) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(true, vertices_596), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
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
cert_row_2 0 1 3 5 8 596
cert_row_4 1 0 2 6 7 8 906 138 3
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 3 0 1 2
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 906
cert_cover_5 1 1 0 2 6 7 138 906 3
cert_coverFacet 2 812
cert_cover_5 2 2 1 2 4 7 44 812 3
cert_coverFacet 3 628
cert_cover_5 3 0 1 3 4 5 52 628 3
cert_coverFacet 4 852
cert_cover_5 4 0 1 3 5 7 596 852 3
cert_coverFacet 5 744
cert_cover_5 5 3 2 4 5 6 104 744 3
cert_coverFacet 6 960
cert_cover_2 6 6 5 7 8 448 960 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0753

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_one_six_0754.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0754

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 203, 277, 121, 337, 961, 270, 906, 812, 628, 852, 744, 7, 11, 131, 21, 261, 57, 73, 81, 273, 193, 321, 385, 14, 262, 138, 266, 386, 44, 268, 52, 596, 276, 548, 772, 104, 552, 200, 648, 776, 112, 336, 608, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_203, vertices_277, vertices_121, vertices_337, vertices_961, vertices_270, vertices_906, vertices_812, vertices_628, vertices_852, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_261, vertices_57, vertices_73, vertices_81, vertices_273, vertices_193, vertices_321, vertices_385, vertices_14, vertices_262, vertices_138, vertices_266, vertices_386, vertices_44, vertices_268, vertices_52, vertices_596, vertices_276, vertices_548, vertices_772, vertices_104, vertices_552, vertices_200, vertices_648, vertices_776, vertices_112, vertices_336, vertices_608, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_203), (false, vertices_277), (false, vertices_121), (false, vertices_337), (false, vertices_961), (true, vertices_266), (true, vertices_268), (true, vertices_596), (true, vertices_548), (true, vertices_772), (true, vertices_552), (true, vertices_648), (true, vertices_776), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 15 18 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_203) then 12 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_121) then 17 else
  if p.val = (false, vertices_337) then 1 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_596) then 14 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_608) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_337), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(true, vertices_596), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
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
cert_row_2 0 1 3 5 8 596
cert_row_4 1 0 2 6 7 8 906 138 3
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 3 0 1 2
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 906
cert_cover_5 1 1 0 2 6 7 138 906 3
cert_coverFacet 2 812
cert_cover_5 2 2 1 2 4 7 44 812 3
cert_coverFacet 3 628
cert_cover_5 3 0 1 3 4 5 52 628 3
cert_coverFacet 4 852
cert_cover_5 4 0 1 3 5 7 596 852 3
cert_coverFacet 5 744
cert_cover_5 5 3 2 4 5 6 104 744 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0754

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_1110 : Certifies 1110 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0722.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1111 : Certifies 1111 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0723.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1112 : Certifies 1112 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0724.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1113 : Certifies 1113 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0725.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1114 : Certifies 1114 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0726.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1115 : Certifies 1115 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0727.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1116 : Certifies 1116 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0728.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1117 : Certifies 1117 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0729.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1118 : Certifies 1118 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0730.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1119 : Certifies 1119 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0734.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1120 : Certifies 1120 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0735.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1121 : Certifies 1121 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0736.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1122 : Certifies 1122 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0737.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1123 : Certifies 1123 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0738.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1124 : Certifies 1124 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0739.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1125 : Certifies 1125 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0740.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1126 : Certifies 1126 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0741.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1127 : Certifies 1127 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0742.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1128 : Certifies 1128 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0743.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1129 : Certifies 1129 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0744.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1130 : Certifies 1130 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0745.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1131 : Certifies 1131 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0746.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1132 : Certifies 1132 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0747.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1133 : Certifies 1133 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0748.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1134 : Certifies 1134 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0749.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1135 : Certifies 1135 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0750.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1136 : Certifies 1136 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0751.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1137 : Certifies 1137 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0752.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1138 : Certifies 1138 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0753.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1139 : Certifies 1139 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0754.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B037 (j : Fin 30) :
    Certifies (1110 + j.val) := by
  fin_cases j
  · exact projection_1110
  · exact projection_1111
  · exact projection_1112
  · exact projection_1113
  · exact projection_1114
  · exact projection_1115
  · exact projection_1116
  · exact projection_1117
  · exact projection_1118
  · exact projection_1119
  · exact projection_1120
  · exact projection_1121
  · exact projection_1122
  · exact projection_1123
  · exact projection_1124
  · exact projection_1125
  · exact projection_1126
  · exact projection_1127
  · exact projection_1128
  · exact projection_1129
  · exact projection_1130
  · exact projection_1131
  · exact projection_1132
  · exact projection_1133
  · exact projection_1134
  · exact projection_1135
  · exact projection_1136
  · exact projection_1137
  · exact projection_1138
  · exact projection_1139

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
