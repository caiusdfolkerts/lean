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
/- Source: ProjectionCertificates/R_one_six_0048.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0048

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 395, 195, 597, 793, 961, 206, 236, 820, 868, 440, 480, 7, 11, 67, 131, 21, 69, 25, 265, 529, 193, 577, 385, 769, 14, 70, 138, 194, 44, 204, 52, 532, 100, 804, 580, 56, 280, 168, 392, 304, 784, 224, 352, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_395, vertices_195, vertices_597, vertices_793, vertices_961, vertices_206, vertices_236, vertices_820, vertices_868, vertices_440, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_131, vertices_21, vertices_69, vertices_25, vertices_265, vertices_529, vertices_193, vertices_577, vertices_385, vertices_769, vertices_14, vertices_70, vertices_138, vertices_194, vertices_44, vertices_204, vertices_52, vertices_532, vertices_100, vertices_804, vertices_580, vertices_56, vertices_280, vertices_168, vertices_392, vertices_304, vertices_784, vertices_224, vertices_352, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_395), (false, vertices_195), (false, vertices_597), (false, vertices_793), (false, vertices_961), (true, vertices_204), (true, vertices_100), (true, vertices_804), (true, vertices_168), (true, vertices_304), (true, vertices_224), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 14 10 17 18 19 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 11 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_395) then 9 else
  if p.val = (false, vertices_195) then 1 else
  if p.val = (false, vertices_597) then 15 else
  if p.val = (false, vertices_793) then 12 else
  if p.val = (false, vertices_961) then 20 else
  if p.val = (true, vertices_204) then 13 else
  if p.val = (true, vertices_100) then 2 else
  if p.val = (true, vertices_804) then 16 else
  if p.val = (true, vertices_168) then 3 else
  if p.val = (true, vertices_304) then 4 else
  if p.val = (true, vertices_224) then 5 else
  if p.val = (true, vertices_352) then 6 else
  if p.val = (true, vertices_416) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 10 => Sum.inl 2
  | 11 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_804), by decide +kernel⟩
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
cert_row_2 0 1 4 7 8 804
cert_row_2 1 1 2 5 6 204
cert_row_4 2 2 3 4 6 7 440 56 3
cert_rows_3
cert_pivot_3 1 8 2
cert_heightProof 3
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 14 206 3
cert_coverFacet 1 236
cert_cover_5 1 1 1 2 4 5 44 236 3
cert_coverFacet 2 820
cert_cover_5 2 0 1 3 4 7 52 820 3
cert_coverFacet 3 868
cert_cover_5 3 0 1 4 5 7 100 868 3
cert_coverFacet 4 440
cert_cover_5 4 2 2 3 4 6 56 440 3
cert_coverFacet 5 480
cert_cover_2 5 5 4 6 7 224 480 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0048

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_one_six_0049.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0049

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 597, 233, 817, 609, 398, 198, 796, 964, 440, 992, 7, 11, 67, 21, 69, 41, 201, 49, 529, 97, 545, 577, 14, 70, 134, 138, 194, 28, 268, 532, 196, 580, 388, 772, 56, 280, 168, 392, 304, 784, 224, 608, 416, 800, 960]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_597, vertices_233, vertices_817, vertices_609, vertices_398, vertices_198, vertices_796, vertices_964, vertices_440, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_41, vertices_201, vertices_49, vertices_529, vertices_97, vertices_545, vertices_577, vertices_14, vertices_70, vertices_134, vertices_138, vertices_194, vertices_28, vertices_268, vertices_532, vertices_196, vertices_580, vertices_388, vertices_772, vertices_56, vertices_280, vertices_168, vertices_392, vertices_304, vertices_784, vertices_224, vertices_608, vertices_416, vertices_800, vertices_960] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_597), (false, vertices_233), (false, vertices_817), (false, vertices_609), (true, vertices_134), (true, vertices_268), (true, vertices_196), (true, vertices_388), (true, vertices_772), (true, vertices_280), (true, vertices_392), (true, vertices_416), (true, vertices_960)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 11 14 17 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 15 else
  if p.val = (false, vertices_597) then 13 else
  if p.val = (false, vertices_233) then 16 else
  if p.val = (false, vertices_817) then 18 else
  if p.val = (false, vertices_609) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_388) then 5 else
  if p.val = (true, vertices_772) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_392) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_960) then 21 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_609), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
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
cert_row_4 1 0 1 2 6 7 398 14 3
cert_row_4 2 1 2 3 7 8 796 28 3
cert_row_4 3 2 3 4 6 7 440 56 3
cert_rows
cert_pivot_2 5 0 1 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 1 0 1 2 6 14 398 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 796
cert_cover_5 2 2 1 2 3 7 28 796 3
cert_coverFacet 3 964
cert_cover_5 3 0 1 5 6 7 196 964 3
cert_coverFacet 4 440
cert_cover_5 4 3 2 3 4 6 56 440 3
cert_coverFacet 5 992
cert_cover_5 5 0 4 5 6 7 224 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0049

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_one_six_0062.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0062

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 397, 837, 449, 598, 90, 428, 820, 696, 728, 992, 7, 11, 67, 13, 69, 261, 137, 193, 321, 385, 22, 70, 26, 74, 82, 44, 396, 52, 532, 292, 580, 772, 56, 88, 664, 168, 200, 560, 592, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_397, vertices_837, vertices_449, vertices_598, vertices_90, vertices_428, vertices_820, vertices_696, vertices_728, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_69, vertices_261, vertices_137, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_74, vertices_82, vertices_44, vertices_396, vertices_52, vertices_532, vertices_292, vertices_580, vertices_772, vertices_56, vertices_88, vertices_664, vertices_168, vertices_200, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_397), (false, vertices_837), (false, vertices_449), (true, vertices_82), (true, vertices_532), (true, vertices_292), (true, vertices_88), (true, vertices_664), (true, vertices_168), (true, vertices_560), (true, vertices_592), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_837) then 18 else
  if p.val = (false, vertices_449) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_88) then 5 else
  if p.val = (true, vertices_664) then 20 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_800) then 11 else
  if p.val = (true, vertices_704) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(true, vertices_664), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 8 598 22 3
cert_row_4 1 4 5 6 7 8 992 416 1
cert_row_4 2 1 3 4 7 8 820 52 3
cert_row_2 3 2 3 6 8 664
cert_row_2 4 1 2 6 7 396
cert_rows_2
cert_pivot 0 5 4 3 1
cert_heightProof 5
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 22 598 3
cert_coverFacet 1 90
cert_cover_2 1 2 0 3 5 26 90 3
cert_coverFacet 2 428
cert_cover_5 2 4 1 2 4 6 44 428 3
cert_coverFacet 3 820
cert_cover_5 3 2 1 3 4 7 52 820 3
cert_coverFacet 4 696
cert_cover_5 4 3 2 3 4 6 56 696 3
cert_coverFacet 5 728
cert_cover_5 5 3 2 3 5 6 88 728 3
cert_coverFacet 6 992
cert_cover_5 6 1 4 5 6 7 416 992 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 5 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0062

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_one_six_0063.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0063

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 395, 835, 597, 425, 817, 206, 450, 604, 696, 712, 992, 7, 11, 67, 259, 21, 69, 41, 393, 49, 529, 289, 577, 769, 14, 70, 138, 194, 322, 386, 28, 76, 596, 56, 536, 168, 200, 584, 648, 560, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_395, vertices_835, vertices_597, vertices_425, vertices_817, vertices_206, vertices_450, vertices_604, vertices_696, vertices_712, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_41, vertices_393, vertices_49, vertices_529, vertices_289, vertices_577, vertices_769, vertices_14, vertices_70, vertices_138, vertices_194, vertices_322, vertices_386, vertices_28, vertices_76, vertices_596, vertices_56, vertices_536, vertices_168, vertices_200, vertices_584, vertices_648, vertices_560, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_395), (false, vertices_835), (false, vertices_597), (false, vertices_425), (false, vertices_817), (true, vertices_194), (true, vertices_76), (true, vertices_536), (true, vertices_200), (true, vertices_584), (true, vertices_648), (true, vertices_672), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 15 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_395) then 16 else
  if p.val = (false, vertices_835) then 11 else
  if p.val = (false, vertices_597) then 14 else
  if p.val = (false, vertices_425) then 17 else
  if p.val = (false, vertices_817) then 19 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_536) then 3 else
  if p.val = (true, vertices_200) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_704) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 6 206 14 3
cert_row_2 1 1 3 5 8 596
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 4 5 6 7 8 992 416 1
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 450
cert_cover_2 1 5 0 6 7 194 450 3
cert_coverFacet 2 604
cert_cover_5 2 1 1 2 3 5 28 604 3
cert_coverFacet 3 696
cert_cover_5 3 2 2 3 4 6 56 696 3
cert_coverFacet 4 712
cert_cover_2 4 5 2 6 8 200 712 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 416 992 1
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0063

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_one_six_0064.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0064

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 789, 837, 601, 142, 454, 172, 436, 824, 744, 992, 7, 11, 67, 21, 69, 773, 25, 73, 529, 577, 14, 70, 134, 138, 194, 44, 140, 52, 276, 164, 324, 388, 56, 536, 168, 552, 200, 584, 304, 784, 736, 416, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_789, vertices_837, vertices_601, vertices_142, vertices_454, vertices_172, vertices_436, vertices_824, vertices_744, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_773, vertices_25, vertices_73, vertices_529, vertices_577, vertices_14, vertices_70, vertices_134, vertices_138, vertices_194, vertices_44, vertices_140, vertices_52, vertices_276, vertices_164, vertices_324, vertices_388, vertices_56, vertices_536, vertices_168, vertices_552, vertices_200, vertices_584, vertices_304, vertices_784, vertices_736, vertices_416, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_789), (false, vertices_837), (false, vertices_601), (true, vertices_134), (true, vertices_140), (true, vertices_164), (true, vertices_388), (true, vertices_168), (true, vertices_552), (true, vertices_304), (true, vertices_736), (true, vertices_416), (true, vertices_800), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 17 19 20 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 12 else
  if p.val = (false, vertices_789) then 15 else
  if p.val = (false, vertices_837) then 16 else
  if p.val = (false, vertices_601) then 18 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_736) then 21 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_448) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inr ⟨(true, vertices_736), by decide +kernel⟩
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 70 3
cert_row_2 1 4 5 6 8 736
cert_row_4 2 1 3 4 6 7 436 52 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 172
cert_cover_2 2 2 1 4 6 44 172 3
cert_coverFacet 3 436
cert_cover_5 3 2 1 3 4 6 52 436 3
cert_coverFacet 4 824
cert_cover_5 4 3 2 3 4 7 56 824 3
cert_coverFacet 5 744
cert_cover_5 5 1 2 4 5 6 168 744 2
cert_coverFacet 6 992
cert_cover_5 6 1 4 5 6 7 736 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0064

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_one_six_0071.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0071

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 653, 837, 961, 342, 90, 556, 820, 248, 936, 496, 7, 11, 67, 13, 69, 517, 137, 193, 833, 641, 22, 70, 26, 74, 82, 44, 524, 52, 276, 548, 324, 772, 56, 88, 168, 552, 200, 648, 240, 304, 336, 416, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_653, vertices_837, vertices_961, vertices_342, vertices_90, vertices_556, vertices_820, vertices_248, vertices_936, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_69, vertices_517, vertices_137, vertices_193, vertices_833, vertices_641, vertices_22, vertices_70, vertices_26, vertices_74, vertices_82, vertices_44, vertices_524, vertices_52, vertices_276, vertices_548, vertices_324, vertices_772, vertices_56, vertices_88, vertices_168, vertices_552, vertices_200, vertices_648, vertices_240, vertices_304, vertices_336, vertices_416, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_653), (false, vertices_837), (false, vertices_961), (true, vertices_82), (true, vertices_276), (true, vertices_548), (true, vertices_88), (true, vertices_168), (true, vertices_552), (true, vertices_240), (true, vertices_304), (true, vertices_336), (true, vertices_416), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 17 19 20 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 12 else
  if p.val = (false, vertices_653) then 15 else
  if p.val = (false, vertices_837) then 21 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_88) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_240) then 18 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 7 342 22 3
cert_row_2 1 3 4 5 6 240
cert_row_4 2 1 3 4 7 8 820 52 3
cert_row_4 3 2 4 6 7 8 936 168 3
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 0 0 1 3 5 22 342 3
cert_coverFacet 1 90
cert_cover_2 1 2 0 3 5 26 90 3
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 820
cert_cover_5 3 2 1 3 4 7 52 820 3
cert_coverFacet 4 248
cert_cover_5 4 1 2 3 4 5 56 248 3
cert_coverFacet 5 936
cert_cover_5 5 3 2 4 6 7 168 936 3
cert_coverFacet 6 496
cert_cover_5 6 1 3 4 5 7 240 496 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0071

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_one_six_0072.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0072

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 397, 837, 449, 598, 666, 706, 428, 820, 696, 992, 7, 11, 67, 13, 69, 261, 137, 193, 321, 385, 22, 70, 26, 138, 530, 194, 578, 642, 44, 396, 52, 532, 292, 580, 772, 56, 664, 168, 560, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_397, vertices_837, vertices_449, vertices_598, vertices_666, vertices_706, vertices_428, vertices_820, vertices_696, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_69, vertices_261, vertices_137, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_138, vertices_530, vertices_194, vertices_578, vertices_642, vertices_44, vertices_396, vertices_52, vertices_532, vertices_292, vertices_580, vertices_772, vertices_56, vertices_664, vertices_168, vertices_560, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_397), (false, vertices_837), (false, vertices_449), (true, vertices_530), (true, vertices_578), (true, vertices_642), (true, vertices_532), (true, vertices_292), (true, vertices_664), (true, vertices_168), (true, vertices_560), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 14 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_837) then 18 else
  if p.val = (false, vertices_449) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_664) then 20 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_800) then 11 else
  if p.val = (true, vertices_704) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(true, vertices_664), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 8 598 22 3
cert_row_4 1 4 5 6 7 8 992 416 1
cert_row_4 2 1 3 4 7 8 820 52 3
cert_row_2 3 2 3 6 8 664
cert_row_2 4 1 2 6 7 396
cert_rows_2
cert_pivot 0 5 4 3 1
cert_heightProof 5
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 22 598 3
cert_coverFacet 1 666
cert_cover_5 1 3 0 2 3 6 26 666 3
cert_coverFacet 2 706
cert_cover_2 2 5 0 6 8 194 706 3
cert_coverFacet 3 428
cert_cover_5 3 4 1 2 4 6 44 428 3
cert_coverFacet 4 820
cert_cover_5 4 2 1 3 4 7 52 820 3
cert_coverFacet 5 696
cert_cover_5 5 3 2 3 4 6 56 696 3
cert_coverFacet 6 992
cert_cover_5 6 1 4 5 6 7 416 992 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 5 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0072

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_one_six_0073.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0073

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 597, 665, 961, 398, 838, 450, 428, 820, 696, 928, 7, 11, 67, 21, 69, 25, 137, 529, 193, 577, 641, 14, 70, 262, 138, 194, 322, 386, 44, 396, 52, 532, 292, 580, 772, 56, 664, 168, 560, 416, 672, 800, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_597, vertices_665, vertices_961, vertices_398, vertices_838, vertices_450, vertices_428, vertices_820, vertices_696, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_25, vertices_137, vertices_529, vertices_193, vertices_577, vertices_641, vertices_14, vertices_70, vertices_262, vertices_138, vertices_194, vertices_322, vertices_386, vertices_44, vertices_396, vertices_52, vertices_532, vertices_292, vertices_580, vertices_772, vertices_56, vertices_664, vertices_168, vertices_560, vertices_416, vertices_672, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_597), (false, vertices_665), (false, vertices_961), (true, vertices_262), (true, vertices_322), (true, vertices_386), (true, vertices_396), (true, vertices_292), (true, vertices_772), (true, vertices_168), (true, vertices_560), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 17 19 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 12 else
  if p.val = (false, vertices_597) then 15 else
  if p.val = (false, vertices_665) then 18 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_396) then 16 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
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
cert_row_4 0 0 1 5 7 8 838 70 3
cert_row_4 1 1 3 4 7 8 820 52 3
cert_row_2 2 2 3 6 8 664
cert_row_2 3 1 2 6 7 396
cert_rows
cert_pivot_2 0 4 3 1
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 3 0 1 2 6 14 398 3
cert_coverFacet 1 838
cert_cover_5 1 0 0 1 5 7 70 838 3
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
cert_coverFacet 3 428
cert_cover_5 3 3 1 2 4 6 44 428 3
cert_coverFacet 4 820
cert_cover_5 4 1 1 3 4 7 52 820 3
cert_coverFacet 5 696
cert_cover_5 5 2 2 3 4 6 56 696 3
cert_coverFacet 6 928
cert_cover_2 6 6 4 7 8 416 928 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0073

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_one_six_0074.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0074

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 597, 665, 961, 398, 838, 450, 428, 820, 184, 944, 7, 11, 67, 21, 69, 25, 137, 529, 193, 577, 641, 14, 70, 262, 138, 194, 322, 386, 44, 396, 52, 532, 292, 580, 772, 56, 152, 168, 176, 816, 656, 416, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_597, vertices_665, vertices_961, vertices_398, vertices_838, vertices_450, vertices_428, vertices_820, vertices_184, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_25, vertices_137, vertices_529, vertices_193, vertices_577, vertices_641, vertices_14, vertices_70, vertices_262, vertices_138, vertices_194, vertices_322, vertices_386, vertices_44, vertices_396, vertices_52, vertices_532, vertices_292, vertices_580, vertices_772, vertices_56, vertices_152, vertices_168, vertices_176, vertices_816, vertices_656, vertices_416, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_597), (false, vertices_665), (false, vertices_961), (true, vertices_262), (true, vertices_322), (true, vertices_386), (true, vertices_396), (true, vertices_292), (true, vertices_772), (true, vertices_168), (true, vertices_176), (true, vertices_816), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 11 15 17 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 10 else
  if p.val = (false, vertices_597) then 13 else
  if p.val = (false, vertices_665) then 16 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_396) then 14 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_816) then 18 else
  if p.val = (true, vertices_416) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
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
cert_row_2 0 1 2 6 7 396
cert_row_2 1 3 4 7 8 816
cert_row_4 2 0 1 5 7 8 838 70 3
cert_rows_3
cert_pivot_3 3 2 0
cert_heightProof 3
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 838
cert_cover_5 1 2 0 1 5 7 70 838 3
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
cert_coverFacet 3 428
cert_cover_5 3 0 1 2 4 6 44 428 3
cert_coverFacet 4 820
cert_cover_5 4 1 1 3 4 7 52 820 3
cert_coverFacet 5 184
cert_cover_2 5 3 2 4 6 56 184 3
cert_coverFacet 6 944
cert_cover_5 6 1 3 4 6 7 176 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0074

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_one_six_0075.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0075

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 395, 835, 597, 425, 817, 206, 450, 156, 724, 696, 992, 7, 11, 67, 259, 21, 69, 41, 393, 49, 529, 289, 577, 769, 14, 70, 138, 194, 322, 386, 28, 140, 596, 148, 196, 56, 152, 168, 560, 656, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_395, vertices_835, vertices_597, vertices_425, vertices_817, vertices_206, vertices_450, vertices_156, vertices_724, vertices_696, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_41, vertices_393, vertices_49, vertices_529, vertices_289, vertices_577, vertices_769, vertices_14, vertices_70, vertices_138, vertices_194, vertices_322, vertices_386, vertices_28, vertices_140, vertices_596, vertices_148, vertices_196, vertices_56, vertices_152, vertices_168, vertices_560, vertices_656, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_395), (false, vertices_835), (false, vertices_597), (false, vertices_425), (false, vertices_817), (true, vertices_194), (true, vertices_140), (true, vertices_148), (true, vertices_196), (true, vertices_152), (true, vertices_656), (true, vertices_672), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 15 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_395) then 16 else
  if p.val = (false, vertices_835) then 11 else
  if p.val = (false, vertices_597) then 14 else
  if p.val = (false, vertices_425) then 17 else
  if p.val = (false, vertices_817) then 19 else
  if p.val = (true, vertices_194) then 1 else
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
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 6 206 14 3
cert_row_2 1 1 3 5 8 596
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 4 5 6 7 8 992 416 1
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 450
cert_cover_2 1 5 0 6 7 194 450 3
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0075

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_one_six_0076.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0076

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 85, 665, 849, 961, 142, 454, 684, 372, 932, 824, 7, 11, 67, 21, 69, 25, 137, 81, 529, 193, 833, 641, 14, 70, 134, 138, 194, 44, 140, 52, 84, 676, 292, 324, 388, 56, 536, 552, 648, 304, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_85, vertices_665, vertices_849, vertices_961, vertices_142, vertices_454, vertices_684, vertices_372, vertices_932, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_25, vertices_137, vertices_81, vertices_529, vertices_193, vertices_833, vertices_641, vertices_14, vertices_70, vertices_134, vertices_138, vertices_194, vertices_44, vertices_140, vertices_52, vertices_84, vertices_676, vertices_292, vertices_324, vertices_388, vertices_56, vertices_536, vertices_552, vertices_648, vertices_304, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_85), (false, vertices_665), (false, vertices_849), (false, vertices_961), (true, vertices_134), (true, vertices_140), (true, vertices_676), (true, vertices_292), (true, vertices_324), (true, vertices_388), (true, vertices_552), (true, vertices_304), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 15 17 18 19 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 11 else
  if p.val = (false, vertices_85) then 1 else
  if p.val = (false, vertices_665) then 16 else
  if p.val = (false, vertices_849) then 20 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_676) then 14 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_800) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_85), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_676), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
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
cert_row_4 0 0 1 5 6 7 454 70 3
cert_row_2 1 1 4 6 8 676
cert_row_4 2 1 3 4 5 7 372 52 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 684
cert_cover_5 2 1 1 2 4 6 44 684 3
cert_coverFacet 3 372
cert_cover_5 3 2 1 3 4 5 52 372 3
cert_coverFacet 4 932
cert_cover_5 4 1 1 4 6 7 676 932 3
cert_coverFacet 5 824
cert_cover_5 5 3 2 3 4 7 56 824 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0076

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_one_six_0077.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0077

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 139, 451, 341, 425, 817, 206, 668, 852, 708, 696, 992, 7, 11, 67, 131, 21, 69, 41, 137, 49, 273, 289, 321, 385, 14, 70, 138, 194, 28, 140, 340, 532, 196, 580, 644, 56, 664, 168, 560, 784, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_139, vertices_451, vertices_341, vertices_425, vertices_817, vertices_206, vertices_668, vertices_852, vertices_708, vertices_696, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_131, vertices_21, vertices_69, vertices_41, vertices_137, vertices_49, vertices_273, vertices_289, vertices_321, vertices_385, vertices_14, vertices_70, vertices_138, vertices_194, vertices_28, vertices_140, vertices_340, vertices_532, vertices_196, vertices_580, vertices_644, vertices_56, vertices_664, vertices_168, vertices_560, vertices_784, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_139), (false, vertices_451), (false, vertices_341), (false, vertices_425), (false, vertices_817), (true, vertices_140), (true, vertices_532), (true, vertices_196), (true, vertices_580), (true, vertices_644), (true, vertices_664), (true, vertices_672), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 15 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_139) then 1 else
  if p.val = (false, vertices_451) then 11 else
  if p.val = (false, vertices_341) then 14 else
  if p.val = (false, vertices_425) then 16 else
  if p.val = (false, vertices_817) then 19 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_580) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_664) then 17 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_704) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_139), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_664), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 6 206 14 3
cert_row_2 1 2 3 6 8 664
cert_row_2 2 1 3 5 7 340
cert_row_4 3 4 5 6 7 8 992 416 1
cert_rows
cert_pivot_2 0 2 1 4
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 668
cert_cover_5 1 1 1 2 3 6 28 668 3
cert_coverFacet 2 852
cert_cover_5 2 2 1 3 5 8 340 852 3
cert_coverFacet 3 708
cert_cover_2 3 5 1 6 8 196 708 3
cert_coverFacet 4 696
cert_cover_5 4 1 2 3 4 6 56 696 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 416 992 1
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0077

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_one_six_0078.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0078

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 597, 665, 961, 142, 454, 428, 372, 568, 936, 880, 7, 11, 67, 21, 69, 25, 137, 529, 193, 577, 641, 14, 70, 134, 138, 194, 44, 140, 52, 84, 292, 324, 388, 56, 536, 424, 552, 648, 368, 560, 592, 800, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_597, vertices_665, vertices_961, vertices_142, vertices_454, vertices_428, vertices_372, vertices_568, vertices_936, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_25, vertices_137, vertices_529, vertices_193, vertices_577, vertices_641, vertices_14, vertices_70, vertices_134, vertices_138, vertices_194, vertices_44, vertices_140, vertices_52, vertices_84, vertices_292, vertices_324, vertices_388, vertices_56, vertices_536, vertices_424, vertices_552, vertices_648, vertices_368, vertices_560, vertices_592, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_597), (false, vertices_665), (false, vertices_961), (true, vertices_134), (true, vertices_140), (true, vertices_292), (true, vertices_324), (true, vertices_388), (true, vertices_424), (true, vertices_552), (true, vertices_368), (true, vertices_560), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 11 14 17 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 10 else
  if p.val = (false, vertices_597) then 13 else
  if p.val = (false, vertices_665) then 15 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_292) then 3 else
  if p.val = (true, vertices_324) then 4 else
  if p.val = (true, vertices_388) then 5 else
  if p.val = (true, vertices_424) then 16 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_368) then 18 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_800) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_424), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(true, vertices_368), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 4 6 7 424
cert_row_2 1 3 4 5 7 368
cert_row_4 2 0 1 5 6 7 454 70 3
cert_rows_3
cert_pivot_3 3 2 0
cert_heightProof 3
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 454
cert_cover_5 1 2 0 1 5 6 70 454 3
cert_coverFacet 2 428
cert_cover_5 2 0 1 2 4 6 44 428 3
cert_coverFacet 3 372
cert_cover_5 3 1 1 3 4 5 52 372 3
cert_coverFacet 4 568
cert_cover_2 4 3 2 4 8 56 568 3
cert_coverFacet 5 936
cert_cover_5 5 0 2 4 6 8 424 936 3
cert_coverFacet 6 880
cert_cover_5 6 1 3 4 5 8 368 880 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0078

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_one_six_0079.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0079

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 597, 665, 961, 142, 454, 428, 372, 696, 880, 928, 7, 11, 67, 21, 69, 25, 137, 529, 193, 577, 641, 14, 70, 134, 138, 194, 44, 140, 52, 84, 292, 324, 388, 56, 664, 168, 368, 560, 592, 416, 672, 800, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_597, vertices_665, vertices_961, vertices_142, vertices_454, vertices_428, vertices_372, vertices_696, vertices_880, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_25, vertices_137, vertices_529, vertices_193, vertices_577, vertices_641, vertices_14, vertices_70, vertices_134, vertices_138, vertices_194, vertices_44, vertices_140, vertices_52, vertices_84, vertices_292, vertices_324, vertices_388, vertices_56, vertices_664, vertices_168, vertices_368, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_597), (false, vertices_665), (false, vertices_961), (true, vertices_134), (true, vertices_140), (true, vertices_292), (true, vertices_324), (true, vertices_388), (true, vertices_168), (true, vertices_368), (true, vertices_560), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 18 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 12 else
  if p.val = (false, vertices_597) then 15 else
  if p.val = (false, vertices_665) then 17 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_292) then 3 else
  if p.val = (true, vertices_324) then 4 else
  if p.val = (true, vertices_388) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_368) then 19 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(true, vertices_368), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 6 8 664
cert_row_2 1 3 4 5 7 368
cert_row_4 2 0 1 5 6 7 454 70 3
cert_row_4 3 1 2 4 6 7 428 44 3
cert_rows
cert_pivot_2 8 3 0 1
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 454
cert_cover_5 1 2 0 1 5 6 70 454 3
cert_coverFacet 2 428
cert_cover_5 2 3 1 2 4 6 44 428 3
cert_coverFacet 3 372
cert_cover_5 3 1 1 3 4 5 52 372 3
cert_coverFacet 4 696
cert_cover_5 4 0 2 3 4 6 56 696 3
cert_coverFacet 5 880
cert_cover_5 5 1 3 4 5 8 368 880 3
cert_coverFacet 6 928
cert_cover_2 6 6 4 7 8 416 928 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0079

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_one_six_0083.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0083

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 597, 665, 961, 398, 454, 300, 372, 568, 936, 880, 7, 11, 67, 21, 69, 25, 137, 529, 193, 577, 641, 14, 70, 390, 138, 194, 44, 268, 52, 84, 292, 324, 56, 536, 296, 552, 392, 648, 368, 560, 592, 800, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_597, vertices_665, vertices_961, vertices_398, vertices_454, vertices_300, vertices_372, vertices_568, vertices_936, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_25, vertices_137, vertices_529, vertices_193, vertices_577, vertices_641, vertices_14, vertices_70, vertices_390, vertices_138, vertices_194, vertices_44, vertices_268, vertices_52, vertices_84, vertices_292, vertices_324, vertices_56, vertices_536, vertices_296, vertices_552, vertices_392, vertices_648, vertices_368, vertices_560, vertices_592, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_597), (false, vertices_665), (false, vertices_961), (true, vertices_390), (true, vertices_268), (true, vertices_292), (true, vertices_324), (true, vertices_296), (true, vertices_552), (true, vertices_392), (true, vertices_368), (true, vertices_560), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 15 17 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 10 else
  if p.val = (false, vertices_597) then 14 else
  if p.val = (false, vertices_665) then 16 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_390) then 11 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_324) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_368) then 18 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_800) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(true, vertices_368), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 7 390
cert_row_2 1 3 4 5 7 368
cert_row_4 2 2 4 6 7 8 936 296 2
cert_rows_3
cert_pivot_3 3 0 2
cert_heightProof 3
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 300
cert_cover_2 2 2 1 4 7 44 300 3
cert_coverFacet 3 372
cert_cover_5 3 1 1 3 4 5 52 372 3
cert_coverFacet 4 568
cert_cover_2 4 3 2 4 8 56 568 3
cert_coverFacet 5 936
cert_cover_5 5 2 2 4 6 7 296 936 2
cert_coverFacet 6 880
cert_cover_5 6 1 3 4 5 8 368 880 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0083

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_one_six_0084.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0084

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 597, 665, 961, 398, 454, 300, 564, 868, 440, 944, 7, 11, 67, 21, 69, 25, 137, 529, 193, 577, 641, 14, 70, 390, 138, 194, 44, 268, 52, 532, 292, 548, 324, 580, 56, 152, 296, 392, 432, 560, 656, 800, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_597, vertices_665, vertices_961, vertices_398, vertices_454, vertices_300, vertices_564, vertices_868, vertices_440, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_25, vertices_137, vertices_529, vertices_193, vertices_577, vertices_641, vertices_14, vertices_70, vertices_390, vertices_138, vertices_194, vertices_44, vertices_268, vertices_52, vertices_532, vertices_292, vertices_548, vertices_324, vertices_580, vertices_56, vertices_152, vertices_296, vertices_392, vertices_432, vertices_560, vertices_656, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_597), (false, vertices_665), (false, vertices_961), (true, vertices_390), (true, vertices_268), (true, vertices_292), (true, vertices_548), (true, vertices_324), (true, vertices_296), (true, vertices_392), (true, vertices_432), (true, vertices_560), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 15 17 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 10 else
  if p.val = (false, vertices_597) then 14 else
  if p.val = (false, vertices_665) then 16 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_390) then 11 else
  if p.val = (true, vertices_268) then 1 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_548) then 3 else
  if p.val = (true, vertices_324) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_432) then 18 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_800) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(true, vertices_432), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 7 390
cert_row_2 1 3 4 6 7 432
cert_row_4 2 1 4 5 7 8 868 292 2
cert_rows_3
cert_pivot_3 3 0 1
cert_heightProof 3
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 14 398 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 300
cert_cover_2 2 2 1 4 7 44 300 3
cert_coverFacet 3 564
cert_cover_2 3 3 1 4 8 52 564 3
cert_coverFacet 4 868
cert_cover_5 4 2 1 4 5 7 292 868 2
cert_coverFacet 5 440
cert_cover_5 5 1 2 3 4 6 56 440 3
cert_coverFacet 6 944
cert_cover_5 6 1 3 4 6 8 432 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0084

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_one_six_0085.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0085

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 653, 837, 961, 86, 154, 466, 812, 372, 696, 944, 7, 11, 67, 13, 69, 517, 137, 193, 833, 641, 22, 70, 26, 138, 82, 146, 194, 44, 524, 52, 84, 292, 324, 772, 56, 152, 552, 648, 688, 304, 336, 400, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_653, vertices_837, vertices_961, vertices_86, vertices_154, vertices_466, vertices_812, vertices_372, vertices_696, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_69, vertices_517, vertices_137, vertices_193, vertices_833, vertices_641, vertices_22, vertices_70, vertices_26, vertices_138, vertices_82, vertices_146, vertices_194, vertices_44, vertices_524, vertices_52, vertices_84, vertices_292, vertices_324, vertices_772, vertices_56, vertices_152, vertices_552, vertices_648, vertices_688, vertices_304, vertices_336, vertices_400, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_653), (false, vertices_837), (false, vertices_961), (true, vertices_82), (true, vertices_146), (true, vertices_84), (true, vertices_292), (true, vertices_152), (true, vertices_552), (true, vertices_688), (true, vertices_304), (true, vertices_336), (true, vertices_400), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 17 19 20 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 12 else
  if p.val = (false, vertices_653) then 15 else
  if p.val = (false, vertices_837) then 21 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_688) then 18 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(true, vertices_688), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 6 7 466 82 3
cert_row_2 1 3 4 6 8 688
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 1 3 4 5 7 372 52 3
cert_rows
cert_pivot_2 0 6 2 1
cert_heightProof 4
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 466
cert_cover_5 2 0 0 3 5 6 82 466 3
cert_coverFacet 3 812
cert_cover_5 3 2 1 2 4 7 44 812 3
cert_coverFacet 4 372
cert_cover_5 4 3 1 3 4 5 52 372 3
cert_coverFacet 5 696
cert_cover_5 5 1 2 3 4 6 56 696 3
cert_coverFacet 6 944
cert_cover_5 6 1 3 4 6 7 688 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0085

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_one_six_0087.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0087

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 653, 837, 961, 342, 666, 466, 812, 308, 568, 944, 7, 11, 67, 13, 69, 517, 137, 193, 833, 641, 22, 70, 26, 138, 338, 146, 194, 44, 524, 52, 276, 292, 324, 772, 56, 536, 552, 648, 304, 560, 400, 656, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_653, vertices_837, vertices_961, vertices_342, vertices_666, vertices_466, vertices_812, vertices_308, vertices_568, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_69, vertices_517, vertices_137, vertices_193, vertices_833, vertices_641, vertices_22, vertices_70, vertices_26, vertices_138, vertices_338, vertices_146, vertices_194, vertices_44, vertices_524, vertices_52, vertices_276, vertices_292, vertices_324, vertices_772, vertices_56, vertices_536, vertices_552, vertices_648, vertices_304, vertices_560, vertices_400, vertices_656, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_653), (false, vertices_837), (false, vertices_961), (true, vertices_338), (true, vertices_146), (true, vertices_276), (true, vertices_292), (true, vertices_536), (true, vertices_552), (true, vertices_304), (true, vertices_560), (true, vertices_400), (true, vertices_656), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 19 20 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 12 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_837) then 21 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_338) then 13 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_292) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_338), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 5 7 338
cert_row_4 1 0 2 3 6 8 666 26 3
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 3 4 6 7 8 944 304 2
cert_rows
cert_pivot_2 5 0 1 3
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 0 0 1 3 5 22 342 3
cert_coverFacet 1 666
cert_cover_5 1 1 0 2 3 6 26 666 3
cert_coverFacet 2 466
cert_cover_5 2 0 0 3 5 6 338 466 3
cert_coverFacet 3 812
cert_cover_5 3 2 1 2 4 7 44 812 3
cert_coverFacet 4 308
cert_cover_2 4 3 1 4 7 52 308 3
cert_coverFacet 5 568
cert_cover_2 5 3 2 4 8 56 568 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 304 944 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0087

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_one_six_0090.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0090

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 651, 835, 341, 809, 305, 206, 706, 220, 696, 496, 992, 7, 11, 67, 515, 21, 69, 41, 521, 49, 273, 289, 321, 769, 14, 70, 138, 194, 578, 642, 28, 204, 84, 56, 152, 552, 648, 176, 304, 208, 336, 480, 672, 800, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_651, vertices_835, vertices_341, vertices_809, vertices_305, vertices_206, vertices_706, vertices_220, vertices_696, vertices_496, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_515, vertices_21, vertices_69, vertices_41, vertices_521, vertices_49, vertices_273, vertices_289, vertices_321, vertices_769, vertices_14, vertices_70, vertices_138, vertices_194, vertices_578, vertices_642, vertices_28, vertices_204, vertices_84, vertices_56, vertices_152, vertices_552, vertices_648, vertices_176, vertices_304, vertices_208, vertices_336, vertices_480, vertices_672, vertices_800, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_651), (false, vertices_835), (false, vertices_341), (false, vertices_809), (false, vertices_305), (true, vertices_194), (true, vertices_204), (true, vertices_152), (true, vertices_176), (true, vertices_208), (true, vertices_480), (true, vertices_672), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 15 17 18 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_651) then 9 else
  if p.val = (false, vertices_835) then 10 else
  if p.val = (false, vertices_341) then 13 else
  if p.val = (false, vertices_809) then 16 else
  if p.val = (false, vertices_305) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_204) then 14 else
  if p.val = (true, vertices_152) then 3 else
  if p.val = (true, vertices_176) then 4 else
  if p.val = (true, vertices_208) then 5 else
  if p.val = (true, vertices_480) then 19 else
  if p.val = (true, vertices_672) then 6 else
  if p.val = (true, vertices_704) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_305), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 10 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inl 4
  | 19 => Sum.inr ⟨(true, vertices_480), by decide +kernel⟩
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 4 5 6 7 480
cert_row_2 1 1 2 5 6 204
cert_row_4 2 2 3 4 6 8 696 56 3
cert_rows_3
cert_pivot_3 1 7 2
cert_heightProof 3
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 14 206 3
cert_coverFacet 1 706
cert_cover_2 1 5 0 6 8 194 706 3
cert_coverFacet 2 220
cert_cover_5 2 1 1 2 3 5 28 220 3
cert_coverFacet 3 696
cert_cover_5 3 2 2 3 4 6 56 696 3
cert_coverFacet 4 496
cert_cover_5 4 0 3 4 5 6 176 496 2
cert_coverFacet 5 992
cert_cover_5 5 0 4 5 6 8 480 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0090

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_one_six_0091.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0091

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 651, 835, 341, 681, 817, 206, 706, 220, 440, 464, 992, 7, 11, 67, 515, 21, 69, 41, 649, 49, 273, 545, 321, 769, 14, 70, 138, 194, 578, 642, 28, 204, 84, 56, 152, 168, 304, 208, 336, 400, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_651, vertices_835, vertices_341, vertices_681, vertices_817, vertices_206, vertices_706, vertices_220, vertices_440, vertices_464, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_515, vertices_21, vertices_69, vertices_41, vertices_649, vertices_49, vertices_273, vertices_545, vertices_321, vertices_769, vertices_14, vertices_70, vertices_138, vertices_194, vertices_578, vertices_642, vertices_28, vertices_204, vertices_84, vertices_56, vertices_152, vertices_168, vertices_304, vertices_208, vertices_336, vertices_400, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_651), (false, vertices_835), (false, vertices_341), (false, vertices_681), (false, vertices_817), (true, vertices_194), (true, vertices_204), (true, vertices_152), (true, vertices_208), (true, vertices_400), (true, vertices_416), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 10 14 17 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 11 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_651) then 15 else
  if p.val = (false, vertices_835) then 9 else
  if p.val = (false, vertices_341) then 12 else
  if p.val = (false, vertices_681) then 16 else
  if p.val = (false, vertices_817) then 18 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_204) then 13 else
  if p.val = (true, vertices_152) then 2 else
  if p.val = (true, vertices_208) then 3 else
  if p.val = (true, vertices_400) then 4 else
  if p.val = (true, vertices_416) then 5 else
  if p.val = (true, vertices_448) then 6 else
  if p.val = (true, vertices_704) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 5 6 204
cert_row_4 1 2 3 4 6 7 440 56 3
cert_row_4 2 4 5 6 7 8 992 416 1
cert_rows_3
cert_pivot_3 2 1 4
cert_heightProof 3
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 706
cert_cover_2 1 5 0 6 8 194 706 3
cert_coverFacet 2 220
cert_cover_5 2 0 1 2 3 5 28 220 3
cert_coverFacet 3 440
cert_cover_5 3 1 2 3 4 6 56 440 3
cert_coverFacet 4 464
cert_cover_2 4 5 3 6 7 208 464 3
cert_coverFacet 5 992
cert_cover_5 5 2 4 5 6 7 416 992 1
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0091

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_one_six_0092.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0092

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 651, 835, 341, 809, 305, 206, 962, 220, 696, 496, 928, 7, 11, 67, 515, 21, 69, 41, 521, 49, 273, 289, 321, 769, 14, 70, 138, 194, 834, 642, 28, 204, 84, 56, 152, 552, 648, 176, 304, 208, 336, 416, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_651, vertices_835, vertices_341, vertices_809, vertices_305, vertices_206, vertices_962, vertices_220, vertices_696, vertices_496, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_515, vertices_21, vertices_69, vertices_41, vertices_521, vertices_49, vertices_273, vertices_289, vertices_321, vertices_769, vertices_14, vertices_70, vertices_138, vertices_194, vertices_834, vertices_642, vertices_28, vertices_204, vertices_84, vertices_56, vertices_152, vertices_552, vertices_648, vertices_176, vertices_304, vertices_208, vertices_336, vertices_416, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_651), (false, vertices_835), (false, vertices_341), (false, vertices_809), (false, vertices_305), (true, vertices_194), (true, vertices_204), (true, vertices_152), (true, vertices_176), (true, vertices_208), (true, vertices_416), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 17 19 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_651) then 11 else
  if p.val = (false, vertices_835) then 12 else
  if p.val = (false, vertices_341) then 15 else
  if p.val = (false, vertices_809) then 18 else
  if p.val = (false, vertices_305) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_204) then 16 else
  if p.val = (true, vertices_152) then 3 else
  if p.val = (true, vertices_176) then 4 else
  if p.val = (true, vertices_208) then 5 else
  if p.val = (true, vertices_416) then 6 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_305), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 5 7 8 834
cert_row_2 1 1 2 5 6 204
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 3 4 5 6 7 496 176 2
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 14 206 3
cert_coverFacet 1 962
cert_cover_5 1 0 0 5 6 7 194 962 3
cert_coverFacet 2 220
cert_cover_5 2 1 1 2 3 5 28 220 3
cert_coverFacet 3 696
cert_cover_5 3 2 2 3 4 6 56 696 3
cert_coverFacet 4 496
cert_cover_5 4 3 3 4 5 6 176 496 2
cert_coverFacet 5 928
cert_cover_2 5 6 4 7 8 416 928 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0092

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_one_six_0093.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0093

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 651, 835, 341, 553, 817, 206, 962, 220, 184, 936, 496, 7, 11, 67, 515, 21, 69, 41, 521, 49, 273, 545, 321, 769, 14, 70, 138, 194, 834, 642, 28, 204, 84, 56, 152, 168, 552, 648, 176, 304, 208, 336, 416, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_651, vertices_835, vertices_341, vertices_553, vertices_817, vertices_206, vertices_962, vertices_220, vertices_184, vertices_936, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_515, vertices_21, vertices_69, vertices_41, vertices_521, vertices_49, vertices_273, vertices_545, vertices_321, vertices_769, vertices_14, vertices_70, vertices_138, vertices_194, vertices_834, vertices_642, vertices_28, vertices_204, vertices_84, vertices_56, vertices_152, vertices_168, vertices_552, vertices_648, vertices_176, vertices_304, vertices_208, vertices_336, vertices_416, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_651), (false, vertices_835), (false, vertices_341), (false, vertices_553), (false, vertices_817), (true, vertices_194), (true, vertices_204), (true, vertices_152), (true, vertices_168), (true, vertices_176), (true, vertices_208), (true, vertices_416), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 17 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_651) then 11 else
  if p.val = (false, vertices_835) then 12 else
  if p.val = (false, vertices_341) then 15 else
  if p.val = (false, vertices_553) then 1 else
  if p.val = (false, vertices_817) then 19 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_204) then 16 else
  if p.val = (true, vertices_152) then 3 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_176) then 5 else
  if p.val = (true, vertices_208) then 6 else
  if p.val = (true, vertices_416) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_896) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 5 7 8 834
cert_row_2 1 1 2 5 6 204
cert_row_4 2 2 4 6 7 8 936 168 3
cert_row_4 3 3 4 5 6 7 496 176 2
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 14 206 3
cert_coverFacet 1 962
cert_cover_5 1 0 0 5 6 7 194 962 3
cert_coverFacet 2 220
cert_cover_5 2 1 1 2 3 5 28 220 3
cert_coverFacet 3 184
cert_cover_2 3 3 2 4 6 56 184 3
cert_coverFacet 4 936
cert_cover_5 4 2 2 4 6 7 168 936 3
cert_coverFacet 5 496
cert_cover_5 5 3 3 4 5 6 176 496 2
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0093

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_one_six_0094.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0094

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 651, 835, 341, 681, 817, 206, 706, 284, 460, 440, 992, 7, 11, 67, 515, 21, 69, 41, 649, 49, 273, 545, 321, 769, 14, 70, 138, 194, 578, 642, 28, 204, 268, 276, 324, 56, 280, 168, 392, 304, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_651, vertices_835, vertices_341, vertices_681, vertices_817, vertices_206, vertices_706, vertices_284, vertices_460, vertices_440, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_515, vertices_21, vertices_69, vertices_41, vertices_649, vertices_49, vertices_273, vertices_545, vertices_321, vertices_769, vertices_14, vertices_70, vertices_138, vertices_194, vertices_578, vertices_642, vertices_28, vertices_204, vertices_268, vertices_276, vertices_324, vertices_56, vertices_280, vertices_168, vertices_392, vertices_304, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_651), (false, vertices_835), (false, vertices_341), (false, vertices_681), (false, vertices_817), (true, vertices_194), (true, vertices_204), (true, vertices_268), (true, vertices_280), (true, vertices_392), (true, vertices_416), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 10 14 17 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 11 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_651) then 15 else
  if p.val = (false, vertices_835) then 9 else
  if p.val = (false, vertices_341) then 12 else
  if p.val = (false, vertices_681) then 16 else
  if p.val = (false, vertices_817) then 18 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_204) then 13 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_280) then 3 else
  if p.val = (true, vertices_392) then 4 else
  if p.val = (true, vertices_416) then 5 else
  if p.val = (true, vertices_448) then 6 else
  if p.val = (true, vertices_704) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 5 6 204
cert_row_4 1 2 3 4 6 7 440 56 3
cert_row_4 2 4 5 6 7 8 992 416 1
cert_rows_3
cert_pivot_3 2 1 4
cert_heightProof 3
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 706
cert_cover_2 1 5 0 6 8 194 706 3
cert_coverFacet 2 284
cert_cover_2 2 2 1 3 7 28 284 3
cert_coverFacet 3 460
cert_cover_5 3 0 1 2 5 7 204 460 3
cert_coverFacet 4 440
cert_cover_5 4 1 2 3 4 6 56 440 3
cert_coverFacet 5 992
cert_cover_5 5 2 4 5 6 7 416 992 1
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0094

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_one_six_0095.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0095

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 139, 277, 453, 681, 433, 78, 714, 604, 852, 824, 992, 7, 11, 131, 21, 197, 261, 41, 137, 49, 273, 161, 385, 14, 70, 74, 138, 194, 28, 76, 596, 276, 324, 56, 536, 552, 584, 648, 304, 784, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_139, vertices_277, vertices_453, vertices_681, vertices_433, vertices_78, vertices_714, vertices_604, vertices_852, vertices_824, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_197, vertices_261, vertices_41, vertices_137, vertices_49, vertices_273, vertices_161, vertices_385, vertices_14, vertices_70, vertices_74, vertices_138, vertices_194, vertices_28, vertices_76, vertices_596, vertices_276, vertices_324, vertices_56, vertices_536, vertices_552, vertices_584, vertices_648, vertices_304, vertices_784, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_139), (false, vertices_277), (false, vertices_453), (false, vertices_681), (false, vertices_433), (true, vertices_74), (true, vertices_76), (true, vertices_596), (true, vertices_536), (true, vertices_584), (true, vertices_784), (true, vertices_800), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 17 11 14 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_199) then 18 else
  if p.val = (false, vertices_139) then 0 else
  if p.val = (false, vertices_277) then 1 else
  if p.val = (false, vertices_453) then 19 else
  if p.val = (false, vertices_681) then 13 else
  if p.val = (false, vertices_433) then 15 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_596) then 16 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_784) then 6 else
  if p.val = (true, vertices_800) then 7 else
  if p.val = (true, vertices_704) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_139), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inl 2
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_596), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 5 8 596
cert_row_4 1 0 2 5 6 8 714 74 3
cert_row_4 2 2 3 4 7 8 824 56 3
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
cert_coverFacet 4 824
cert_cover_5 4 2 2 3 4 7 56 824 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 416 992 1
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0095

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_one_six_0096.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0096

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 139, 277, 453, 425, 817, 78, 714, 604, 852, 696, 992, 7, 11, 131, 21, 197, 261, 41, 137, 49, 273, 289, 385, 14, 70, 74, 138, 194, 28, 76, 596, 276, 324, 56, 536, 168, 584, 648, 560, 784, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_139, vertices_277, vertices_453, vertices_425, vertices_817, vertices_78, vertices_714, vertices_604, vertices_852, vertices_696, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_197, vertices_261, vertices_41, vertices_137, vertices_49, vertices_273, vertices_289, vertices_385, vertices_14, vertices_70, vertices_74, vertices_138, vertices_194, vertices_28, vertices_76, vertices_596, vertices_276, vertices_324, vertices_56, vertices_536, vertices_168, vertices_584, vertices_648, vertices_560, vertices_784, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_139), (false, vertices_277), (false, vertices_453), (false, vertices_425), (false, vertices_817), (true, vertices_74), (true, vertices_76), (true, vertices_596), (true, vertices_536), (true, vertices_584), (true, vertices_648), (true, vertices_672), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 17 11 14 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_199) then 18 else
  if p.val = (false, vertices_139) then 0 else
  if p.val = (false, vertices_277) then 1 else
  if p.val = (false, vertices_453) then 19 else
  if p.val = (false, vertices_425) then 13 else
  if p.val = (false, vertices_817) then 15 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_596) then 16 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_704) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_139), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inl 2
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_596), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
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
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 416 992 1
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0096

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_one_six_0097.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0097

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 139, 707, 597, 425, 689, 206, 796, 460, 836, 824, 992, 7, 11, 67, 131, 21, 69, 41, 137, 49, 529, 161, 577, 641, 14, 70, 138, 194, 28, 204, 268, 532, 324, 580, 772, 56, 792, 296, 392, 560, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_139, vertices_707, vertices_597, vertices_425, vertices_689, vertices_206, vertices_796, vertices_460, vertices_836, vertices_824, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_131, vertices_21, vertices_69, vertices_41, vertices_137, vertices_49, vertices_529, vertices_161, vertices_577, vertices_641, vertices_14, vertices_70, vertices_138, vertices_194, vertices_28, vertices_204, vertices_268, vertices_532, vertices_324, vertices_580, vertices_772, vertices_56, vertices_792, vertices_296, vertices_392, vertices_560, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_139), (false, vertices_707), (false, vertices_597), (false, vertices_425), (false, vertices_689), (true, vertices_204), (true, vertices_268), (true, vertices_324), (true, vertices_772), (true, vertices_792), (true, vertices_800), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 10 14 17 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 11 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_139) then 1 else
  if p.val = (false, vertices_707) then 9 else
  if p.val = (false, vertices_597) then 12 else
  if p.val = (false, vertices_425) then 15 else
  if p.val = (false, vertices_689) then 18 else
  if p.val = (true, vertices_204) then 13 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_324) then 3 else
  if p.val = (true, vertices_772) then 4 else
  if p.val = (true, vertices_792) then 16 else
  if p.val = (true, vertices_800) then 5 else
  if p.val = (true, vertices_448) then 6 else
  if p.val = (true, vertices_832) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_139), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_792), by decide +kernel⟩
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0097

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_one_six_0098.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0098

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 267, 835, 597, 425, 817, 206, 458, 668, 708, 696, 992, 7, 11, 67, 259, 21, 69, 41, 265, 49, 529, 289, 577, 769, 14, 70, 202, 266, 322, 28, 140, 532, 196, 580, 644, 56, 664, 168, 392, 560, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_267, vertices_835, vertices_597, vertices_425, vertices_817, vertices_206, vertices_458, vertices_668, vertices_708, vertices_696, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_41, vertices_265, vertices_49, vertices_529, vertices_289, vertices_577, vertices_769, vertices_14, vertices_70, vertices_202, vertices_266, vertices_322, vertices_28, vertices_140, vertices_532, vertices_196, vertices_580, vertices_644, vertices_56, vertices_664, vertices_168, vertices_392, vertices_560, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_267), (false, vertices_835), (false, vertices_597), (false, vertices_425), (false, vertices_817), (true, vertices_202), (true, vertices_140), (true, vertices_196), (true, vertices_644), (true, vertices_664), (true, vertices_672), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 14 17 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_267) then 1 else
  if p.val = (false, vertices_835) then 9 else
  if p.val = (false, vertices_597) then 13 else
  if p.val = (false, vertices_425) then 15 else
  if p.val = (false, vertices_817) then 18 else
  if p.val = (true, vertices_202) then 10 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_196) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_664) then 16 else
  if p.val = (true, vertices_672) then 5 else
  if p.val = (true, vertices_448) then 6 else
  if p.val = (true, vertices_704) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_664), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 6 202
cert_row_2 1 2 3 6 8 664
cert_row_4 2 4 5 6 7 8 992 416 1
cert_rows_3
cert_pivot_3 2 0 4
cert_heightProof 3
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 7 202 458 3
cert_coverFacet 2 668
cert_cover_5 2 1 1 2 3 6 28 668 3
cert_coverFacet 3 708
cert_cover_2 3 5 1 6 8 196 708 3
cert_coverFacet 4 696
cert_cover_5 4 1 2 3 4 6 56 696 3
cert_coverFacet 5 992
cert_cover_5 5 2 4 5 6 7 416 992 1
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0098

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_one_six_0099.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0099

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 597, 665, 961, 270, 838, 458, 300, 692, 932, 440, 7, 11, 67, 21, 69, 25, 137, 529, 193, 577, 641, 14, 70, 262, 202, 266, 322, 44, 268, 52, 532, 676, 292, 580, 772, 56, 152, 296, 392, 176, 656, 416, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_597, vertices_665, vertices_961, vertices_270, vertices_838, vertices_458, vertices_300, vertices_692, vertices_932, vertices_440] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_25, vertices_137, vertices_529, vertices_193, vertices_577, vertices_641, vertices_14, vertices_70, vertices_262, vertices_202, vertices_266, vertices_322, vertices_44, vertices_268, vertices_52, vertices_532, vertices_676, vertices_292, vertices_580, vertices_772, vertices_56, vertices_152, vertices_296, vertices_392, vertices_176, vertices_656, vertices_416, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_597), (false, vertices_665), (false, vertices_961), (true, vertices_262), (true, vertices_266), (true, vertices_322), (true, vertices_268), (true, vertices_676), (true, vertices_292), (true, vertices_772), (true, vertices_296), (true, vertices_392), (true, vertices_176), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 17 19 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 12 else
  if p.val = (false, vertices_597) then 15 else
  if p.val = (false, vertices_665) then 18 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_676) then 16 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_772) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_392) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_416) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_676), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
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
cert_row_4 0 2 3 4 6 7 440 56 3
cert_row_2 1 0 2 5 6 202
cert_row_2 2 1 4 6 8 676
cert_row_4 3 0 1 5 7 8 838 70 3
cert_rows
cert_pivot_2 3 2 4 0
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 838
cert_cover_5 1 3 0 1 5 7 70 838 3
cert_coverFacet 2 458
cert_cover_5 2 1 0 2 5 7 202 458 3
cert_coverFacet 3 300
cert_cover_2 3 2 1 4 7 44 300 3
cert_coverFacet 4 692
cert_cover_5 4 2 1 3 4 6 52 692 3
cert_coverFacet 5 932
cert_cover_5 5 2 1 4 6 7 676 932 3
cert_coverFacet 6 440
cert_cover_5 6 0 2 3 4 6 56 440 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0099

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_one_six_0100.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0100

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 597, 665, 961, 270, 838, 458, 428, 820, 184, 944, 7, 11, 67, 21, 69, 25, 137, 529, 193, 577, 641, 14, 70, 262, 202, 266, 322, 44, 268, 52, 532, 292, 580, 772, 56, 152, 168, 392, 176, 816, 656, 416, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_597, vertices_665, vertices_961, vertices_270, vertices_838, vertices_458, vertices_428, vertices_820, vertices_184, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_25, vertices_137, vertices_529, vertices_193, vertices_577, vertices_641, vertices_14, vertices_70, vertices_262, vertices_202, vertices_266, vertices_322, vertices_44, vertices_268, vertices_52, vertices_532, vertices_292, vertices_580, vertices_772, vertices_56, vertices_152, vertices_168, vertices_392, vertices_176, vertices_816, vertices_656, vertices_416, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_597), (false, vertices_665), (false, vertices_961), (true, vertices_262), (true, vertices_266), (true, vertices_322), (true, vertices_268), (true, vertices_292), (true, vertices_772), (true, vertices_168), (true, vertices_392), (true, vertices_176), (true, vertices_816), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 18 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 12 else
  if p.val = (false, vertices_597) then 15 else
  if p.val = (false, vertices_665) then 17 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_772) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_392) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_816) then 19 else
  if p.val = (true, vertices_416) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(true, vertices_816), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 7 8 816
cert_row_4 1 0 1 5 7 8 838 70 3
cert_row_2 2 0 2 5 6 202
cert_row_4 3 1 2 4 6 7 428 44 3
cert_rows
cert_pivot_2 3 8 0 1
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 838
cert_cover_5 1 1 0 1 5 7 70 838 3
cert_coverFacet 2 458
cert_cover_5 2 2 0 2 5 7 202 458 3
cert_coverFacet 3 428
cert_cover_5 3 3 1 2 4 6 44 428 3
cert_coverFacet 4 820
cert_cover_5 4 0 1 3 4 7 52 820 3
cert_coverFacet 5 184
cert_cover_2 5 3 2 4 6 56 184 3
cert_coverFacet 6 944
cert_cover_5 6 0 3 4 6 7 176 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0100

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_one_six_0101.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0101

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 267, 835, 597, 425, 817, 206, 458, 668, 964, 696, 928, 7, 11, 67, 259, 21, 69, 41, 265, 49, 529, 289, 577, 769, 14, 70, 202, 266, 322, 28, 140, 532, 196, 580, 644, 56, 664, 168, 392, 560, 416, 672, 800, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_267, vertices_835, vertices_597, vertices_425, vertices_817, vertices_206, vertices_458, vertices_668, vertices_964, vertices_696, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_41, vertices_265, vertices_49, vertices_529, vertices_289, vertices_577, vertices_769, vertices_14, vertices_70, vertices_202, vertices_266, vertices_322, vertices_28, vertices_140, vertices_532, vertices_196, vertices_580, vertices_644, vertices_56, vertices_664, vertices_168, vertices_392, vertices_560, vertices_416, vertices_672, vertices_800, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_267), (false, vertices_835), (false, vertices_597), (false, vertices_425), (false, vertices_817), (true, vertices_202), (true, vertices_140), (true, vertices_196), (true, vertices_644), (true, vertices_664), (true, vertices_672), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 8 11 14 17 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_267) then 1 else
  if p.val = (false, vertices_835) then 9 else
  if p.val = (false, vertices_597) then 13 else
  if p.val = (false, vertices_425) then 15 else
  if p.val = (false, vertices_817) then 18 else
  if p.val = (true, vertices_202) then 10 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_196) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_664) then 16 else
  if p.val = (true, vertices_672) then 5 else
  if p.val = (true, vertices_448) then 6 else
  if p.val = (true, vertices_896) then 7 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 8 => Sum.inl 0
  | 9 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_664), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 6 202
cert_row_2 1 2 3 6 8 664
cert_row_4 2 1 5 6 7 8 964 196 3
cert_rows_3
cert_pivot_3 2 0 1
cert_heightProof 3
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 7 202 458 3
cert_coverFacet 2 668
cert_cover_5 2 1 1 2 3 6 28 668 3
cert_coverFacet 3 964
cert_cover_5 3 2 1 5 6 7 196 964 3
cert_coverFacet 4 696
cert_cover_5 4 1 2 3 4 6 56 696 3
cert_coverFacet 5 928
cert_cover_2 5 6 4 7 8 416 928 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0101

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_0720 : Certifies 720 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0048.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0721 : Certifies 721 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0049.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0722 : Certifies 722 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0062.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0723 : Certifies 723 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0063.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0724 : Certifies 724 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0064.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0725 : Certifies 725 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0071.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0726 : Certifies 726 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0072.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0727 : Certifies 727 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0073.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0728 : Certifies 728 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0074.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0729 : Certifies 729 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0075.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0730 : Certifies 730 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0076.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0731 : Certifies 731 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0077.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0732 : Certifies 732 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0078.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0733 : Certifies 733 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0079.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0734 : Certifies 734 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0083.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0735 : Certifies 735 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0084.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0736 : Certifies 736 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0085.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0737 : Certifies 737 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0087.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0738 : Certifies 738 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0090.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0739 : Certifies 739 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0091.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0740 : Certifies 740 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0092.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0741 : Certifies 741 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0093.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0742 : Certifies 742 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0094.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0743 : Certifies 743 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0095.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0744 : Certifies 744 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0096.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0745 : Certifies 745 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0097.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0746 : Certifies 746 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0098.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0747 : Certifies 747 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0099.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0748 : Certifies 748 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0100.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0749 : Certifies 749 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0101.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B024 (j : Fin 30) :
    Certifies (720 + j.val) := by
  fin_cases j
  · exact projection_0720
  · exact projection_0721
  · exact projection_0722
  · exact projection_0723
  · exact projection_0724
  · exact projection_0725
  · exact projection_0726
  · exact projection_0727
  · exact projection_0728
  · exact projection_0729
  · exact projection_0730
  · exact projection_0731
  · exact projection_0732
  · exact projection_0733
  · exact projection_0734
  · exact projection_0735
  · exact projection_0736
  · exact projection_0737
  · exact projection_0738
  · exact projection_0739
  · exact projection_0740
  · exact projection_0741
  · exact projection_0742
  · exact projection_0743
  · exact projection_0744
  · exact projection_0745
  · exact projection_0746
  · exact projection_0747
  · exact projection_0748
  · exact projection_0749

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
