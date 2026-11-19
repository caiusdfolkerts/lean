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
/- Source: ProjectionCertificates/R_one_six_0220.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0220

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 323, 653, 961, 86, 346, 812, 244, 932, 376, 480, 7, 11, 67, 259, 13, 133, 521, 193, 321, 641, 769, 22, 70, 26, 266, 82, 322, 44, 524, 52, 84, 164, 804, 196, 644, 56, 344, 296, 776, 112, 224, 352, 416, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_323, vertices_653, vertices_961, vertices_86, vertices_346, vertices_812, vertices_244, vertices_932, vertices_376, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_133, vertices_521, vertices_193, vertices_321, vertices_641, vertices_769, vertices_22, vertices_70, vertices_26, vertices_266, vertices_82, vertices_322, vertices_44, vertices_524, vertices_52, vertices_84, vertices_164, vertices_804, vertices_196, vertices_644, vertices_56, vertices_344, vertices_296, vertices_776, vertices_112, vertices_224, vertices_352, vertices_416, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_323), (false, vertices_653), (false, vertices_961), (true, vertices_82), (true, vertices_84), (true, vertices_164), (true, vertices_804), (true, vertices_344), (true, vertices_296), (true, vertices_112), (true, vertices_224), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 16 18 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_199) then 10 else
  if p.val = (false, vertices_779) then 11 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_653) then 14 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_804) then 15 else
  if p.val = (true, vertices_344) then 17 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_112) then 5 else
  if p.val = (true, vertices_224) then 6 else
  if p.val = (true, vertices_352) then 7 else
  if p.val = (true, vertices_416) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_804), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(true, vertices_344), by decide +kernel⟩
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
cert_row_2 0 1 4 7 8 804
cert_row_2 1 2 3 5 7 344
cert_row_4 2 1 3 4 5 6 244 52 3
cert_rows_3
cert_pivot_3 2 8 1
cert_heightProof 3
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 346
cert_cover_5 1 1 0 2 3 5 26 346 3
cert_coverFacet 2 812
cert_cover_5 2 0 1 2 4 7 44 812 3
cert_coverFacet 3 244
cert_cover_5 3 2 1 3 4 5 52 244 3
cert_coverFacet 4 932
cert_cover_5 4 0 1 4 6 7 164 932 3
cert_coverFacet 5 376
cert_cover_5 5 1 2 3 4 5 56 376 3
cert_coverFacet 6 480
cert_cover_2 6 5 4 6 7 224 480 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0220

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_one_six_0221.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0221

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 323, 653, 961, 86, 346, 684, 436, 468, 824, 928, 7, 11, 67, 259, 13, 133, 521, 193, 321, 641, 769, 22, 70, 26, 266, 82, 322, 44, 652, 52, 84, 404, 164, 196, 56, 280, 552, 776, 304, 336, 416, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_323, vertices_653, vertices_961, vertices_86, vertices_346, vertices_684, vertices_436, vertices_468, vertices_824, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_133, vertices_521, vertices_193, vertices_321, vertices_641, vertices_769, vertices_22, vertices_70, vertices_26, vertices_266, vertices_82, vertices_322, vertices_44, vertices_652, vertices_52, vertices_84, vertices_404, vertices_164, vertices_196, vertices_56, vertices_280, vertices_552, vertices_776, vertices_304, vertices_336, vertices_416, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_323), (false, vertices_653), (false, vertices_961), (true, vertices_82), (true, vertices_84), (true, vertices_404), (true, vertices_164), (true, vertices_280), (true, vertices_552), (true, vertices_304), (true, vertices_336), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 18 19 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_404) then 17 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_404), by decide +kernel⟩
  | 18 => Sum.inl 2
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
cert_row_4 0 0 2 3 5 7 346 26 3
cert_row_4 1 2 3 4 7 8 824 56 3
cert_row_2 2 1 3 6 7 404
cert_row_2 3 1 2 6 8 652
cert_rows
cert_pivot_2 0 4 3 1
cert_heightProof 4
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 346
cert_cover_5 1 0 0 2 3 5 26 346 3
cert_coverFacet 2 684
cert_cover_5 2 3 1 2 4 6 44 684 3
cert_coverFacet 3 436
cert_cover_5 3 2 1 3 4 6 52 436 3
cert_coverFacet 4 468
cert_cover_5 4 2 1 3 5 6 84 468 3
cert_coverFacet 5 824
cert_cover_5 5 1 2 3 4 7 56 824 3
cert_coverFacet 6 928
cert_cover_2 6 6 4 7 8 416 928 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0221

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_one_six_0222.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0222

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 323, 653, 961, 86, 346, 684, 372, 484, 824, 928, 7, 11, 67, 259, 13, 133, 521, 193, 321, 641, 769, 22, 70, 26, 266, 82, 322, 44, 652, 52, 84, 356, 164, 196, 56, 280, 552, 776, 304, 336, 416, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_323, vertices_653, vertices_961, vertices_86, vertices_346, vertices_684, vertices_372, vertices_484, vertices_824, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_133, vertices_521, vertices_193, vertices_321, vertices_641, vertices_769, vertices_22, vertices_70, vertices_26, vertices_266, vertices_82, vertices_322, vertices_44, vertices_652, vertices_52, vertices_84, vertices_356, vertices_164, vertices_196, vertices_56, vertices_280, vertices_552, vertices_776, vertices_304, vertices_336, vertices_416, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_323), (false, vertices_653), (false, vertices_961), (true, vertices_82), (true, vertices_84), (true, vertices_356), (true, vertices_164), (true, vertices_280), (true, vertices_552), (true, vertices_304), (true, vertices_336), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 18 19 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_356) then 17 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_356), by decide +kernel⟩
  | 18 => Sum.inl 2
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
cert_row_2 0 1 2 6 8 652
cert_row_2 1 1 4 5 7 356
cert_row_4 2 0 2 3 5 7 346 26 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 6 1 0 2
cert_heightProof 4
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 346
cert_cover_5 1 2 0 2 3 5 26 346 3
cert_coverFacet 2 684
cert_cover_5 2 0 1 2 4 6 44 684 3
cert_coverFacet 3 372
cert_cover_5 3 1 1 3 4 5 52 372 3
cert_coverFacet 4 484
cert_cover_5 4 1 1 4 5 6 356 484 3
cert_coverFacet 5 824
cert_cover_5 5 3 2 3 4 7 56 824 3
cert_coverFacet 6 928
cert_cover_2 6 6 4 7 8 416 928 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0222

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_one_six_0223.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0223

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 323, 653, 961, 86, 346, 684, 244, 824, 496, 928, 7, 11, 67, 259, 13, 133, 521, 193, 321, 641, 769, 22, 70, 26, 266, 82, 322, 44, 652, 52, 84, 164, 196, 56, 280, 552, 776, 240, 304, 336, 416, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_323, vertices_653, vertices_961, vertices_86, vertices_346, vertices_684, vertices_244, vertices_824, vertices_496, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_133, vertices_521, vertices_193, vertices_321, vertices_641, vertices_769, vertices_22, vertices_70, vertices_26, vertices_266, vertices_82, vertices_322, vertices_44, vertices_652, vertices_52, vertices_84, vertices_164, vertices_196, vertices_56, vertices_280, vertices_552, vertices_776, vertices_240, vertices_304, vertices_336, vertices_416, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_323), (false, vertices_653), (false, vertices_961), (true, vertices_82), (true, vertices_84), (true, vertices_164), (true, vertices_280), (true, vertices_552), (true, vertices_240), (true, vertices_304), (true, vertices_336), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_240) then 19 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
cert_nodeAtPriority_38 323 82 84 164 280 552 304 336 416 672 800 199 779 653 240
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 8 652
cert_row_2 1 3 4 5 6 240
cert_row_4 2 0 2 3 5 7 346 26 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 346
cert_cover_5 1 2 0 2 3 5 26 346 3
cert_coverFacet 2 684
cert_cover_5 2 0 1 2 4 6 44 684 3
cert_coverFacet 3 244
cert_cover_5 3 1 1 3 4 5 52 244 3
cert_coverFacet 4 824
cert_cover_5 4 3 2 3 4 7 56 824 3
cert_coverFacet 5 496
cert_cover_5 5 1 3 4 5 7 240 496 3
cert_coverFacet 6 928
cert_cover_2 6 6 4 7 8 416 928 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0223

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_one_six_0224.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0224

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 323, 653, 961, 342, 282, 684, 244, 824, 496, 928, 7, 11, 67, 259, 13, 133, 521, 193, 321, 641, 769, 22, 70, 26, 266, 274, 322, 44, 652, 52, 84, 164, 196, 56, 280, 552, 776, 240, 304, 336, 416, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_323, vertices_653, vertices_961, vertices_342, vertices_282, vertices_684, vertices_244, vertices_824, vertices_496, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_133, vertices_521, vertices_193, vertices_321, vertices_641, vertices_769, vertices_22, vertices_70, vertices_26, vertices_266, vertices_274, vertices_322, vertices_44, vertices_652, vertices_52, vertices_84, vertices_164, vertices_196, vertices_56, vertices_280, vertices_552, vertices_776, vertices_240, vertices_304, vertices_336, vertices_416, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_323), (false, vertices_653), (false, vertices_961), (true, vertices_274), (true, vertices_84), (true, vertices_164), (true, vertices_280), (true, vertices_552), (true, vertices_240), (true, vertices_304), (true, vertices_336), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_240) then 19 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
cert_nodeAtPriority_38 323 274 84 164 280 552 304 336 416 672 800 199 779 653 240
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 7 342 22 3
cert_row_2 1 3 4 5 6 240
cert_row_2 2 1 2 6 8 652
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 0 0 1 3 5 22 342 3
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 684
cert_cover_5 2 2 1 2 4 6 44 684 3
cert_coverFacet 3 244
cert_cover_5 3 1 1 3 4 5 52 244 3
cert_coverFacet 4 824
cert_cover_5 4 3 2 3 4 7 56 824 3
cert_coverFacet 5 496
cert_cover_5 5 1 3 4 5 7 240 496 3
cert_coverFacet 6 928
cert_cover_2 6 6 4 7 8 416 928 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0224

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_one_six_0225.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0225

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 651, 341, 233, 369, 782, 326, 962, 284, 824, 680, 992, 7, 11, 131, 21, 69, 41, 137, 49, 337, 97, 193, 14, 70, 262, 522, 194, 322, 642, 770, 28, 268, 276, 324, 56, 280, 168, 552, 648, 776, 304, 224, 352, 672, 800, 960]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_651, vertices_341, vertices_233, vertices_369, vertices_782, vertices_326, vertices_962, vertices_284, vertices_824, vertices_680, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_69, vertices_41, vertices_137, vertices_49, vertices_337, vertices_97, vertices_193, vertices_14, vertices_70, vertices_262, vertices_522, vertices_194, vertices_322, vertices_642, vertices_770, vertices_28, vertices_268, vertices_276, vertices_324, vertices_56, vertices_280, vertices_168, vertices_552, vertices_648, vertices_776, vertices_304, vertices_224, vertices_352, vertices_672, vertices_800, vertices_960] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_651), (false, vertices_341), (false, vertices_233), (false, vertices_369), (true, vertices_262), (true, vertices_322), (true, vertices_770), (true, vertices_268), (true, vertices_280), (true, vertices_552), (true, vertices_776), (true, vertices_672), (true, vertices_800), (true, vertices_960)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 14 16 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_199) then 10 else
  if p.val = (false, vertices_651) then 11 else
  if p.val = (false, vertices_341) then 17 else
  if p.val = (false, vertices_233) then 15 else
  if p.val = (false, vertices_369) then 18 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_960) then 21 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 11 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 16 => Sum.inl 3
  | 17 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
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
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 194 962 3
cert_coverFacet 3 284
cert_cover_2 3 2 1 3 7 28 284 3
cert_coverFacet 4 824
cert_cover_5 4 2 2 3 4 7 56 824 3
cert_coverFacet 5 680
cert_cover_2 5 4 2 6 8 168 680 3
cert_coverFacet 6 992
cert_cover_5 6 0 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0225

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_one_six_0226.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0226

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 651, 85, 681, 369, 225, 782, 326, 962, 348, 824, 992, 7, 11, 131, 21, 69, 41, 649, 49, 81, 97, 161, 193, 14, 70, 262, 522, 194, 322, 642, 770, 28, 268, 84, 324, 56, 280, 552, 776, 304, 336, 224, 352, 672, 800, 960]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_651, vertices_85, vertices_681, vertices_369, vertices_225, vertices_782, vertices_326, vertices_962, vertices_348, vertices_824, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_69, vertices_41, vertices_649, vertices_49, vertices_81, vertices_97, vertices_161, vertices_193, vertices_14, vertices_70, vertices_262, vertices_522, vertices_194, vertices_322, vertices_642, vertices_770, vertices_28, vertices_268, vertices_84, vertices_324, vertices_56, vertices_280, vertices_552, vertices_776, vertices_304, vertices_336, vertices_224, vertices_352, vertices_672, vertices_800, vertices_960] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_651), (false, vertices_85), (false, vertices_681), (false, vertices_369), (false, vertices_225), (true, vertices_262), (true, vertices_322), (true, vertices_770), (true, vertices_268), (true, vertices_324), (true, vertices_280), (true, vertices_776), (true, vertices_800), (true, vertices_960)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 14 17 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_199) then 11 else
  if p.val = (false, vertices_651) then 15 else
  if p.val = (false, vertices_85) then 0 else
  if p.val = (false, vertices_681) then 16 else
  if p.val = (false, vertices_369) then 18 else
  if p.val = (false, vertices_225) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_324) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_960) then 21 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_85), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_225), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
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
cert_row_4 2 1 2 3 5 7 348 28 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 6 0 1 2
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 14 782 3
cert_coverFacet 1 326
cert_cover_2 1 1 0 5 7 70 326 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 194 962 3
cert_coverFacet 3 348
cert_cover_5 3 2 1 2 3 5 28 348 3
cert_coverFacet 4 824
cert_cover_5 4 3 2 3 4 7 56 824 3
cert_coverFacet 5 992
cert_cover_5 5 0 4 5 6 7 224 992 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0226

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_one_six_0227.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0227

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 651, 85, 681, 241, 782, 326, 962, 348, 824, 368, 992, 7, 11, 131, 21, 69, 41, 649, 49, 81, 161, 193, 14, 70, 262, 522, 194, 322, 642, 770, 28, 268, 84, 324, 56, 280, 552, 776, 112, 304, 336, 224, 352, 672, 800, 960]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_651, vertices_85, vertices_681, vertices_241, vertices_782, vertices_326, vertices_962, vertices_348, vertices_824, vertices_368, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_69, vertices_41, vertices_649, vertices_49, vertices_81, vertices_161, vertices_193, vertices_14, vertices_70, vertices_262, vertices_522, vertices_194, vertices_322, vertices_642, vertices_770, vertices_28, vertices_268, vertices_84, vertices_324, vertices_56, vertices_280, vertices_552, vertices_776, vertices_112, vertices_304, vertices_336, vertices_224, vertices_352, vertices_672, vertices_800, vertices_960] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_651), (false, vertices_85), (false, vertices_681), (false, vertices_241), (true, vertices_262), (true, vertices_322), (true, vertices_770), (true, vertices_268), (true, vertices_324), (true, vertices_280), (true, vertices_776), (true, vertices_304), (true, vertices_336), (true, vertices_352), (true, vertices_800), (true, vertices_960)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 14 16 19 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_651) then 17 else
  if p.val = (false, vertices_85) then 0 else
  if p.val = (false, vertices_681) then 18 else
  if p.val = (false, vertices_241) then 20 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_352) then 10 else
  if p.val = (true, vertices_800) then 11 else
  if p.val = (true, vertices_960) then 23 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_85), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
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
cert_row_4 2 1 2 3 5 7 348 28 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 6 0 1 2
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 14 782 3
cert_coverFacet 1 326
cert_cover_2 1 1 0 5 7 70 326 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 194 962 3
cert_coverFacet 3 348
cert_cover_5 3 2 1 2 3 5 28 348 3
cert_coverFacet 4 824
cert_cover_5 4 3 2 3 4 7 56 824 3
cert_coverFacet 5 368
cert_cover_2 5 4 3 5 7 112 368 3
cert_coverFacet 6 992
cert_cover_5 6 0 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0227

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_one_six_0228.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0228

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 323, 653, 961, 342, 794, 172, 244, 632, 744, 848, 7, 11, 67, 259, 13, 133, 521, 193, 321, 641, 769, 22, 70, 26, 778, 274, 322, 44, 140, 52, 84, 164, 196, 56, 536, 616, 168, 648, 112, 336, 592, 784, 224, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_323, vertices_653, vertices_961, vertices_342, vertices_794, vertices_172, vertices_244, vertices_632, vertices_744, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_133, vertices_521, vertices_193, vertices_321, vertices_641, vertices_769, vertices_22, vertices_70, vertices_26, vertices_778, vertices_274, vertices_322, vertices_44, vertices_140, vertices_52, vertices_84, vertices_164, vertices_196, vertices_56, vertices_536, vertices_616, vertices_168, vertices_648, vertices_112, vertices_336, vertices_592, vertices_784, vertices_224, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_323), (false, vertices_653), (false, vertices_961), (true, vertices_274), (true, vertices_84), (true, vertices_164), (true, vertices_536), (true, vertices_616), (true, vertices_168), (true, vertices_112), (true, vertices_336), (true, vertices_592), (true, vertices_784), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_616) then 18 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_224) then 10 else
  0
cert_priority
cert_nodeAtPriority_55 323 274 84 164 536 168 112 336 592 784 224 199 779 653 616
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 4 5 6 244 52 3
cert_row_2 1 2 4 5 8 616
cert_row_2 2 0 2 7 8 778
cert_row_4 3 0 1 3 5 7 342 22 3
cert_rows
cert_pivot_2 6 4 2 0
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 3 0 1 3 5 22 342 3
cert_coverFacet 1 794
cert_cover_5 1 2 0 2 3 7 26 794 3
cert_coverFacet 2 172
cert_cover_2 2 2 1 4 6 44 172 3
cert_coverFacet 3 244
cert_cover_5 3 0 1 3 4 5 52 244 3
cert_coverFacet 4 632
cert_cover_5 4 1 2 3 4 5 56 632 3
cert_coverFacet 5 744
cert_cover_5 5 1 2 4 5 6 616 744 3
cert_coverFacet 6 848
cert_cover_2 6 5 3 7 8 336 848 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0228

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_one_six_0229.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0229

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 651, 341, 681, 241, 782, 326, 962, 796, 632, 848, 736, 7, 11, 131, 21, 69, 41, 649, 49, 81, 161, 193, 14, 70, 262, 522, 194, 322, 642, 770, 28, 780, 276, 324, 56, 536, 552, 112, 336, 592, 784, 224, 608, 672, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_651, vertices_341, vertices_681, vertices_241, vertices_782, vertices_326, vertices_962, vertices_796, vertices_632, vertices_848, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_69, vertices_41, vertices_649, vertices_49, vertices_81, vertices_161, vertices_193, vertices_14, vertices_70, vertices_262, vertices_522, vertices_194, vertices_322, vertices_642, vertices_770, vertices_28, vertices_780, vertices_276, vertices_324, vertices_56, vertices_536, vertices_552, vertices_112, vertices_336, vertices_592, vertices_784, vertices_224, vertices_608, vertices_672, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_651), (false, vertices_341), (false, vertices_681), (false, vertices_241), (true, vertices_262), (true, vertices_322), (true, vertices_770), (true, vertices_780), (true, vertices_536), (true, vertices_592), (true, vertices_784), (true, vertices_608), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 11 15 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_199) then 10 else
  if p.val = (false, vertices_651) then 16 else
  if p.val = (false, vertices_341) then 13 else
  if p.val = (false, vertices_681) then 17 else
  if p.val = (false, vertices_241) then 19 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_780) then 14 else
  if p.val = (true, vertices_536) then 3 else
  if p.val = (true, vertices_592) then 4 else
  if p.val = (true, vertices_784) then 5 else
  if p.val = (true, vertices_608) then 6 else
  if p.val = (true, vertices_704) then 7 else
  if p.val = (true, vertices_832) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_780), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 7 8 780
cert_row_4 1 0 5 6 7 8 962 194 3
cert_row_4 2 2 3 4 5 8 632 56 3
cert_rows_3
cert_pivot_3 0 1 2
cert_heightProof 3
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 326
cert_cover_2 1 1 0 5 7 70 326 3
cert_coverFacet 2 962
cert_cover_5 2 1 0 5 6 7 194 962 3
cert_coverFacet 3 796
cert_cover_5 3 0 1 2 3 7 28 796 3
cert_coverFacet 4 632
cert_cover_5 4 2 2 3 4 5 56 632 3
cert_coverFacet 5 848
cert_cover_2 5 5 3 7 8 336 848 3
cert_coverFacet 6 736
cert_cover_2 6 5 4 6 8 224 736 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0229

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_one_six_0230.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0230

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 397, 449, 86, 602, 428, 692, 724, 824, 840, 992, 7, 11, 67, 13, 133, 265, 193, 321, 385, 22, 70, 26, 74, 82, 44, 396, 52, 84, 660, 164, 196, 56, 536, 296, 328, 584, 776, 560, 592, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_397, vertices_449, vertices_86, vertices_602, vertices_428, vertices_692, vertices_724, vertices_824, vertices_840, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_74, vertices_82, vertices_44, vertices_396, vertices_52, vertices_84, vertices_660, vertices_164, vertices_196, vertices_56, vertices_536, vertices_296, vertices_328, vertices_584, vertices_776, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_397), (false, vertices_449), (true, vertices_82), (true, vertices_84), (true, vertices_660), (true, vertices_164), (true, vertices_536), (true, vertices_296), (true, vertices_584), (true, vertices_776), (true, vertices_560), (true, vertices_592), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 19 else
  if p.val = (false, vertices_199) then 16 else
  if p.val = (false, vertices_331) then 17 else
  if p.val = (false, vertices_397) then 20 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_660) then 21 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_416) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_800) then 12 else
  if p.val = (true, vertices_704) then 13 else
  if p.val = (true, vertices_832) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_660), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 8 602 26 3
cert_row_4 1 4 5 6 7 8 992 416 1
cert_row_4 2 2 3 4 7 8 824 56 3
cert_row_2 3 1 2 6 7 396
cert_row_2 4 1 3 6 8 660
cert_rows_2
cert_pivot 0 5 4 2 1
cert_heightProof 5
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 602
cert_cover_5 1 0 0 2 3 5 26 602 3
cert_coverFacet 2 428
cert_cover_5 2 3 1 2 4 6 44 428 3
cert_coverFacet 3 692
cert_cover_5 3 4 1 3 4 6 52 692 3
cert_coverFacet 4 724
cert_cover_5 4 4 1 3 5 6 84 724 3
cert_coverFacet 5 824
cert_cover_5 5 2 2 3 4 7 56 824 3
cert_coverFacet 6 840
cert_cover_2 6 5 2 7 8 328 840 3
cert_coverFacet 7 992
cert_cover_5 7 1 4 5 6 7 416 992 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 5 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0230

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_one_six_0231.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0231

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 597, 425, 689, 705, 334, 450, 604, 824, 840, 992, 7, 11, 131, 21, 69, 41, 393, 49, 529, 161, 193, 577, 641, 14, 70, 266, 194, 322, 386, 28, 76, 596, 56, 536, 296, 328, 584, 776, 560, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_597, vertices_425, vertices_689, vertices_705, vertices_334, vertices_450, vertices_604, vertices_824, vertices_840, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_69, vertices_41, vertices_393, vertices_49, vertices_529, vertices_161, vertices_193, vertices_577, vertices_641, vertices_14, vertices_70, vertices_266, vertices_194, vertices_322, vertices_386, vertices_28, vertices_76, vertices_596, vertices_56, vertices_536, vertices_296, vertices_328, vertices_584, vertices_776, vertices_560, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_597), (false, vertices_425), (false, vertices_689), (false, vertices_705), (true, vertices_322), (true, vertices_76), (true, vertices_536), (true, vertices_328), (true, vertices_584), (true, vertices_776), (true, vertices_800), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 15 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_199) then 11 else
  if p.val = (false, vertices_395) then 16 else
  if p.val = (false, vertices_597) then 14 else
  if p.val = (false, vertices_425) then 17 else
  if p.val = (false, vertices_689) then 19 else
  if p.val = (false, vertices_705) then 0 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_536) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_800) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_705), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
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
cert_row_4 0 0 1 2 5 7 334 14 3
cert_row_2 1 1 3 5 8 596
cert_row_4 2 2 3 4 7 8 824 56 3
cert_row_4 3 4 5 6 7 8 992 416 1
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 5 14 334 3
cert_coverFacet 1 450
cert_cover_2 1 5 0 6 7 194 450 3
cert_coverFacet 2 604
cert_cover_5 2 1 1 2 3 5 28 604 3
cert_coverFacet 3 824
cert_cover_5 3 2 2 3 4 7 56 824 3
cert_coverFacet 4 840
cert_cover_2 4 5 2 7 8 328 840 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 416 992 1
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0231

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_one_six_0232.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0232

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 397, 961, 86, 90, 172, 692, 724, 376, 936, 880, 7, 11, 67, 13, 133, 265, 193, 321, 385, 22, 70, 26, 74, 82, 44, 140, 52, 84, 660, 164, 196, 56, 88, 168, 296, 328, 392, 368, 560, 592, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_397, vertices_961, vertices_86, vertices_90, vertices_172, vertices_692, vertices_724, vertices_376, vertices_936, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_74, vertices_82, vertices_44, vertices_140, vertices_52, vertices_84, vertices_660, vertices_164, vertices_196, vertices_56, vertices_88, vertices_168, vertices_296, vertices_328, vertices_392, vertices_368, vertices_560, vertices_592, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_84), (true, vertices_660), (true, vertices_164), (true, vertices_88), (true, vertices_168), (true, vertices_296), (true, vertices_368), (true, vertices_560), (true, vertices_592), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 17 18 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 11 else
  if p.val = (false, vertices_331) then 12 else
  if p.val = (false, vertices_397) then 15 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_660) then 16 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_88) then 3 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_368) then 19 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_800) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_660), by decide +kernel⟩
  | 17 => Sum.inl 2
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
cert_row_2 0 1 3 6 8 660
cert_row_2 1 3 4 5 7 368
cert_row_4 2 2 4 6 7 8 936 168 3
cert_rows_3
cert_pivot_3 3 1 2
cert_heightProof 3
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 90
cert_cover_2 1 2 0 3 5 26 90 3
cert_coverFacet 2 172
cert_cover_2 2 2 1 4 6 44 172 3
cert_coverFacet 3 692
cert_cover_5 3 0 1 3 4 6 52 692 3
cert_coverFacet 4 724
cert_cover_5 4 0 1 3 5 6 84 724 3
cert_coverFacet 5 376
cert_cover_5 5 1 2 3 4 5 56 376 3
cert_coverFacet 6 936
cert_cover_5 6 2 2 4 6 7 168 936 3
cert_coverFacet 7 880
cert_cover_5 7 1 3 4 5 8 368 880 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0232

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_one_six_0233.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0233

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 397, 961, 86, 90, 172, 628, 740, 440, 856, 944, 7, 11, 67, 13, 133, 265, 193, 321, 385, 22, 70, 26, 74, 82, 44, 140, 52, 84, 612, 164, 196, 56, 88, 280, 168, 328, 392, 432, 560, 592, 784, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_397, vertices_961, vertices_86, vertices_90, vertices_172, vertices_628, vertices_740, vertices_440, vertices_856, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_74, vertices_82, vertices_44, vertices_140, vertices_52, vertices_84, vertices_612, vertices_164, vertices_196, vertices_56, vertices_88, vertices_280, vertices_168, vertices_328, vertices_392, vertices_432, vertices_560, vertices_592, vertices_784, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_84), (true, vertices_612), (true, vertices_164), (true, vertices_88), (true, vertices_280), (true, vertices_168), (true, vertices_432), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 17 18 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 11 else
  if p.val = (false, vertices_331) then 12 else
  if p.val = (false, vertices_397) then 15 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_612) then 16 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_88) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_432) then 19 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_672) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_612), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(true, vertices_432), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 5 8 612
cert_row_2 1 3 4 6 7 432
cert_row_4 2 2 3 5 7 8 856 88 3
cert_rows_3
cert_pivot_3 4 1 2
cert_heightProof 3
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 90
cert_cover_2 1 2 0 3 5 26 90 3
cert_coverFacet 2 172
cert_cover_2 2 2 1 4 6 44 172 3
cert_coverFacet 3 628
cert_cover_5 3 0 1 3 4 5 52 628 3
cert_coverFacet 4 740
cert_cover_5 4 0 1 4 5 6 612 740 3
cert_coverFacet 5 440
cert_cover_5 5 1 2 3 4 6 56 440 3
cert_coverFacet 6 856
cert_cover_5 6 2 2 3 5 7 88 856 3
cert_coverFacet 7 944
cert_cover_5 7 1 3 4 6 8 432 944 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0233

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_one_six_0234.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0234

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 397, 961, 86, 602, 428, 692, 724, 824, 840, 928, 7, 11, 67, 13, 133, 265, 193, 321, 385, 22, 70, 26, 74, 82, 44, 396, 52, 84, 660, 164, 196, 56, 536, 296, 328, 584, 776, 560, 592, 416, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_397, vertices_961, vertices_86, vertices_602, vertices_428, vertices_692, vertices_724, vertices_824, vertices_840, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_74, vertices_82, vertices_44, vertices_396, vertices_52, vertices_84, vertices_660, vertices_164, vertices_196, vertices_56, vertices_536, vertices_296, vertices_328, vertices_584, vertices_776, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_84), (true, vertices_660), (true, vertices_164), (true, vertices_536), (true, vertices_296), (true, vertices_584), (true, vertices_776), (true, vertices_560), (true, vertices_592), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 20 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_331) then 14 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_660) then 18 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_536) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
cert_priority
cert_nodeAtPriority_20 0 82 1 84 164 536 296 584 776 560 592 416 672 800 199 331 397 660
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 8 602 26 3
cert_row_4 1 2 3 4 7 8 824 56 3
cert_row_2 2 1 2 6 7 396
cert_row_2 3 1 3 6 8 660
cert_rows
cert_pivot_2 0 4 2 1
cert_heightProof 4
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 602
cert_cover_5 1 0 0 2 3 5 26 602 3
cert_coverFacet 2 428
cert_cover_5 2 2 1 2 4 6 44 428 3
cert_coverFacet 3 692
cert_cover_5 3 3 1 3 4 6 52 692 3
cert_coverFacet 4 724
cert_cover_5 4 3 1 3 5 6 84 724 3
cert_coverFacet 5 824
cert_cover_5 5 1 2 3 4 7 56 824 3
cert_coverFacet 6 840
cert_cover_2 6 5 2 7 8 328 840 3
cert_coverFacet 7 928
cert_cover_2 7 6 4 7 8 416 928 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0234

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_one_six_0235.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0235

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 397, 961, 86, 602, 428, 628, 740, 824, 840, 928, 7, 11, 67, 13, 133, 265, 193, 321, 385, 22, 70, 26, 74, 82, 44, 396, 52, 84, 612, 164, 196, 56, 536, 296, 328, 584, 776, 560, 592, 416, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_397, vertices_961, vertices_86, vertices_602, vertices_428, vertices_628, vertices_740, vertices_824, vertices_840, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_74, vertices_82, vertices_44, vertices_396, vertices_52, vertices_84, vertices_612, vertices_164, vertices_196, vertices_56, vertices_536, vertices_296, vertices_328, vertices_584, vertices_776, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_84), (true, vertices_612), (true, vertices_164), (true, vertices_536), (true, vertices_296), (true, vertices_584), (true, vertices_776), (true, vertices_560), (true, vertices_592), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 20 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_331) then 14 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_612) then 18 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_536) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
cert_priority
cert_nodeAtPriority_20 0 82 1 84 164 536 296 584 776 560 592 416 672 800 199 331 397 612
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 7 396
cert_row_2 1 1 4 5 8 612
cert_row_4 2 0 2 3 5 8 602 26 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 6 1 0 2
cert_heightProof 4
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 602
cert_cover_5 1 2 0 2 3 5 26 602 3
cert_coverFacet 2 428
cert_cover_5 2 0 1 2 4 6 44 428 3
cert_coverFacet 3 628
cert_cover_5 3 1 1 3 4 5 52 628 3
cert_coverFacet 4 740
cert_cover_5 4 1 1 4 5 6 612 740 3
cert_coverFacet 5 824
cert_cover_5 5 3 2 3 4 7 56 824 3
cert_coverFacet 6 840
cert_cover_2 6 5 2 7 8 328 840 3
cert_coverFacet 7 928
cert_cover_2 7 6 4 7 8 416 928 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0235

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_one_six_0236.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0236

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 397, 961, 86, 602, 428, 244, 824, 840, 752, 928, 7, 11, 67, 13, 133, 265, 193, 321, 385, 22, 70, 26, 74, 82, 44, 396, 52, 84, 164, 196, 56, 536, 296, 328, 584, 776, 240, 560, 592, 416, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_397, vertices_961, vertices_86, vertices_602, vertices_428, vertices_244, vertices_824, vertices_840, vertices_752, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_74, vertices_82, vertices_44, vertices_396, vertices_52, vertices_84, vertices_164, vertices_196, vertices_56, vertices_536, vertices_296, vertices_328, vertices_584, vertices_776, vertices_240, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_84), (true, vertices_164), (true, vertices_536), (true, vertices_296), (true, vertices_584), (true, vertices_776), (true, vertices_240), (true, vertices_560), (true, vertices_592), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 19 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_331) then 14 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_536) then 3 else
  if p.val = (true, vertices_296) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_240) then 20 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 7 396
cert_row_2 1 3 4 5 6 240
cert_row_4 2 0 2 3 5 8 602 26 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 602
cert_cover_5 1 2 0 2 3 5 26 602 3
cert_coverFacet 2 428
cert_cover_5 2 0 1 2 4 6 44 428 3
cert_coverFacet 3 244
cert_cover_5 3 1 1 3 4 5 52 244 3
cert_coverFacet 4 824
cert_cover_5 4 3 2 3 4 7 56 824 3
cert_coverFacet 5 840
cert_cover_2 5 5 2 7 8 328 840 3
cert_coverFacet 6 752
cert_cover_5 6 1 3 4 5 8 240 752 3
cert_coverFacet 7 928
cert_cover_2 7 6 4 7 8 416 928 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0236

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_one_six_0237.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0237

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 395, 597, 425, 689, 705, 334, 450, 284, 852, 824, 992, 7, 11, 131, 21, 69, 41, 393, 49, 529, 161, 193, 577, 641, 14, 70, 266, 194, 322, 386, 28, 268, 596, 276, 324, 56, 280, 296, 560, 784, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_395, vertices_597, vertices_425, vertices_689, vertices_705, vertices_334, vertices_450, vertices_284, vertices_852, vertices_824, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_69, vertices_41, vertices_393, vertices_49, vertices_529, vertices_161, vertices_193, vertices_577, vertices_641, vertices_14, vertices_70, vertices_266, vertices_194, vertices_322, vertices_386, vertices_28, vertices_268, vertices_596, vertices_276, vertices_324, vertices_56, vertices_280, vertices_296, vertices_560, vertices_784, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_395), (false, vertices_597), (false, vertices_425), (false, vertices_689), (false, vertices_705), (true, vertices_322), (true, vertices_268), (true, vertices_276), (true, vertices_324), (true, vertices_280), (true, vertices_784), (true, vertices_800), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 15 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_199) then 11 else
  if p.val = (false, vertices_395) then 16 else
  if p.val = (false, vertices_597) then 14 else
  if p.val = (false, vertices_425) then 17 else
  if p.val = (false, vertices_689) then 19 else
  if p.val = (false, vertices_705) then 0 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_324) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_784) then 6 else
  if p.val = (true, vertices_800) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_832) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_705), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
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
cert_row_4 0 0 1 2 5 7 334 14 3
cert_row_2 1 1 3 5 8 596
cert_row_4 2 2 3 4 7 8 824 56 3
cert_row_4 3 4 5 6 7 8 992 416 1
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 5 14 334 3
cert_coverFacet 1 450
cert_cover_2 1 5 0 6 7 194 450 3
cert_coverFacet 2 284
cert_cover_2 2 2 1 3 7 28 284 3
cert_coverFacet 3 852
cert_cover_5 3 1 1 3 5 7 596 852 3
cert_coverFacet 4 824
cert_cover_5 4 2 2 3 4 7 56 824 3
cert_coverFacet 5 992
cert_cover_5 5 3 4 5 6 7 416 992 1
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0237

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_one_six_0238.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0238

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 397, 449, 86, 282, 850, 428, 692, 724, 824, 992, 7, 11, 67, 13, 133, 265, 193, 321, 385, 22, 70, 26, 266, 82, 274, 322, 44, 396, 52, 84, 660, 164, 196, 56, 280, 296, 560, 592, 784, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_397, vertices_449, vertices_86, vertices_282, vertices_850, vertices_428, vertices_692, vertices_724, vertices_824, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_266, vertices_82, vertices_274, vertices_322, vertices_44, vertices_396, vertices_52, vertices_84, vertices_660, vertices_164, vertices_196, vertices_56, vertices_280, vertices_296, vertices_560, vertices_592, vertices_784, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_397), (false, vertices_449), (true, vertices_82), (true, vertices_274), (true, vertices_84), (true, vertices_660), (true, vertices_164), (true, vertices_280), (true, vertices_296), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 19 else
  if p.val = (false, vertices_199) then 16 else
  if p.val = (false, vertices_331) then 17 else
  if p.val = (false, vertices_397) then 20 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_660) then 21 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_416) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_800) then 12 else
  if p.val = (true, vertices_704) then 13 else
  if p.val = (true, vertices_832) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_660), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 7 8 850 82 3
cert_row_4 1 4 5 6 7 8 992 416 1
cert_row_4 2 2 3 4 7 8 824 56 3
cert_row_2 3 1 2 6 7 396
cert_row_2 4 1 3 6 8 660
cert_rows_2
cert_pivot 0 5 4 2 1
cert_heightProof 5
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 850
cert_cover_5 2 0 0 3 5 7 82 850 3
cert_coverFacet 3 428
cert_cover_5 3 3 1 2 4 6 44 428 3
cert_coverFacet 4 692
cert_cover_5 4 4 1 3 4 6 52 692 3
cert_coverFacet 5 724
cert_cover_5 5 4 1 3 5 6 84 724 3
cert_coverFacet 6 824
cert_cover_5 6 2 2 3 4 7 56 824 3
cert_coverFacet 7 992
cert_cover_5 7 1 4 5 6 7 416 992 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 5 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0238

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_one_six_0239.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0239

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 397, 449, 598, 794, 834, 428, 692, 708, 824, 992, 7, 11, 67, 13, 133, 265, 193, 321, 385, 22, 70, 26, 266, 530, 322, 578, 770, 44, 396, 52, 532, 164, 196, 580, 644, 56, 792, 296, 560, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_397, vertices_449, vertices_598, vertices_794, vertices_834, vertices_428, vertices_692, vertices_708, vertices_824, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_266, vertices_530, vertices_322, vertices_578, vertices_770, vertices_44, vertices_396, vertices_52, vertices_532, vertices_164, vertices_196, vertices_580, vertices_644, vertices_56, vertices_792, vertices_296, vertices_560, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_397), (false, vertices_449), (true, vertices_530), (true, vertices_578), (true, vertices_770), (true, vertices_532), (true, vertices_164), (true, vertices_580), (true, vertices_644), (true, vertices_792), (true, vertices_296), (true, vertices_560), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 19 else
  if p.val = (false, vertices_199) then 16 else
  if p.val = (false, vertices_331) then 17 else
  if p.val = (false, vertices_397) then 20 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_578) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_580) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_792) then 22 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_416) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_800) then 12 else
  if p.val = (true, vertices_704) then 13 else
  if p.val = (true, vertices_832) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(true, vertices_792), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 8 598 22 3
cert_row_4 1 4 5 6 7 8 992 416 1
cert_row_4 2 1 3 4 6 8 692 52 3
cert_row_2 3 1 2 6 7 396
cert_row_2 4 2 3 7 8 792
cert_rows_2
cert_pivot 0 5 4 1 2
cert_heightProof 5
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 22 598 3
cert_coverFacet 1 794
cert_cover_5 1 4 0 2 3 7 26 794 3
cert_coverFacet 2 834
cert_cover_2 2 5 0 7 8 322 834 3
cert_coverFacet 3 428
cert_cover_5 3 3 1 2 4 6 44 428 3
cert_coverFacet 4 692
cert_cover_5 4 2 1 3 4 6 52 692 3
cert_coverFacet 5 708
cert_cover_2 5 5 1 6 8 196 708 3
cert_coverFacet 6 824
cert_cover_5 6 4 2 3 4 7 56 824 3
cert_coverFacet 7 992
cert_cover_5 7 1 4 5 6 7 416 992 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 5 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0239

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_one_six_0240.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0240

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 397, 961, 86, 282, 850, 172, 244, 824, 936, 752, 7, 11, 67, 13, 133, 265, 193, 321, 385, 22, 70, 26, 266, 82, 274, 322, 44, 140, 52, 84, 164, 196, 56, 280, 168, 808, 392, 240, 560, 592, 784, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_397, vertices_961, vertices_86, vertices_282, vertices_850, vertices_172, vertices_244, vertices_824, vertices_936, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_266, vertices_82, vertices_274, vertices_322, vertices_44, vertices_140, vertices_52, vertices_84, vertices_164, vertices_196, vertices_56, vertices_280, vertices_168, vertices_808, vertices_392, vertices_240, vertices_560, vertices_592, vertices_784, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_274), (true, vertices_84), (true, vertices_164), (true, vertices_280), (true, vertices_168), (true, vertices_808), (true, vertices_240), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 18 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 11 else
  if p.val = (false, vertices_331) then 12 else
  if p.val = (false, vertices_397) then 15 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_808) then 17 else
  if p.val = (true, vertices_240) then 19 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_672) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(true, vertices_808), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 5 6 240
cert_row_2 1 2 4 7 8 808
cert_row_4 2 0 3 5 7 8 850 82 3
cert_rows_3
cert_pivot_3 2 6 0
cert_heightProof 3
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 850
cert_cover_5 2 2 0 3 5 7 82 850 3
cert_coverFacet 3 172
cert_cover_2 3 2 1 4 6 44 172 3
cert_coverFacet 4 244
cert_cover_5 4 0 1 3 4 5 52 244 3
cert_coverFacet 5 824
cert_cover_5 5 1 2 3 4 7 56 824 3
cert_coverFacet 6 936
cert_cover_5 6 1 2 4 6 7 168 936 3
cert_coverFacet 7 752
cert_cover_5 7 0 3 4 5 8 240 752 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0240

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_one_six_0241.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0241

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 397, 961, 86, 282, 850, 172, 692, 724, 824, 936, 7, 11, 67, 13, 133, 265, 193, 321, 385, 22, 70, 26, 266, 82, 274, 322, 44, 140, 52, 84, 660, 164, 196, 56, 280, 168, 808, 392, 560, 592, 784, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_397, vertices_961, vertices_86, vertices_282, vertices_850, vertices_172, vertices_692, vertices_724, vertices_824, vertices_936] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_266, vertices_82, vertices_274, vertices_322, vertices_44, vertices_140, vertices_52, vertices_84, vertices_660, vertices_164, vertices_196, vertices_56, vertices_280, vertices_168, vertices_808, vertices_392, vertices_560, vertices_592, vertices_784, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_274), (true, vertices_84), (true, vertices_660), (true, vertices_164), (true, vertices_280), (true, vertices_168), (true, vertices_808), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 17 19 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 11 else
  if p.val = (false, vertices_331) then 12 else
  if p.val = (false, vertices_397) then 15 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_660) then 16 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_808) then 18 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_672) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_660), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(true, vertices_808), by decide +kernel⟩
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
cert_row_2 0 2 4 7 8 808
cert_row_2 1 1 3 6 8 660
cert_row_4 2 0 3 5 7 8 850 82 3
cert_rows_3
cert_pivot_3 1 2 0
cert_heightProof 3
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 850
cert_cover_5 2 2 0 3 5 7 82 850 3
cert_coverFacet 3 172
cert_cover_2 3 2 1 4 6 44 172 3
cert_coverFacet 4 692
cert_cover_5 4 1 1 3 4 6 52 692 3
cert_coverFacet 5 724
cert_cover_5 5 1 1 3 5 6 84 724 3
cert_coverFacet 6 824
cert_cover_5 6 0 2 3 4 7 56 824 3
cert_coverFacet 7 936
cert_cover_5 7 0 2 4 6 7 168 936 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0241

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_one_six_0242.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0242

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 397, 961, 86, 282, 850, 172, 628, 740, 696, 920, 7, 11, 67, 13, 133, 265, 193, 321, 385, 22, 70, 26, 266, 82, 274, 322, 44, 140, 52, 84, 612, 164, 196, 56, 664, 280, 168, 392, 560, 592, 784, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_397, vertices_961, vertices_86, vertices_282, vertices_850, vertices_172, vertices_628, vertices_740, vertices_696, vertices_920] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_266, vertices_82, vertices_274, vertices_322, vertices_44, vertices_140, vertices_52, vertices_84, vertices_612, vertices_164, vertices_196, vertices_56, vertices_664, vertices_280, vertices_168, vertices_392, vertices_560, vertices_592, vertices_784, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_274), (true, vertices_84), (true, vertices_612), (true, vertices_164), (true, vertices_664), (true, vertices_280), (true, vertices_168), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 17 19 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 11 else
  if p.val = (false, vertices_331) then 12 else
  if p.val = (false, vertices_397) then 15 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_612) then 16 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_664) then 18 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_672) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_612), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(true, vertices_664), by decide +kernel⟩
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
cert_row_2 0 1 4 5 8 612
cert_row_2 1 2 3 6 8 664
cert_row_4 2 0 3 5 7 8 850 82 3
cert_rows_3
cert_pivot_3 2 1 0
cert_heightProof 3
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 850
cert_cover_5 2 2 0 3 5 7 82 850 3
cert_coverFacet 3 172
cert_cover_2 3 2 1 4 6 44 172 3
cert_coverFacet 4 628
cert_cover_5 4 0 1 3 4 5 52 628 3
cert_coverFacet 5 740
cert_cover_5 5 0 1 4 5 6 612 740 3
cert_coverFacet 6 696
cert_cover_5 6 1 2 3 4 6 56 696 3
cert_coverFacet 7 920
cert_cover_5 7 1 2 3 6 7 664 920 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0242

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_one_six_0243.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0243

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 397, 961, 86, 282, 850, 172, 628, 740, 824, 936, 7, 11, 67, 13, 133, 265, 193, 321, 385, 22, 70, 26, 266, 82, 274, 322, 44, 140, 52, 84, 612, 164, 196, 56, 280, 168, 808, 392, 560, 592, 784, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_397, vertices_961, vertices_86, vertices_282, vertices_850, vertices_172, vertices_628, vertices_740, vertices_824, vertices_936] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_266, vertices_82, vertices_274, vertices_322, vertices_44, vertices_140, vertices_52, vertices_84, vertices_612, vertices_164, vertices_196, vertices_56, vertices_280, vertices_168, vertices_808, vertices_392, vertices_560, vertices_592, vertices_784, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_274), (true, vertices_84), (true, vertices_612), (true, vertices_164), (true, vertices_280), (true, vertices_168), (true, vertices_808), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 17 19 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 11 else
  if p.val = (false, vertices_331) then 12 else
  if p.val = (false, vertices_397) then 15 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_612) then 16 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_808) then 18 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_672) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_612), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(true, vertices_808), by decide +kernel⟩
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
cert_row_2 0 1 4 5 8 612
cert_row_2 1 2 4 7 8 808
cert_row_4 2 0 3 5 7 8 850 82 3
cert_rows_3
cert_pivot_3 2 1 0
cert_heightProof 3
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 850
cert_cover_5 2 2 0 3 5 7 82 850 3
cert_coverFacet 3 172
cert_cover_2 3 2 1 4 6 44 172 3
cert_coverFacet 4 628
cert_cover_5 4 0 1 3 4 5 52 628 3
cert_coverFacet 5 740
cert_cover_5 5 0 1 4 5 6 612 740 3
cert_coverFacet 6 824
cert_cover_5 6 1 2 3 4 7 56 824 3
cert_coverFacet 7 936
cert_cover_5 7 1 2 4 6 7 168 936 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0243

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_one_six_0244.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0244

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 397, 961, 86, 282, 850, 172, 628, 740, 440, 944, 7, 11, 67, 13, 133, 265, 193, 321, 385, 22, 70, 26, 266, 82, 274, 322, 44, 140, 52, 84, 612, 164, 196, 56, 280, 168, 392, 432, 560, 592, 784, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_397, vertices_961, vertices_86, vertices_282, vertices_850, vertices_172, vertices_628, vertices_740, vertices_440, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_266, vertices_82, vertices_274, vertices_322, vertices_44, vertices_140, vertices_52, vertices_84, vertices_612, vertices_164, vertices_196, vertices_56, vertices_280, vertices_168, vertices_392, vertices_432, vertices_560, vertices_592, vertices_784, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_274), (true, vertices_84), (true, vertices_612), (true, vertices_164), (true, vertices_280), (true, vertices_168), (true, vertices_432), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 17 18 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 11 else
  if p.val = (false, vertices_331) then 12 else
  if p.val = (false, vertices_397) then 15 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_612) then 16 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_432) then 19 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_672) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_612), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(true, vertices_432), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 5 8 612
cert_row_2 1 3 4 6 7 432
cert_row_4 2 0 3 5 7 8 850 82 3
cert_rows_3
cert_pivot_3 4 1 0
cert_heightProof 3
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 850
cert_cover_5 2 2 0 3 5 7 82 850 3
cert_coverFacet 3 172
cert_cover_2 3 2 1 4 6 44 172 3
cert_coverFacet 4 628
cert_cover_5 4 0 1 3 4 5 52 628 3
cert_coverFacet 5 740
cert_cover_5 5 0 1 4 5 6 612 740 3
cert_coverFacet 6 440
cert_cover_5 6 1 2 3 4 6 56 440 3
cert_coverFacet 7 944
cert_cover_5 7 1 3 4 6 8 432 944 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0244

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_one_six_0245.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0245

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 397, 961, 86, 794, 850, 172, 628, 740, 696, 904, 7, 11, 67, 13, 133, 265, 193, 321, 385, 22, 70, 26, 266, 82, 786, 322, 44, 140, 52, 84, 612, 164, 196, 56, 536, 168, 392, 648, 776, 560, 592, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_397, vertices_961, vertices_86, vertices_794, vertices_850, vertices_172, vertices_628, vertices_740, vertices_696, vertices_904] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_266, vertices_82, vertices_786, vertices_322, vertices_44, vertices_140, vertices_52, vertices_84, vertices_612, vertices_164, vertices_196, vertices_56, vertices_536, vertices_168, vertices_392, vertices_648, vertices_776, vertices_560, vertices_592, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_786), (true, vertices_84), (true, vertices_612), (true, vertices_164), (true, vertices_536), (true, vertices_168), (true, vertices_648), (true, vertices_776), (true, vertices_560), (true, vertices_592), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 10 19 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 15 else
  if p.val = (false, vertices_331) then 11 else
  if p.val = (false, vertices_397) then 12 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_786) then 16 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_612) then 18 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_536) then 3 else
  if p.val = (true, vertices_168) then 4 else
  if p.val = (true, vertices_648) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_672) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inl 2
  | 11 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_786), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(true, vertices_612), by decide +kernel⟩
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
cert_row_2 0 0 3 7 8 786
cert_row_2 1 1 4 5 8 612
cert_row_4 2 2 3 4 6 8 696 56 3
cert_rows_3
cert_pivot_3 1 0 2
cert_heightProof 3
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 794
cert_cover_5 1 0 0 2 3 7 26 794 3
cert_coverFacet 2 850
cert_cover_5 2 0 0 3 5 7 82 850 3
cert_coverFacet 3 172
cert_cover_2 3 2 1 4 6 44 172 3
cert_coverFacet 4 628
cert_cover_5 4 1 1 3 4 5 52 628 3
cert_coverFacet 5 740
cert_cover_5 5 1 1 4 5 6 612 740 3
cert_coverFacet 6 696
cert_cover_5 6 2 2 3 4 6 56 696 3
cert_coverFacet 7 904
cert_cover_2 7 6 2 7 8 392 904 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0245

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_one_six_0246.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0246

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 397, 961, 598, 282, 850, 172, 692, 708, 824, 936, 7, 11, 67, 13, 133, 265, 193, 321, 385, 22, 70, 26, 266, 594, 274, 322, 44, 140, 52, 532, 164, 196, 580, 644, 56, 280, 168, 808, 392, 560, 784, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_397, vertices_961, vertices_598, vertices_282, vertices_850, vertices_172, vertices_692, vertices_708, vertices_824, vertices_936] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_266, vertices_594, vertices_274, vertices_322, vertices_44, vertices_140, vertices_52, vertices_532, vertices_164, vertices_196, vertices_580, vertices_644, vertices_56, vertices_280, vertices_168, vertices_808, vertices_392, vertices_560, vertices_784, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_397), (false, vertices_961), (true, vertices_594), (true, vertices_274), (true, vertices_532), (true, vertices_164), (true, vertices_580), (true, vertices_644), (true, vertices_280), (true, vertices_168), (true, vertices_808), (true, vertices_560), (true, vertices_784), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 10 17 19 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 11 else
  if p.val = (false, vertices_331) then 15 else
  if p.val = (false, vertices_397) then 12 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_594) then 16 else
  if p.val = (true, vertices_274) then 0 else
  if p.val = (true, vertices_532) then 1 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_580) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_808) then 18 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_672) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inl 1
  | 11 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_594), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(true, vertices_808), by decide +kernel⟩
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
cert_row_2 0 2 4 7 8 808
cert_row_2 1 0 3 5 8 594
cert_row_4 2 1 3 4 6 8 692 52 3
cert_rows_3
cert_pivot_3 0 2 1
cert_heightProof 3
cert_coverFacet 0 598
cert_cover_5 0 1 0 1 3 5 22 598 3
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 850
cert_cover_5 2 1 0 3 5 7 594 850 3
cert_coverFacet 3 172
cert_cover_2 3 2 1 4 6 44 172 3
cert_coverFacet 4 692
cert_cover_5 4 2 1 3 4 6 52 692 3
cert_coverFacet 5 708
cert_cover_2 5 5 1 6 8 196 708 3
cert_coverFacet 6 824
cert_cover_5 6 0 2 3 4 7 56 824 3
cert_coverFacet 7 936
cert_cover_5 7 0 2 4 6 7 168 936 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0246

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_one_six_0247.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0247

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 397, 961, 86, 282, 850, 428, 692, 724, 824, 928, 7, 11, 67, 13, 133, 265, 193, 321, 385, 22, 70, 26, 266, 82, 274, 322, 44, 396, 52, 84, 660, 164, 196, 56, 280, 296, 560, 592, 784, 416, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_397, vertices_961, vertices_86, vertices_282, vertices_850, vertices_428, vertices_692, vertices_724, vertices_824, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_266, vertices_82, vertices_274, vertices_322, vertices_44, vertices_396, vertices_52, vertices_84, vertices_660, vertices_164, vertices_196, vertices_56, vertices_280, vertices_296, vertices_560, vertices_592, vertices_784, vertices_416, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_274), (true, vertices_84), (true, vertices_660), (true, vertices_164), (true, vertices_280), (true, vertices_296), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 20 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_331) then 14 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_660) then 18 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
cert_priority
cert_nodeAtPriority_20 0 82 1 274 84 164 280 296 560 592 784 416 672 800 199 331 397 660
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 7 8 850 82 3
cert_row_4 1 2 3 4 7 8 824 56 3
cert_row_2 2 1 2 6 7 396
cert_row_2 3 1 3 6 8 660
cert_rows
cert_pivot_2 0 4 2 1
cert_heightProof 4
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 850
cert_cover_5 2 0 0 3 5 7 82 850 3
cert_coverFacet 3 428
cert_cover_5 3 2 1 2 4 6 44 428 3
cert_coverFacet 4 692
cert_cover_5 4 3 1 3 4 6 52 692 3
cert_coverFacet 5 724
cert_cover_5 5 3 1 3 5 6 84 724 3
cert_coverFacet 6 824
cert_cover_5 6 1 2 3 4 7 56 824 3
cert_coverFacet 7 928
cert_cover_2 7 6 4 7 8 416 928 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0247

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_one_six_0248.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0248

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 397, 961, 86, 282, 850, 428, 628, 740, 824, 928, 7, 11, 67, 13, 133, 265, 193, 321, 385, 22, 70, 26, 266, 82, 274, 322, 44, 396, 52, 84, 612, 164, 196, 56, 280, 296, 560, 592, 784, 416, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_397, vertices_961, vertices_86, vertices_282, vertices_850, vertices_428, vertices_628, vertices_740, vertices_824, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_266, vertices_82, vertices_274, vertices_322, vertices_44, vertices_396, vertices_52, vertices_84, vertices_612, vertices_164, vertices_196, vertices_56, vertices_280, vertices_296, vertices_560, vertices_592, vertices_784, vertices_416, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_274), (true, vertices_84), (true, vertices_612), (true, vertices_164), (true, vertices_280), (true, vertices_296), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 20 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_331) then 14 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_612) then 18 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
cert_priority
cert_nodeAtPriority_20 0 82 1 274 84 164 280 296 560 592 784 416 672 800 199 331 397 612
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 7 396
cert_row_2 1 1 4 5 8 612
cert_row_4 2 0 3 5 7 8 850 82 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 6 1 0 2
cert_heightProof 4
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 850
cert_cover_5 2 2 0 3 5 7 82 850 3
cert_coverFacet 3 428
cert_cover_5 3 0 1 2 4 6 44 428 3
cert_coverFacet 4 628
cert_cover_5 4 1 1 3 4 5 52 628 3
cert_coverFacet 5 740
cert_cover_5 5 1 1 4 5 6 612 740 3
cert_coverFacet 6 824
cert_cover_5 6 3 2 3 4 7 56 824 3
cert_coverFacet 7 928
cert_cover_2 7 6 4 7 8 416 928 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0248

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_one_six_0249.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0249

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 397, 961, 86, 282, 850, 428, 244, 824, 752, 928, 7, 11, 67, 13, 133, 265, 193, 321, 385, 22, 70, 26, 266, 82, 274, 322, 44, 396, 52, 84, 164, 196, 56, 280, 296, 240, 560, 592, 784, 416, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_397, vertices_961, vertices_86, vertices_282, vertices_850, vertices_428, vertices_244, vertices_824, vertices_752, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_266, vertices_82, vertices_274, vertices_322, vertices_44, vertices_396, vertices_52, vertices_84, vertices_164, vertices_196, vertices_56, vertices_280, vertices_296, vertices_240, vertices_560, vertices_592, vertices_784, vertices_416, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_274), (true, vertices_84), (true, vertices_164), (true, vertices_280), (true, vertices_296), (true, vertices_240), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 19 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_331) then 14 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_240) then 20 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_592) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 7 396
cert_row_2 1 3 4 5 6 240
cert_row_4 2 0 3 5 7 8 850 82 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 850
cert_cover_5 2 2 0 3 5 7 82 850 3
cert_coverFacet 3 428
cert_cover_5 3 0 1 2 4 6 44 428 3
cert_coverFacet 4 244
cert_cover_5 4 1 1 3 4 5 52 244 3
cert_coverFacet 5 824
cert_cover_5 5 3 2 3 4 7 56 824 3
cert_coverFacet 6 752
cert_cover_5 6 1 3 4 5 8 240 752 3
cert_coverFacet 7 928
cert_cover_2 7 6 4 7 8 416 928 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0249

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_0840 : Certifies 840 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0220.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0841 : Certifies 841 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0221.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0842 : Certifies 842 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0222.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0843 : Certifies 843 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0223.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0844 : Certifies 844 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0224.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0845 : Certifies 845 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0225.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0846 : Certifies 846 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0226.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0847 : Certifies 847 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0227.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0848 : Certifies 848 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0228.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0849 : Certifies 849 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0229.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0850 : Certifies 850 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0230.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0851 : Certifies 851 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0231.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0852 : Certifies 852 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0232.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0853 : Certifies 853 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0233.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0854 : Certifies 854 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0234.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0855 : Certifies 855 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0235.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0856 : Certifies 856 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0236.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0857 : Certifies 857 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0237.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0858 : Certifies 858 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0238.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0859 : Certifies 859 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0239.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0860 : Certifies 860 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0240.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0861 : Certifies 861 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0241.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0862 : Certifies 862 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0242.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0863 : Certifies 863 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0243.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0864 : Certifies 864 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0244.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0865 : Certifies 865 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0245.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0866 : Certifies 866 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0246.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0867 : Certifies 867 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0247.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0868 : Certifies 868 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0248.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0869 : Certifies 869 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0249.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B028 (j : Fin 30) :
    Certifies (840 + j.val) := by
  fin_cases j
  · exact projection_0840
  · exact projection_0841
  · exact projection_0842
  · exact projection_0843
  · exact projection_0844
  · exact projection_0845
  · exact projection_0846
  · exact projection_0847
  · exact projection_0848
  · exact projection_0849
  · exact projection_0850
  · exact projection_0851
  · exact projection_0852
  · exact projection_0853
  · exact projection_0854
  · exact projection_0855
  · exact projection_0856
  · exact projection_0857
  · exact projection_0858
  · exact projection_0859
  · exact projection_0860
  · exact projection_0861
  · exact projection_0862
  · exact projection_0863
  · exact projection_0864
  · exact projection_0865
  · exact projection_0866
  · exact projection_0867
  · exact projection_0868
  · exact projection_0869

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
