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
/- Source: ProjectionCertificates/R_one_six_0530.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0530

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 323, 653, 449, 897, 342, 282, 684, 244, 632, 856, 992, 7, 11, 67, 259, 13, 133, 521, 193, 321, 385, 641, 769, 22, 70, 26, 266, 274, 322, 44, 652, 52, 84, 164, 196, 56, 600, 280, 552, 776, 112, 336, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_323, vertices_653, vertices_449, vertices_897, vertices_342, vertices_282, vertices_684, vertices_244, vertices_632, vertices_856, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_133, vertices_521, vertices_193, vertices_321, vertices_385, vertices_641, vertices_769, vertices_22, vertices_70, vertices_26, vertices_266, vertices_274, vertices_322, vertices_44, vertices_652, vertices_52, vertices_84, vertices_164, vertices_196, vertices_56, vertices_600, vertices_280, vertices_552, vertices_776, vertices_112, vertices_336, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_323), (false, vertices_653), (false, vertices_449), (false, vertices_897), (true, vertices_274), (true, vertices_84), (true, vertices_164), (true, vertices_600), (true, vertices_280), (true, vertices_552), (true, vertices_112), (true, vertices_336), (true, vertices_224), (true, vertices_608), (true, vertices_672), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_199) then 15 else
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_653) then 19 else
  if p.val = (false, vertices_449) then 1 else
  if p.val = (false, vertices_897) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_600) then 21 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_608) then 11 else
  if p.val = (true, vertices_672) then 12 else
  if p.val = (true, vertices_832) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 2 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(true, vertices_600), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 7 342 22 3
cert_row_4 1 4 5 6 7 8 992 224 3
cert_row_4 2 1 3 4 5 6 244 52 3
cert_row_2 3 2 3 5 8 600
cert_row_2 4 1 2 6 8 652
cert_rows_2
cert_pivot 0 7 4 3 1
cert_heightProof 5
cert_coverFacet 0 342
cert_cover_5 0 0 0 1 3 5 22 342 3
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 684
cert_cover_5 2 4 1 2 4 6 44 684 3
cert_coverFacet 3 244
cert_cover_5 3 2 1 3 4 5 52 244 3
cert_coverFacet 4 632
cert_cover_5 4 3 2 3 4 5 56 632 3
cert_coverFacet 5 856
cert_cover_5 5 3 2 3 5 7 600 856 3
cert_coverFacet 6 992
cert_cover_5 6 1 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 5 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0530

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_one_six_0531.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0531

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 323, 653, 961, 86, 346, 172, 372, 484, 696, 792, 944, 7, 11, 67, 259, 13, 133, 521, 193, 321, 641, 769, 22, 70, 26, 266, 82, 322, 44, 140, 52, 84, 356, 164, 196, 56, 280, 536, 168, 648, 776, 688, 304, 336, 784, 416, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_323, vertices_653, vertices_961, vertices_86, vertices_346, vertices_172, vertices_372, vertices_484, vertices_696, vertices_792, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_133, vertices_521, vertices_193, vertices_321, vertices_641, vertices_769, vertices_22, vertices_70, vertices_26, vertices_266, vertices_82, vertices_322, vertices_44, vertices_140, vertices_52, vertices_84, vertices_356, vertices_164, vertices_196, vertices_56, vertices_280, vertices_536, vertices_168, vertices_648, vertices_776, vertices_688, vertices_304, vertices_336, vertices_784, vertices_416, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_323), (false, vertices_653), (false, vertices_961), (true, vertices_82), (true, vertices_84), (true, vertices_356), (true, vertices_164), (true, vertices_280), (true, vertices_536), (true, vertices_168), (true, vertices_688), (true, vertices_304), (true, vertices_336), (true, vertices_784), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 18 19 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_356) then 17 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_688) then 20 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_416) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_356), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(true, vertices_688), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 5 7 356
cert_row_2 1 3 4 6 8 688
cert_row_4 2 0 2 3 5 7 346 26 3
cert_rows_3
cert_pivot_3 4 1 0
cert_heightProof 3
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 346
cert_cover_5 1 2 0 2 3 5 26 346 3
cert_coverFacet 2 172
cert_cover_2 2 2 1 4 6 44 172 3
cert_coverFacet 3 372
cert_cover_5 3 0 1 3 4 5 52 372 3
cert_coverFacet 4 484
cert_cover_5 4 0 1 4 5 6 356 484 3
cert_coverFacet 5 696
cert_cover_5 5 1 2 3 4 6 56 696 3
cert_coverFacet 6 792
cert_cover_2 6 3 2 7 8 280 792 3
cert_coverFacet 7 944
cert_cover_5 7 1 3 4 6 7 688 944 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0531

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_one_six_0532.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0532

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 323, 653, 961, 342, 282, 236, 372, 696, 792, 944, 480, 7, 11, 67, 259, 13, 133, 521, 193, 321, 641, 769, 22, 70, 26, 266, 274, 322, 44, 140, 52, 340, 100, 196, 56, 280, 536, 168, 648, 776, 688, 304, 784, 224, 352, 416, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_323, vertices_653, vertices_961, vertices_342, vertices_282, vertices_236, vertices_372, vertices_696, vertices_792, vertices_944, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_133, vertices_521, vertices_193, vertices_321, vertices_641, vertices_769, vertices_22, vertices_70, vertices_26, vertices_266, vertices_274, vertices_322, vertices_44, vertices_140, vertices_52, vertices_340, vertices_100, vertices_196, vertices_56, vertices_280, vertices_536, vertices_168, vertices_648, vertices_776, vertices_688, vertices_304, vertices_784, vertices_224, vertices_352, vertices_416, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_323), (false, vertices_653), (false, vertices_961), (true, vertices_274), (true, vertices_340), (true, vertices_100), (true, vertices_280), (true, vertices_536), (true, vertices_168), (true, vertices_688), (true, vertices_304), (true, vertices_784), (true, vertices_224), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 18 19 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_340) then 17 else
  if p.val = (true, vertices_100) then 2 else
  if p.val = (true, vertices_280) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_688) then 20 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_352) then 9 else
  if p.val = (true, vertices_416) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_340), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(true, vertices_688), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 5 7 340
cert_row_2 1 3 4 6 8 688
cert_row_4 2 1 2 4 5 6 236 44 3
cert_rows_3
cert_pivot_3 3 7 1
cert_heightProof 3
cert_coverFacet 0 342
cert_cover_5 0 0 0 1 3 5 22 342 3
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 236
cert_cover_5 2 2 1 2 4 5 44 236 3
cert_coverFacet 3 372
cert_cover_5 3 0 1 3 4 5 52 372 3
cert_coverFacet 4 696
cert_cover_5 4 1 2 3 4 6 56 696 3
cert_coverFacet 5 792
cert_cover_2 5 3 2 7 8 280 792 3
cert_coverFacet 6 944
cert_cover_5 6 1 3 4 6 7 688 944 3
cert_coverFacet 7 480
cert_cover_2 7 5 4 6 7 224 480 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0532

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_one_six_0533.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0533

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 651, 341, 233, 369, 782, 326, 962, 284, 696, 792, 816, 992, 7, 11, 131, 21, 69, 41, 137, 49, 337, 97, 193, 14, 70, 262, 522, 194, 322, 642, 770, 28, 268, 276, 324, 56, 280, 536, 168, 648, 776, 304, 560, 784, 224, 352, 672, 800, 960]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_651, vertices_341, vertices_233, vertices_369, vertices_782, vertices_326, vertices_962, vertices_284, vertices_696, vertices_792, vertices_816, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_69, vertices_41, vertices_137, vertices_49, vertices_337, vertices_97, vertices_193, vertices_14, vertices_70, vertices_262, vertices_522, vertices_194, vertices_322, vertices_642, vertices_770, vertices_28, vertices_268, vertices_276, vertices_324, vertices_56, vertices_280, vertices_536, vertices_168, vertices_648, vertices_776, vertices_304, vertices_560, vertices_784, vertices_224, vertices_352, vertices_672, vertices_800, vertices_960] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_651), (false, vertices_341), (false, vertices_233), (false, vertices_369), (true, vertices_262), (true, vertices_322), (true, vertices_770), (true, vertices_268), (true, vertices_280), (true, vertices_536), (true, vertices_776), (true, vertices_560), (true, vertices_784), (true, vertices_672), (true, vertices_800), (true, vertices_960)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 16 18 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_651) then 13 else
  if p.val = (false, vertices_341) then 19 else
  if p.val = (false, vertices_233) then 17 else
  if p.val = (false, vertices_369) then 20 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_960) then 23 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
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
cert_row_4 2 2 3 4 6 8 696 56 3
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
cert_coverFacet 4 696
cert_cover_5 4 2 2 3 4 6 56 696 3
cert_coverFacet 5 792
cert_cover_2 5 3 2 7 8 280 792 3
cert_coverFacet 6 816
cert_cover_2 6 4 3 7 8 304 816 3
cert_coverFacet 7 992
cert_cover_5 7 0 4 5 6 7 224 992 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0533

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_one_six_0534.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0534

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 323, 653, 961, 342, 538, 786, 236, 372, 696, 944, 480, 7, 11, 67, 259, 13, 133, 521, 193, 321, 641, 769, 22, 70, 26, 522, 274, 530, 322, 770, 44, 140, 52, 340, 100, 196, 56, 536, 168, 648, 688, 304, 784, 224, 352, 416, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_323, vertices_653, vertices_961, vertices_342, vertices_538, vertices_786, vertices_236, vertices_372, vertices_696, vertices_944, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_133, vertices_521, vertices_193, vertices_321, vertices_641, vertices_769, vertices_22, vertices_70, vertices_26, vertices_522, vertices_274, vertices_530, vertices_322, vertices_770, vertices_44, vertices_140, vertices_52, vertices_340, vertices_100, vertices_196, vertices_56, vertices_536, vertices_168, vertices_648, vertices_688, vertices_304, vertices_784, vertices_224, vertices_352, vertices_416, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_323), (false, vertices_653), (false, vertices_961), (true, vertices_274), (true, vertices_530), (true, vertices_340), (true, vertices_100), (true, vertices_536), (true, vertices_168), (true, vertices_688), (true, vertices_304), (true, vertices_784), (true, vertices_224), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 18 19 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_779) then 13 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_340) then 17 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_688) then 20 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_352) then 9 else
  if p.val = (true, vertices_416) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_340), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(true, vertices_688), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 5 7 340
cert_row_2 1 3 4 6 8 688
cert_row_4 2 1 2 4 5 6 236 44 3
cert_rows_3
cert_pivot_3 3 7 1
cert_heightProof 3
cert_coverFacet 0 342
cert_cover_5 0 0 0 1 3 5 22 342 3
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 786
cert_cover_2 2 3 0 7 8 274 786 3
cert_coverFacet 3 236
cert_cover_5 3 2 1 2 4 5 44 236 3
cert_coverFacet 4 372
cert_cover_5 4 0 1 3 4 5 52 372 3
cert_coverFacet 5 696
cert_cover_5 5 1 2 3 4 6 56 696 3
cert_coverFacet 6 944
cert_cover_5 6 1 3 4 6 7 688 944 3
cert_coverFacet 7 480
cert_cover_2 7 5 4 6 7 224 480 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0534

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_one_six_0535.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0535

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 651, 341, 233, 369, 782, 326, 962, 540, 788, 696, 816, 992, 7, 11, 131, 21, 69, 41, 137, 49, 337, 97, 193, 14, 70, 262, 522, 194, 322, 642, 770, 28, 524, 276, 532, 324, 772, 56, 536, 168, 648, 304, 560, 784, 224, 352, 672, 800, 960]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_651, vertices_341, vertices_233, vertices_369, vertices_782, vertices_326, vertices_962, vertices_540, vertices_788, vertices_696, vertices_816, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_69, vertices_41, vertices_137, vertices_49, vertices_337, vertices_97, vertices_193, vertices_14, vertices_70, vertices_262, vertices_522, vertices_194, vertices_322, vertices_642, vertices_770, vertices_28, vertices_524, vertices_276, vertices_532, vertices_324, vertices_772, vertices_56, vertices_536, vertices_168, vertices_648, vertices_304, vertices_560, vertices_784, vertices_224, vertices_352, vertices_672, vertices_800, vertices_960] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_651), (false, vertices_341), (false, vertices_233), (false, vertices_369), (true, vertices_262), (true, vertices_322), (true, vertices_770), (true, vertices_524), (true, vertices_532), (true, vertices_772), (true, vertices_536), (true, vertices_560), (true, vertices_784), (true, vertices_672), (true, vertices_800), (true, vertices_960)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 16 18 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_651) then 13 else
  if p.val = (false, vertices_341) then 19 else
  if p.val = (false, vertices_233) then 17 else
  if p.val = (false, vertices_369) then 20 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_960) then 23 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
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
cert_row_4 2 2 3 4 6 8 696 56 3
cert_rows_3
cert_pivot_3 0 5 2
cert_heightProof 3
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 14 782 3
cert_coverFacet 1 326
cert_cover_2 1 1 0 5 7 70 326 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 194 962 3
cert_coverFacet 3 540
cert_cover_2 3 2 1 3 8 28 540 3
cert_coverFacet 4 788
cert_cover_2 4 3 1 7 8 276 788 3
cert_coverFacet 5 696
cert_cover_5 5 2 2 3 4 6 56 696 3
cert_coverFacet 6 816
cert_cover_2 6 4 3 7 8 304 816 3
cert_coverFacet 7 992
cert_cover_5 7 0 4 5 6 7 224 992 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0535

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_one_six_0536.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0536

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 651, 341, 233, 369, 782, 326, 450, 898, 796, 696, 816, 992, 7, 11, 131, 21, 69, 41, 137, 49, 337, 97, 193, 14, 70, 262, 522, 194, 322, 386, 642, 770, 28, 780, 276, 324, 56, 536, 168, 648, 304, 560, 784, 224, 352, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_651, vertices_341, vertices_233, vertices_369, vertices_782, vertices_326, vertices_450, vertices_898, vertices_796, vertices_696, vertices_816, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_69, vertices_41, vertices_137, vertices_49, vertices_337, vertices_97, vertices_193, vertices_14, vertices_70, vertices_262, vertices_522, vertices_194, vertices_322, vertices_386, vertices_642, vertices_770, vertices_28, vertices_780, vertices_276, vertices_324, vertices_56, vertices_536, vertices_168, vertices_648, vertices_304, vertices_560, vertices_784, vertices_224, vertices_352, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_651), (false, vertices_341), (false, vertices_233), (false, vertices_369), (true, vertices_262), (true, vertices_322), (true, vertices_386), (true, vertices_770), (true, vertices_780), (true, vertices_536), (true, vertices_560), (true, vertices_784), (true, vertices_672), (true, vertices_800), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_651) then 13 else
  if p.val = (false, vertices_341) then 20 else
  if p.val = (false, vertices_233) then 18 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_780) then 16 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_784) then 6 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_780), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 7 8 780
cert_row_4 1 2 3 4 6 8 696 56 3
cert_row_4 2 4 5 6 7 8 992 224 3
cert_rows_3
cert_pivot_3 2 1 4
cert_heightProof 3
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 326
cert_cover_2 1 1 0 5 7 70 326 3
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
cert_coverFacet 3 898
cert_cover_2 3 6 0 7 8 386 898 3
cert_coverFacet 4 796
cert_cover_5 4 0 1 2 3 7 28 796 3
cert_coverFacet 5 696
cert_cover_5 5 1 2 3 4 6 56 696 3
cert_coverFacet 6 816
cert_cover_2 6 4 3 7 8 304 816 3
cert_coverFacet 7 992
cert_cover_5 7 2 4 5 6 7 224 992 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0536

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_one_six_0537.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0537

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 651, 341, 681, 241, 782, 326, 450, 898, 796, 632, 848, 992, 7, 11, 131, 21, 69, 41, 649, 49, 81, 161, 193, 14, 70, 262, 522, 194, 322, 386, 642, 770, 28, 780, 276, 324, 56, 536, 552, 112, 336, 592, 784, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_651, vertices_341, vertices_681, vertices_241, vertices_782, vertices_326, vertices_450, vertices_898, vertices_796, vertices_632, vertices_848, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_69, vertices_41, vertices_649, vertices_49, vertices_81, vertices_161, vertices_193, vertices_14, vertices_70, vertices_262, vertices_522, vertices_194, vertices_322, vertices_386, vertices_642, vertices_770, vertices_28, vertices_780, vertices_276, vertices_324, vertices_56, vertices_536, vertices_552, vertices_112, vertices_336, vertices_592, vertices_784, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_651), (false, vertices_341), (false, vertices_681), (false, vertices_241), (true, vertices_262), (true, vertices_322), (true, vertices_386), (true, vertices_770), (true, vertices_780), (true, vertices_536), (true, vertices_592), (true, vertices_784), (true, vertices_608), (true, vertices_448), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 17 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_651) then 18 else
  if p.val = (false, vertices_341) then 15 else
  if p.val = (false, vertices_681) then 19 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_780) then 16 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_592) then 5 else
  if p.val = (true, vertices_784) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_832) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_780), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
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
cert_row_2 0 1 2 7 8 780
cert_row_4 1 2 3 4 5 8 632 56 3
cert_row_4 2 4 5 6 7 8 992 224 3
cert_rows_3
cert_pivot_3 2 1 4
cert_heightProof 3
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 326
cert_cover_2 1 1 0 5 7 70 326 3
cert_coverFacet 2 450
cert_cover_2 2 5 0 6 7 194 450 3
cert_coverFacet 3 898
cert_cover_2 3 6 0 7 8 386 898 3
cert_coverFacet 4 796
cert_cover_5 4 0 1 2 3 7 28 796 3
cert_coverFacet 5 632
cert_cover_5 5 1 2 3 4 5 56 632 3
cert_coverFacet 6 848
cert_cover_2 6 5 3 7 8 336 848 3
cert_coverFacet 7 992
cert_cover_5 7 2 4 5 6 7 224 992 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0537

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_one_six_0538.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0538

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 651, 341, 233, 369, 782, 326, 706, 834, 796, 696, 816, 992, 7, 11, 131, 21, 69, 41, 137, 49, 337, 97, 193, 14, 70, 262, 522, 194, 322, 578, 642, 770, 28, 780, 276, 324, 56, 536, 168, 648, 304, 560, 784, 224, 352, 672, 800, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_651, vertices_341, vertices_233, vertices_369, vertices_782, vertices_326, vertices_706, vertices_834, vertices_796, vertices_696, vertices_816, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_69, vertices_41, vertices_137, vertices_49, vertices_337, vertices_97, vertices_193, vertices_14, vertices_70, vertices_262, vertices_522, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_28, vertices_780, vertices_276, vertices_324, vertices_56, vertices_536, vertices_168, vertices_648, vertices_304, vertices_560, vertices_784, vertices_224, vertices_352, vertices_672, vertices_800, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_651), (false, vertices_341), (false, vertices_233), (false, vertices_369), (true, vertices_262), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_780), (true, vertices_536), (true, vertices_560), (true, vertices_784), (true, vertices_672), (true, vertices_800), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_651) then 13 else
  if p.val = (false, vertices_341) then 20 else
  if p.val = (false, vertices_233) then 18 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_322) then 1 else
  if p.val = (true, vertices_578) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_780) then 16 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_560) then 5 else
  if p.val = (true, vertices_784) then 6 else
  if p.val = (true, vertices_672) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_780), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 7 8 780
cert_row_4 1 2 3 4 6 8 696 56 3
cert_row_4 2 4 5 6 7 8 992 224 3
cert_rows_3
cert_pivot_3 2 1 4
cert_heightProof 3
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 14 782 3
cert_coverFacet 1 326
cert_cover_2 1 1 0 5 7 70 326 3
cert_coverFacet 2 706
cert_cover_2 2 5 0 6 8 194 706 3
cert_coverFacet 3 834
cert_cover_2 3 5 0 7 8 322 834 3
cert_coverFacet 4 796
cert_cover_5 4 0 1 2 3 7 28 796 3
cert_coverFacet 5 696
cert_cover_5 5 1 2 3 4 6 56 696 3
cert_coverFacet 6 816
cert_cover_2 6 4 3 7 8 304 816 3
cert_coverFacet 7 992
cert_cover_5 7 2 4 5 6 7 224 992 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0538

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_one_six_0539.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0539

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 323, 341, 793, 142, 714, 834, 172, 820, 484, 696, 992, 7, 11, 67, 259, 21, 69, 25, 777, 273, 321, 14, 134, 138, 522, 194, 322, 578, 770, 44, 140, 52, 276, 164, 292, 196, 324, 56, 536, 168, 648, 560, 784, 480, 672, 800, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_323, vertices_341, vertices_793, vertices_142, vertices_714, vertices_834, vertices_172, vertices_820, vertices_484, vertices_696, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_25, vertices_777, vertices_273, vertices_321, vertices_14, vertices_134, vertices_138, vertices_522, vertices_194, vertices_322, vertices_578, vertices_770, vertices_44, vertices_140, vertices_52, vertices_276, vertices_164, vertices_292, vertices_196, vertices_324, vertices_56, vertices_536, vertices_168, vertices_648, vertices_560, vertices_784, vertices_480, vertices_672, vertices_800, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_323), (false, vertices_341), (false, vertices_793), (true, vertices_138), (true, vertices_578), (true, vertices_140), (true, vertices_164), (true, vertices_292), (true, vertices_168), (true, vertices_648), (true, vertices_560), (true, vertices_480), (true, vertices_672), (true, vertices_800), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_779) then 19 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_341) then 17 else
  if p.val = (false, vertices_793) then 20 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_578) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_480) then 23 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(true, vertices_480), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 8 714 138 2
cert_row_2 1 4 5 6 7 480
cert_row_4 2 1 3 4 7 8 820 52 3
cert_row_4 3 2 3 4 6 8 696 56 3
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 714
cert_cover_5 1 0 0 2 5 6 138 714 2
cert_coverFacet 2 834
cert_cover_2 2 5 0 7 8 322 834 3
cert_coverFacet 3 172
cert_cover_2 3 2 1 4 6 44 172 3
cert_coverFacet 4 820
cert_cover_5 4 2 1 3 4 7 52 820 3
cert_coverFacet 5 484
cert_cover_5 5 1 1 4 5 6 164 484 2
cert_coverFacet 6 696
cert_cover_5 6 3 2 3 4 6 56 696 3
cert_coverFacet 7 992
cert_cover_5 7 1 4 5 6 8 480 992 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0539

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_one_six_0540.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0540

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 323, 653, 961, 278, 326, 794, 236, 372, 696, 944, 480, 7, 11, 67, 259, 13, 133, 521, 193, 321, 641, 769, 22, 70, 262, 26, 778, 274, 322, 44, 140, 52, 276, 100, 196, 324, 56, 536, 168, 648, 688, 304, 784, 224, 352, 416, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_323, vertices_653, vertices_961, vertices_278, vertices_326, vertices_794, vertices_236, vertices_372, vertices_696, vertices_944, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_133, vertices_521, vertices_193, vertices_321, vertices_641, vertices_769, vertices_22, vertices_70, vertices_262, vertices_26, vertices_778, vertices_274, vertices_322, vertices_44, vertices_140, vertices_52, vertices_276, vertices_100, vertices_196, vertices_324, vertices_56, vertices_536, vertices_168, vertices_648, vertices_688, vertices_304, vertices_784, vertices_224, vertices_352, vertices_416, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_323), (false, vertices_653), (false, vertices_961), (true, vertices_262), (true, vertices_274), (true, vertices_276), (true, vertices_100), (true, vertices_324), (true, vertices_536), (true, vertices_168), (true, vertices_688), (true, vertices_304), (true, vertices_784), (true, vertices_224), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 20 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_100) then 4 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_688) then 21 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_416) then 12 else
  0
cert_priority
cert_nodeAtPriority_29 323 262 274 276 100 324 536 168 304 784 224 352 416 199 779 653 688
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 7 8 778
cert_row_2 1 3 4 6 8 688
cert_row_4 2 1 2 4 5 6 236 44 3
cert_row_4 3 1 3 4 5 7 372 52 3
cert_rows
cert_pivot_2 0 8 2 1
cert_heightProof 4
cert_coverFacet 0 278
cert_cover_2 0 1 0 3 7 22 278 3
cert_coverFacet 1 326
cert_cover_2 1 1 0 5 7 70 326 3
cert_coverFacet 2 794
cert_cover_5 2 0 0 2 3 7 26 794 3
cert_coverFacet 3 236
cert_cover_5 3 2 1 2 4 5 44 236 3
cert_coverFacet 4 372
cert_cover_5 4 3 1 3 4 5 52 372 3
cert_coverFacet 5 696
cert_cover_5 5 1 2 3 4 6 56 696 3
cert_coverFacet 6 944
cert_cover_5 6 1 3 4 6 7 688 944 3
cert_coverFacet 7 480
cert_cover_2 7 5 4 6 7 224 480 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0540

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_one_six_0541.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0541

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 323, 653, 961, 86, 794, 338, 236, 372, 696, 944, 480, 7, 11, 67, 259, 13, 133, 521, 193, 321, 641, 769, 22, 70, 26, 778, 82, 274, 322, 44, 140, 52, 84, 100, 196, 56, 536, 168, 648, 688, 304, 336, 784, 224, 352, 416, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_323, vertices_653, vertices_961, vertices_86, vertices_794, vertices_338, vertices_236, vertices_372, vertices_696, vertices_944, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_133, vertices_521, vertices_193, vertices_321, vertices_641, vertices_769, vertices_22, vertices_70, vertices_26, vertices_778, vertices_82, vertices_274, vertices_322, vertices_44, vertices_140, vertices_52, vertices_84, vertices_100, vertices_196, vertices_56, vertices_536, vertices_168, vertices_648, vertices_688, vertices_304, vertices_336, vertices_784, vertices_224, vertices_352, vertices_416, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_323), (false, vertices_653), (false, vertices_961), (true, vertices_82), (true, vertices_274), (true, vertices_84), (true, vertices_100), (true, vertices_536), (true, vertices_168), (true, vertices_688), (true, vertices_304), (true, vertices_336), (true, vertices_784), (true, vertices_224), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 20 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_100) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_688) then 21 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_416) then 12 else
  0
cert_priority
cert_nodeAtPriority_29 323 82 274 84 100 536 168 304 336 784 224 352 416 199 779 653 688
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 7 8 778
cert_row_2 1 3 4 6 8 688
cert_row_4 2 1 2 4 5 6 236 44 3
cert_row_4 3 1 3 4 5 7 372 52 3
cert_rows
cert_pivot_2 0 8 2 1
cert_heightProof 4
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 794
cert_cover_5 1 0 0 2 3 7 26 794 3
cert_coverFacet 2 338
cert_cover_2 2 3 0 5 7 82 338 3
cert_coverFacet 3 236
cert_cover_5 3 2 1 2 4 5 44 236 3
cert_coverFacet 4 372
cert_cover_5 4 3 1 3 4 5 52 372 3
cert_coverFacet 5 696
cert_cover_5 5 1 2 3 4 6 56 696 3
cert_coverFacet 6 944
cert_cover_5 6 1 3 4 6 7 688 944 3
cert_coverFacet 7 480
cert_cover_2 7 5 4 6 7 224 480 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0541

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_one_six_0542.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0542

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 323, 653, 961, 278, 326, 794, 236, 372, 696, 880, 736, 7, 11, 67, 259, 13, 133, 521, 193, 321, 641, 769, 22, 70, 262, 26, 778, 274, 322, 44, 140, 52, 276, 100, 196, 324, 56, 536, 168, 648, 368, 560, 784, 224, 608, 672, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_323, vertices_653, vertices_961, vertices_278, vertices_326, vertices_794, vertices_236, vertices_372, vertices_696, vertices_880, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_13, vertices_133, vertices_521, vertices_193, vertices_321, vertices_641, vertices_769, vertices_22, vertices_70, vertices_262, vertices_26, vertices_778, vertices_274, vertices_322, vertices_44, vertices_140, vertices_52, vertices_276, vertices_100, vertices_196, vertices_324, vertices_56, vertices_536, vertices_168, vertices_648, vertices_368, vertices_560, vertices_784, vertices_224, vertices_608, vertices_672, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_323), (false, vertices_653), (false, vertices_961), (true, vertices_262), (true, vertices_274), (true, vertices_276), (true, vertices_100), (true, vertices_324), (true, vertices_536), (true, vertices_168), (true, vertices_368), (true, vertices_560), (true, vertices_784), (true, vertices_224), (true, vertices_608), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 20 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_100) then 4 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_368) then 21 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_608) then 11 else
  if p.val = (true, vertices_672) then 12 else
  0
cert_priority
cert_nodeAtPriority_29 323 262 274 276 100 324 536 168 560 784 224 608 672 199 779 653 368
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 7 8 778
cert_row_2 1 3 4 5 7 368
cert_row_4 2 1 2 4 5 6 236 44 3
cert_row_4 3 2 3 4 6 8 696 56 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 278
cert_cover_2 0 1 0 3 7 22 278 3
cert_coverFacet 1 326
cert_cover_2 1 1 0 5 7 70 326 3
cert_coverFacet 2 794
cert_cover_5 2 0 0 2 3 7 26 794 3
cert_coverFacet 3 236
cert_cover_5 3 2 1 2 4 5 44 236 3
cert_coverFacet 4 372
cert_cover_5 4 1 1 3 4 5 52 372 3
cert_coverFacet 5 696
cert_cover_5 5 3 2 3 4 6 56 696 3
cert_coverFacet 6 880
cert_cover_5 6 1 3 4 5 8 368 880 3
cert_coverFacet 7 736
cert_cover_2 7 5 4 6 8 224 736 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0542

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_one_six_0543.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0543

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 323, 341, 793, 142, 650, 962, 236, 820, 868, 696, 736, 7, 11, 67, 259, 21, 69, 25, 777, 273, 321, 14, 134, 138, 522, 194, 322, 642, 770, 44, 140, 52, 276, 100, 804, 196, 324, 56, 536, 168, 648, 560, 784, 224, 608, 672, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_323, vertices_341, vertices_793, vertices_142, vertices_650, vertices_962, vertices_236, vertices_820, vertices_868, vertices_696, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_259, vertices_21, vertices_69, vertices_25, vertices_777, vertices_273, vertices_321, vertices_14, vertices_134, vertices_138, vertices_522, vertices_194, vertices_322, vertices_642, vertices_770, vertices_44, vertices_140, vertices_52, vertices_276, vertices_100, vertices_804, vertices_196, vertices_324, vertices_56, vertices_536, vertices_168, vertices_648, vertices_560, vertices_784, vertices_224, vertices_608, vertices_672, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_323), (false, vertices_341), (false, vertices_793), (true, vertices_138), (true, vertices_642), (true, vertices_140), (true, vertices_100), (true, vertices_804), (true, vertices_168), (true, vertices_648), (true, vertices_560), (true, vertices_224), (true, vertices_608), (true, vertices_672), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_779) then 20 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_341) then 17 else
  if p.val = (false, vertices_793) then 21 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_100) then 4 else
  if p.val = (true, vertices_804) then 18 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_224) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_804), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 5 6 7 8 962 194 3
cert_row_2 1 1 4 7 8 804
cert_row_4 2 1 2 4 5 6 236 44 3
cert_row_4 3 2 3 4 6 8 696 56 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 650
cert_cover_2 1 2 0 6 8 138 650 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 194 962 3
cert_coverFacet 3 236
cert_cover_5 3 2 1 2 4 5 44 236 3
cert_coverFacet 4 820
cert_cover_5 4 1 1 3 4 7 52 820 3
cert_coverFacet 5 868
cert_cover_5 5 1 1 4 5 7 100 868 3
cert_coverFacet 6 696
cert_cover_5 6 3 2 3 4 6 56 696 3
cert_coverFacet 7 736
cert_cover_2 7 5 4 6 8 224 736 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0543

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_one_six_0544.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0544

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 139, 341, 233, 817, 353, 782, 326, 650, 962, 796, 696, 992, 7, 11, 131, 21, 69, 41, 137, 49, 273, 97, 289, 193, 321, 14, 70, 262, 138, 522, 194, 322, 642, 770, 28, 780, 276, 324, 56, 536, 168, 648, 560, 784, 224, 352, 672, 800, 960]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_139, vertices_341, vertices_233, vertices_817, vertices_353, vertices_782, vertices_326, vertices_650, vertices_962, vertices_796, vertices_696, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_21, vertices_69, vertices_41, vertices_137, vertices_49, vertices_273, vertices_97, vertices_289, vertices_193, vertices_321, vertices_14, vertices_70, vertices_262, vertices_138, vertices_522, vertices_194, vertices_322, vertices_642, vertices_770, vertices_28, vertices_780, vertices_276, vertices_324, vertices_56, vertices_536, vertices_168, vertices_648, vertices_560, vertices_784, vertices_224, vertices_352, vertices_672, vertices_800, vertices_960] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_139), (false, vertices_341), (false, vertices_233), (false, vertices_817), (false, vertices_353), (true, vertices_262), (true, vertices_522), (true, vertices_322), (true, vertices_642), (true, vertices_770), (true, vertices_780), (true, vertices_536), (true, vertices_648), (true, vertices_672), (true, vertices_960)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 16 18 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_199) then 11 else
  if p.val = (false, vertices_139) then 0 else
  if p.val = (false, vertices_341) then 14 else
  if p.val = (false, vertices_233) then 17 else
  if p.val = (false, vertices_817) then 19 else
  if p.val = (false, vertices_353) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_780) then 15 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_648) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_960) then 22 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_139), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_353), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_780), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(true, vertices_960), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 5 6 7 8 960
cert_row_2 1 1 2 7 8 780
cert_row_4 2 2 3 4 6 8 696 56 3
cert_rows_3
cert_pivot_3 1 5 2
cert_heightProof 3
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 14 782 3
cert_coverFacet 1 326
cert_cover_2 1 1 0 5 7 70 326 3
cert_coverFacet 2 650
cert_cover_2 2 2 0 6 8 138 650 3
cert_coverFacet 3 962
cert_cover_5 3 0 0 5 6 7 194 962 3
cert_coverFacet 4 796
cert_cover_5 4 1 1 2 3 7 28 796 3
cert_coverFacet 5 696
cert_cover_5 5 2 2 3 4 6 56 696 3
cert_coverFacet 6 992
cert_cover_5 6 0 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 3 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0544

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_one_six_0546.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0546

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 397, 961, 86, 602, 172, 628, 740, 440, 792, 840, 944, 7, 11, 67, 13, 133, 265, 193, 321, 385, 22, 70, 26, 74, 82, 44, 140, 52, 84, 612, 164, 196, 56, 280, 536, 168, 328, 584, 392, 776, 432, 560, 592, 784, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_397, vertices_961, vertices_86, vertices_602, vertices_172, vertices_628, vertices_740, vertices_440, vertices_792, vertices_840, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_74, vertices_82, vertices_44, vertices_140, vertices_52, vertices_84, vertices_612, vertices_164, vertices_196, vertices_56, vertices_280, vertices_536, vertices_168, vertices_328, vertices_584, vertices_392, vertices_776, vertices_432, vertices_560, vertices_592, vertices_784, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_84), (true, vertices_612), (true, vertices_164), (true, vertices_280), (true, vertices_536), (true, vertices_168), (true, vertices_584), (true, vertices_776), (true, vertices_432), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 20 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_331) then 14 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_84) then 1 else
  if p.val = (true, vertices_612) then 18 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_280) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_432) then 21 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_672) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_612), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(true, vertices_432), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 5 8 612
cert_row_2 1 3 4 6 7 432
cert_row_4 2 0 2 3 5 8 602 26 3
cert_rows_3
cert_pivot_3 4 1 0
cert_heightProof 3
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 602
cert_cover_5 1 2 0 2 3 5 26 602 3
cert_coverFacet 2 172
cert_cover_2 2 2 1 4 6 44 172 3
cert_coverFacet 3 628
cert_cover_5 3 0 1 3 4 5 52 628 3
cert_coverFacet 4 740
cert_cover_5 4 0 1 4 5 6 612 740 3
cert_coverFacet 5 440
cert_cover_5 5 1 2 3 4 6 56 440 3
cert_coverFacet 6 792
cert_cover_2 6 3 2 7 8 280 792 3
cert_coverFacet 7 840
cert_cover_2 7 5 2 7 8 328 840 3
cert_coverFacet 8 944
cert_cover_5 8 1 3 4 6 8 432 944 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 3 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0546

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_one_six_0547.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0547

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 397, 961, 534, 582, 602, 428, 692, 708, 376, 880, 928, 7, 11, 67, 13, 133, 265, 193, 321, 385, 22, 70, 518, 26, 74, 530, 578, 44, 396, 52, 532, 164, 196, 580, 644, 56, 88, 296, 328, 368, 560, 592, 416, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_397, vertices_961, vertices_534, vertices_582, vertices_602, vertices_428, vertices_692, vertices_708, vertices_376, vertices_880, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_518, vertices_26, vertices_74, vertices_530, vertices_578, vertices_44, vertices_396, vertices_52, vertices_532, vertices_164, vertices_196, vertices_580, vertices_644, vertices_56, vertices_88, vertices_296, vertices_328, vertices_368, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_397), (false, vertices_961), (true, vertices_518), (true, vertices_530), (true, vertices_578), (true, vertices_532), (true, vertices_164), (true, vertices_580), (true, vertices_644), (true, vertices_88), (true, vertices_296), (true, vertices_368), (true, vertices_560), (true, vertices_592), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 21 23 24 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_199) then 15 else
  if p.val = (false, vertices_331) then 16 else
  if p.val = (false, vertices_397) then 19 else
  if p.val = (false, vertices_961) then 25 else
  if p.val = (true, vertices_518) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_578) then 2 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_580) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_368) then 22 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_416) then 11 else
  if p.val = (true, vertices_672) then 12 else
  if p.val = (true, vertices_800) then 13 else
  0
cert_priority
cert_nodeAtPriority_46 518 530 578 532 164 580 644 88 296 560 592 416 672 800 199 331 397 368
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 8 602 26 3
cert_row_2 1 1 2 6 7 396
cert_row_2 2 3 4 5 7 368
cert_row_4 3 1 3 4 6 8 692 52 3
cert_rows
cert_pivot_2 0 2 5 1
cert_heightProof 4
cert_coverFacet 0 534
cert_cover_2 0 1 0 3 8 22 534 3
cert_coverFacet 1 582
cert_cover_2 1 1 0 5 8 70 582 3
cert_coverFacet 2 602
cert_cover_5 2 0 0 2 3 5 26 602 3
cert_coverFacet 3 428
cert_cover_5 3 1 1 2 4 6 44 428 3
cert_coverFacet 4 692
cert_cover_5 4 3 1 3 4 6 52 692 3
cert_coverFacet 5 708
cert_cover_2 5 5 1 6 8 196 708 3
cert_coverFacet 6 376
cert_cover_5 6 2 2 3 4 5 56 376 3
cert_coverFacet 7 880
cert_cover_5 7 2 3 4 5 8 368 880 3
cert_coverFacet 8 928
cert_cover_2 8 6 4 7 8 416 928 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0547

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_one_six_0549.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0549

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 269, 389, 961, 86, 282, 850, 428, 628, 740, 696, 920, 7, 11, 67, 13, 133, 261, 265, 193, 321, 385, 22, 70, 26, 266, 82, 274, 322, 44, 268, 52, 84, 612, 164, 196, 388, 56, 664, 280, 168, 392, 560, 592, 784, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_269, vertices_389, vertices_961, vertices_86, vertices_282, vertices_850, vertices_428, vertices_628, vertices_740, vertices_696, vertices_920] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_261, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_266, vertices_82, vertices_274, vertices_322, vertices_44, vertices_268, vertices_52, vertices_84, vertices_612, vertices_164, vertices_196, vertices_388, vertices_56, vertices_664, vertices_280, vertices_168, vertices_392, vertices_560, vertices_592, vertices_784, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_269), (false, vertices_389), (false, vertices_961), (true, vertices_82), (true, vertices_274), (true, vertices_84), (true, vertices_612), (true, vertices_164), (true, vertices_664), (true, vertices_280), (true, vertices_168), (true, vertices_392), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_331) then 15 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_389) then 1 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_612) then 18 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_664) then 20 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_392) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_672) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_269), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_612), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(true, vertices_664), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 7 8 850 82 3
cert_row_2 1 1 4 5 8 612
cert_row_2 2 2 3 6 8 664
cert_row_4 3 1 2 4 6 7 428 44 3
cert_rows
cert_pivot_2 0 5 3 1
cert_heightProof 4
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 850
cert_cover_5 2 0 0 3 5 7 82 850 3
cert_coverFacet 3 428
cert_cover_5 3 3 1 2 4 6 44 428 3
cert_coverFacet 4 628
cert_cover_5 4 1 1 3 4 5 52 628 3
cert_coverFacet 5 740
cert_cover_5 5 1 1 4 5 6 612 740 3
cert_coverFacet 6 696
cert_cover_5 6 2 2 3 4 6 56 696 3
cert_coverFacet 7 920
cert_cover_5 7 2 2 3 6 7 664 920 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0549

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_one_six_0550.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0550

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 269, 389, 961, 598, 794, 834, 428, 244, 824, 752, 928, 7, 11, 67, 13, 133, 261, 265, 193, 321, 385, 22, 70, 26, 266, 530, 322, 578, 770, 44, 268, 52, 84, 164, 196, 388, 56, 792, 296, 240, 560, 592, 416, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_269, vertices_389, vertices_961, vertices_598, vertices_794, vertices_834, vertices_428, vertices_244, vertices_824, vertices_752, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_261, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_266, vertices_530, vertices_322, vertices_578, vertices_770, vertices_44, vertices_268, vertices_52, vertices_84, vertices_164, vertices_196, vertices_388, vertices_56, vertices_792, vertices_296, vertices_240, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_269), (false, vertices_389), (false, vertices_961), (true, vertices_530), (true, vertices_578), (true, vertices_770), (true, vertices_84), (true, vertices_164), (true, vertices_792), (true, vertices_296), (true, vertices_240), (true, vertices_560), (true, vertices_592), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_331) then 15 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_389) then 1 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_792) then 19 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_240) then 21 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_416) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_269), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(true, vertices_792), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
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
cert_coverFacet 2 834
cert_cover_2 2 5 0 7 8 322 834 3
cert_coverFacet 3 428
cert_cover_5 3 3 1 2 4 6 44 428 3
cert_coverFacet 4 244
cert_cover_5 4 1 1 3 4 5 52 244 3
cert_coverFacet 5 824
cert_cover_5 5 2 2 3 4 7 56 824 3
cert_coverFacet 6 752
cert_cover_5 6 1 3 4 5 8 240 752 3
cert_coverFacet 7 928
cert_cover_2 7 6 4 7 8 416 928 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0550

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_one_six_0551.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0551

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 269, 389, 961, 86, 794, 850, 428, 628, 740, 696, 904, 7, 11, 67, 13, 133, 261, 265, 193, 321, 385, 22, 70, 26, 266, 82, 786, 322, 44, 268, 52, 84, 612, 164, 196, 388, 56, 536, 168, 392, 648, 776, 560, 592, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_269, vertices_389, vertices_961, vertices_86, vertices_794, vertices_850, vertices_428, vertices_628, vertices_740, vertices_696, vertices_904] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_261, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_266, vertices_82, vertices_786, vertices_322, vertices_44, vertices_268, vertices_52, vertices_84, vertices_612, vertices_164, vertices_196, vertices_388, vertices_56, vertices_536, vertices_168, vertices_392, vertices_648, vertices_776, vertices_560, vertices_592, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_269), (false, vertices_389), (false, vertices_961), (true, vertices_82), (true, vertices_786), (true, vertices_84), (true, vertices_612), (true, vertices_164), (true, vertices_536), (true, vertices_168), (true, vertices_392), (true, vertices_648), (true, vertices_776), (true, vertices_560), (true, vertices_592), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 13 20 21 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_331) then 18 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_389) then 1 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_786) then 19 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_612) then 15 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_392) then 7 else
  if p.val = (true, vertices_648) then 8 else
  if p.val = (true, vertices_776) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_672) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_269), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_612), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_786), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 7 8 786
cert_row_2 1 1 4 5 8 612
cert_row_4 2 1 2 4 6 7 428 44 3
cert_row_4 3 2 3 4 6 8 696 56 3
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 794
cert_cover_5 1 0 0 2 3 7 26 794 3
cert_coverFacet 2 850
cert_cover_5 2 0 0 3 5 7 82 850 3
cert_coverFacet 3 428
cert_cover_5 3 2 1 2 4 6 44 428 3
cert_coverFacet 4 628
cert_cover_5 4 1 1 3 4 5 52 628 3
cert_coverFacet 5 740
cert_cover_5 5 1 1 4 5 6 612 740 3
cert_coverFacet 6 696
cert_cover_5 6 3 2 3 4 6 56 696 3
cert_coverFacet 7 904
cert_cover_2 7 6 2 7 8 392 904 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0551

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_one_six_0552.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0552

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 141, 393, 961, 598, 794, 834, 428, 244, 824, 752, 928, 7, 11, 67, 13, 133, 137, 265, 193, 321, 385, 22, 70, 26, 266, 530, 322, 578, 770, 44, 140, 52, 84, 164, 196, 56, 792, 296, 392, 240, 560, 592, 416, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_141, vertices_393, vertices_961, vertices_598, vertices_794, vertices_834, vertices_428, vertices_244, vertices_824, vertices_752, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_137, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_266, vertices_530, vertices_322, vertices_578, vertices_770, vertices_44, vertices_140, vertices_52, vertices_84, vertices_164, vertices_196, vertices_56, vertices_792, vertices_296, vertices_392, vertices_240, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_141), (false, vertices_393), (false, vertices_961), (true, vertices_530), (true, vertices_578), (true, vertices_770), (true, vertices_84), (true, vertices_164), (true, vertices_792), (true, vertices_296), (true, vertices_240), (true, vertices_560), (true, vertices_592), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 20 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_331) then 15 else
  if p.val = (false, vertices_141) then 0 else
  if p.val = (false, vertices_393) then 1 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_770) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_792) then 19 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_240) then 21 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_416) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_141), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_393), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(true, vertices_792), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
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
cert_coverFacet 2 834
cert_cover_2 2 5 0 7 8 322 834 3
cert_coverFacet 3 428
cert_cover_5 3 3 1 2 4 6 44 428 3
cert_coverFacet 4 244
cert_cover_5 4 1 1 3 4 5 52 244 3
cert_coverFacet 5 824
cert_cover_5 5 2 2 3 4 7 56 824 3
cert_coverFacet 6 752
cert_cover_5 6 1 3 4 5 8 240 752 3
cert_coverFacet 7 928
cert_cover_2 7 6 4 7 8 416 928 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0552

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_one_six_0553.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0553

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 397, 961, 598, 282, 786, 834, 172, 244, 824, 936, 752, 7, 11, 67, 13, 133, 265, 193, 321, 385, 22, 70, 26, 266, 274, 530, 322, 578, 770, 44, 140, 52, 84, 164, 196, 56, 280, 168, 808, 392, 240, 560, 592, 784, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_397, vertices_961, vertices_598, vertices_282, vertices_786, vertices_834, vertices_172, vertices_244, vertices_824, vertices_936, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_266, vertices_274, vertices_530, vertices_322, vertices_578, vertices_770, vertices_44, vertices_140, vertices_52, vertices_84, vertices_164, vertices_196, vertices_56, vertices_280, vertices_168, vertices_808, vertices_392, vertices_240, vertices_560, vertices_592, vertices_784, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_397), (false, vertices_961), (true, vertices_274), (true, vertices_530), (true, vertices_578), (true, vertices_770), (true, vertices_84), (true, vertices_164), (true, vertices_280), (true, vertices_168), (true, vertices_808), (true, vertices_240), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_331) then 14 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_274) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_578) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_808) then 19 else
  if p.val = (true, vertices_240) then 21 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_672) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(true, vertices_808), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 5 6 240
cert_row_2 1 2 4 7 8 808
cert_row_4 2 0 1 3 5 8 598 22 3
cert_rows_3
cert_pivot_3 2 6 0
cert_heightProof 3
cert_coverFacet 0 598
cert_cover_5 0 2 0 1 3 5 22 598 3
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 786
cert_cover_2 2 3 0 7 8 274 786 3
cert_coverFacet 3 834
cert_cover_2 3 5 0 7 8 322 834 3
cert_coverFacet 4 172
cert_cover_2 4 2 1 4 6 44 172 3
cert_coverFacet 5 244
cert_cover_5 5 0 1 3 4 5 52 244 3
cert_coverFacet 6 824
cert_cover_5 6 1 2 3 4 7 56 824 3
cert_coverFacet 7 936
cert_cover_5 7 1 2 4 6 7 168 936 3
cert_coverFacet 8 752
cert_cover_5 8 0 3 4 5 8 240 752 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 3 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0553

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_one_six_0554.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0554

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 397, 961, 86, 794, 594, 834, 172, 628, 740, 440, 944, 7, 11, 67, 13, 133, 265, 193, 321, 385, 22, 70, 26, 266, 82, 530, 322, 578, 770, 44, 140, 52, 84, 612, 164, 196, 56, 280, 168, 392, 432, 560, 592, 784, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_397, vertices_961, vertices_86, vertices_794, vertices_594, vertices_834, vertices_172, vertices_628, vertices_740, vertices_440, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_266, vertices_82, vertices_530, vertices_322, vertices_578, vertices_770, vertices_44, vertices_140, vertices_52, vertices_84, vertices_612, vertices_164, vertices_196, vertices_56, vertices_280, vertices_168, vertices_392, vertices_432, vertices_560, vertices_592, vertices_784, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_530), (true, vertices_578), (true, vertices_770), (true, vertices_84), (true, vertices_612), (true, vertices_164), (true, vertices_280), (true, vertices_168), (true, vertices_432), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 20 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_331) then 14 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_578) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_612) then 18 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_432) then 21 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_672) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_612), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(true, vertices_432), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 5 8 612
cert_row_2 1 3 4 6 7 432
cert_row_4 2 0 2 3 7 8 794 26 3
cert_rows_3
cert_pivot_3 4 1 0
cert_heightProof 3
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 794
cert_cover_5 1 2 0 2 3 7 26 794 3
cert_coverFacet 2 594
cert_cover_2 2 3 0 5 8 82 594 3
cert_coverFacet 3 834
cert_cover_2 3 5 0 7 8 322 834 3
cert_coverFacet 4 172
cert_cover_2 4 2 1 4 6 44 172 3
cert_coverFacet 5 628
cert_cover_5 5 0 1 3 4 5 52 628 3
cert_coverFacet 6 740
cert_cover_5 6 0 1 4 5 6 612 740 3
cert_coverFacet 7 440
cert_cover_5 7 1 2 3 4 6 56 440 3
cert_coverFacet 8 944
cert_cover_5 8 1 3 4 6 8 432 944 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 3 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0554

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_one_six_0555.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0555

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 397, 961, 598, 794, 834, 172, 628, 228, 440, 944, 736, 7, 11, 67, 13, 133, 265, 193, 321, 385, 22, 70, 26, 266, 530, 322, 578, 770, 44, 140, 52, 596, 100, 164, 196, 56, 280, 168, 392, 432, 560, 784, 224, 608, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_397, vertices_961, vertices_598, vertices_794, vertices_834, vertices_172, vertices_628, vertices_228, vertices_440, vertices_944, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_266, vertices_530, vertices_322, vertices_578, vertices_770, vertices_44, vertices_140, vertices_52, vertices_596, vertices_100, vertices_164, vertices_196, vertices_56, vertices_280, vertices_168, vertices_392, vertices_432, vertices_560, vertices_784, vertices_224, vertices_608, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_397), (false, vertices_961), (true, vertices_530), (true, vertices_578), (true, vertices_770), (true, vertices_596), (true, vertices_100), (true, vertices_164), (true, vertices_280), (true, vertices_168), (true, vertices_432), (true, vertices_560), (true, vertices_784), (true, vertices_224), (true, vertices_608), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 20 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_331) then 14 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_530) then 0 else
  if p.val = (true, vertices_578) then 1 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_596) then 18 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_432) then 21 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_672) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_596), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(true, vertices_432), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 5 8 596
cert_row_2 1 3 4 6 7 432
cert_row_4 2 0 2 3 7 8 794 26 3
cert_rows_3
cert_pivot_3 4 1 0
cert_heightProof 3
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 22 598 3
cert_coverFacet 1 794
cert_cover_5 1 2 0 2 3 7 26 794 3
cert_coverFacet 2 834
cert_cover_2 2 5 0 7 8 322 834 3
cert_coverFacet 3 172
cert_cover_2 3 2 1 4 6 44 172 3
cert_coverFacet 4 628
cert_cover_5 4 0 1 3 4 5 52 628 3
cert_coverFacet 5 228
cert_cover_2 5 4 1 5 6 100 228 3
cert_coverFacet 6 440
cert_cover_5 6 1 2 3 4 6 56 440 3
cert_coverFacet 7 944
cert_cover_5 7 1 3 4 6 8 432 944 3
cert_coverFacet 8 736
cert_cover_2 8 5 4 6 8 224 736 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 3 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0555

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_one_six_0556.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0556

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 397, 961, 598, 794, 834, 172, 244, 824, 424, 752, 928, 7, 11, 67, 13, 133, 265, 193, 321, 385, 22, 70, 26, 266, 530, 322, 578, 770, 44, 140, 52, 84, 164, 196, 56, 792, 168, 296, 392, 240, 560, 592, 416, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_397, vertices_961, vertices_598, vertices_794, vertices_834, vertices_172, vertices_244, vertices_824, vertices_424, vertices_752, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_266, vertices_530, vertices_322, vertices_578, vertices_770, vertices_44, vertices_140, vertices_52, vertices_84, vertices_164, vertices_196, vertices_56, vertices_792, vertices_168, vertices_296, vertices_392, vertices_240, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_397), (false, vertices_961), (true, vertices_530), (true, vertices_578), (true, vertices_770), (true, vertices_84), (true, vertices_164), (true, vertices_792), (true, vertices_168), (true, vertices_296), (true, vertices_240), (true, vertices_560), (true, vertices_592), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_331) then 14 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_530) then 0 else
  if p.val = (true, vertices_578) then 1 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_792) then 19 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_240) then 21 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
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
  | 19 => Sum.inr ⟨(true, vertices_792), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 5 6 240
cert_row_2 1 2 3 7 8 792
cert_row_4 2 0 1 3 5 8 598 22 3
cert_rows_3
cert_pivot_3 2 4 0
cert_heightProof 3
cert_coverFacet 0 598
cert_cover_5 0 2 0 1 3 5 22 598 3
cert_coverFacet 1 794
cert_cover_5 1 1 0 2 3 7 26 794 3
cert_coverFacet 2 834
cert_cover_2 2 5 0 7 8 322 834 3
cert_coverFacet 3 172
cert_cover_2 3 2 1 4 6 44 172 3
cert_coverFacet 4 244
cert_cover_5 4 0 1 3 4 5 52 244 3
cert_coverFacet 5 824
cert_cover_5 5 1 2 3 4 7 56 824 3
cert_coverFacet 6 424
cert_cover_2 6 4 2 6 7 168 424 3
cert_coverFacet 7 752
cert_cover_5 7 0 3 4 5 8 240 752 3
cert_coverFacet 8 928
cert_cover_2 8 6 4 7 8 416 928 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 3 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0556

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_one_six_0557.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0557

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 397, 961, 86, 282, 850, 812, 244, 676, 900, 824, 752, 7, 11, 67, 13, 133, 265, 193, 321, 385, 22, 70, 26, 266, 82, 274, 322, 44, 268, 52, 84, 164, 548, 196, 388, 644, 772, 56, 280, 808, 240, 560, 592, 784, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_397, vertices_961, vertices_86, vertices_282, vertices_850, vertices_812, vertices_244, vertices_676, vertices_900, vertices_824, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_266, vertices_82, vertices_274, vertices_322, vertices_44, vertices_268, vertices_52, vertices_84, vertices_164, vertices_548, vertices_196, vertices_388, vertices_644, vertices_772, vertices_56, vertices_280, vertices_808, vertices_240, vertices_560, vertices_592, vertices_784, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_274), (true, vertices_84), (true, vertices_164), (true, vertices_548), (true, vertices_644), (true, vertices_772), (true, vertices_280), (true, vertices_808), (true, vertices_240), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_331) then 14 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_772) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_808) then 19 else
  if p.val = (true, vertices_240) then 21 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_672) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(true, vertices_808), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
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
cert_coverFacet 3 812
cert_cover_5 3 1 1 2 4 7 44 812 3
cert_coverFacet 4 244
cert_cover_5 4 0 1 3 4 5 52 244 3
cert_coverFacet 5 676
cert_cover_2 5 4 1 6 8 164 676 3
cert_coverFacet 6 900
cert_cover_2 6 6 1 7 8 388 900 3
cert_coverFacet 7 824
cert_cover_5 7 1 2 3 4 7 56 824 3
cert_coverFacet 8 752
cert_cover_5 8 0 3 4 5 8 240 752 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 3 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0557

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_one_six_0558.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0558

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 397, 961, 598, 794, 834, 300, 244, 420, 824, 752, 928, 7, 11, 67, 13, 133, 265, 193, 321, 385, 22, 70, 26, 266, 530, 322, 578, 770, 44, 268, 52, 84, 164, 292, 196, 388, 56, 792, 296, 240, 560, 592, 416, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_397, vertices_961, vertices_598, vertices_794, vertices_834, vertices_300, vertices_244, vertices_420, vertices_824, vertices_752, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_266, vertices_530, vertices_322, vertices_578, vertices_770, vertices_44, vertices_268, vertices_52, vertices_84, vertices_164, vertices_292, vertices_196, vertices_388, vertices_56, vertices_792, vertices_296, vertices_240, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_397), (false, vertices_961), (true, vertices_530), (true, vertices_578), (true, vertices_770), (true, vertices_84), (true, vertices_164), (true, vertices_292), (true, vertices_792), (true, vertices_296), (true, vertices_240), (true, vertices_560), (true, vertices_592), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_331) then 14 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_530) then 0 else
  if p.val = (true, vertices_578) then 1 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_792) then 19 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_240) then 21 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
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
  | 19 => Sum.inr ⟨(true, vertices_792), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 5 6 240
cert_row_2 1 2 3 7 8 792
cert_row_4 2 0 1 3 5 8 598 22 3
cert_rows_3
cert_pivot_3 2 4 0
cert_heightProof 3
cert_coverFacet 0 598
cert_cover_5 0 2 0 1 3 5 22 598 3
cert_coverFacet 1 794
cert_cover_5 1 1 0 2 3 7 26 794 3
cert_coverFacet 2 834
cert_cover_2 2 5 0 7 8 322 834 3
cert_coverFacet 3 300
cert_cover_2 3 2 1 4 7 44 300 3
cert_coverFacet 4 244
cert_cover_5 4 0 1 3 4 5 52 244 3
cert_coverFacet 5 420
cert_cover_2 5 4 1 6 7 164 420 3
cert_coverFacet 6 824
cert_cover_5 6 1 2 3 4 7 56 824 3
cert_coverFacet 7 752
cert_cover_5 7 0 3 4 5 8 240 752 3
cert_coverFacet 8 928
cert_cover_2 8 6 4 7 8 416 928 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 3 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0558

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_one_six_0559.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0559

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 397, 961, 86, 794, 594, 834, 300, 244, 932, 824, 752, 7, 11, 67, 13, 133, 265, 193, 321, 385, 22, 70, 26, 266, 82, 530, 322, 578, 770, 44, 268, 52, 84, 164, 292, 196, 388, 56, 792, 296, 240, 560, 592, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_397, vertices_961, vertices_86, vertices_794, vertices_594, vertices_834, vertices_300, vertices_244, vertices_932, vertices_824, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_266, vertices_82, vertices_530, vertices_322, vertices_578, vertices_770, vertices_44, vertices_268, vertices_52, vertices_84, vertices_164, vertices_292, vertices_196, vertices_388, vertices_56, vertices_792, vertices_296, vertices_240, vertices_560, vertices_592, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_397), (false, vertices_961), (true, vertices_82), (true, vertices_530), (true, vertices_578), (true, vertices_770), (true, vertices_84), (true, vertices_164), (true, vertices_292), (true, vertices_792), (true, vertices_296), (true, vertices_240), (true, vertices_560), (true, vertices_592), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_331) then 14 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_578) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_792) then 19 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_240) then 21 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_672) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(true, vertices_792), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(true, vertices_240), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 5 6 240
cert_row_2 1 2 3 7 8 792
cert_row_4 2 1 4 6 7 8 932 164 3
cert_rows_3
cert_pivot_3 2 5 1
cert_heightProof 3
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 794
cert_cover_5 1 1 0 2 3 7 26 794 3
cert_coverFacet 2 594
cert_cover_2 2 3 0 5 8 82 594 3
cert_coverFacet 3 834
cert_cover_2 3 5 0 7 8 322 834 3
cert_coverFacet 4 300
cert_cover_2 4 2 1 4 7 44 300 3
cert_coverFacet 5 244
cert_cover_5 5 0 1 3 4 5 52 244 3
cert_coverFacet 6 932
cert_cover_5 6 2 1 4 6 7 164 932 3
cert_coverFacet 7 824
cert_cover_5 7 1 2 3 4 7 56 824 3
cert_coverFacet 8 752
cert_cover_5 8 0 3 4 5 8 240 752 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 3 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0559

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_one_six_0560.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0560

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 397, 961, 598, 282, 786, 834, 428, 244, 824, 752, 928, 7, 11, 67, 13, 133, 265, 193, 321, 385, 22, 70, 26, 266, 274, 530, 322, 578, 770, 44, 396, 52, 84, 164, 196, 56, 280, 296, 240, 560, 592, 784, 416, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_397, vertices_961, vertices_598, vertices_282, vertices_786, vertices_834, vertices_428, vertices_244, vertices_824, vertices_752, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_266, vertices_274, vertices_530, vertices_322, vertices_578, vertices_770, vertices_44, vertices_396, vertices_52, vertices_84, vertices_164, vertices_196, vertices_56, vertices_280, vertices_296, vertices_240, vertices_560, vertices_592, vertices_784, vertices_416, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_397), (false, vertices_961), (true, vertices_274), (true, vertices_530), (true, vertices_578), (true, vertices_770), (true, vertices_84), (true, vertices_164), (true, vertices_280), (true, vertices_296), (true, vertices_240), (true, vertices_560), (true, vertices_592), (true, vertices_784), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 21 23 24 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_199) then 15 else
  if p.val = (false, vertices_331) then 16 else
  if p.val = (false, vertices_397) then 19 else
  if p.val = (false, vertices_961) then 25 else
  if p.val = (true, vertices_274) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_578) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_240) then 22 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_416) then 11 else
  if p.val = (true, vertices_672) then 12 else
  if p.val = (true, vertices_800) then 13 else
  0
cert_priority
cert_nodeAtPriority_46 274 530 578 770 84 164 280 296 560 592 784 416 672 800 199 331 397 240
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 8 598 22 3
cert_row_2 1 1 2 6 7 396
cert_row_2 2 3 4 5 6 240
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 0 1 5 2
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 22 598 3
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 786
cert_cover_2 2 3 0 7 8 274 786 3
cert_coverFacet 3 834
cert_cover_2 3 5 0 7 8 322 834 3
cert_coverFacet 4 428
cert_cover_5 4 1 1 2 4 6 44 428 3
cert_coverFacet 5 244
cert_cover_5 5 2 1 3 4 5 52 244 3
cert_coverFacet 6 824
cert_cover_5 6 3 2 3 4 7 56 824 3
cert_coverFacet 7 752
cert_cover_5 7 2 3 4 5 8 240 752 3
cert_coverFacet 8 928
cert_cover_2 8 6 4 7 8 416 928 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0560

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_one_six_0561.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0561

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 397, 961, 598, 538, 778, 834, 428, 244, 824, 752, 928, 7, 11, 67, 13, 133, 265, 193, 321, 385, 22, 70, 26, 266, 522, 530, 322, 578, 770, 44, 396, 52, 84, 164, 196, 56, 536, 296, 776, 240, 560, 592, 416, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_397, vertices_961, vertices_598, vertices_538, vertices_778, vertices_834, vertices_428, vertices_244, vertices_824, vertices_752, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_266, vertices_522, vertices_530, vertices_322, vertices_578, vertices_770, vertices_44, vertices_396, vertices_52, vertices_84, vertices_164, vertices_196, vertices_56, vertices_536, vertices_296, vertices_776, vertices_240, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_397), (false, vertices_961), (true, vertices_522), (true, vertices_530), (true, vertices_578), (true, vertices_770), (true, vertices_84), (true, vertices_164), (true, vertices_536), (true, vertices_296), (true, vertices_776), (true, vertices_240), (true, vertices_560), (true, vertices_592), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 21 23 24 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_199) then 15 else
  if p.val = (false, vertices_331) then 16 else
  if p.val = (false, vertices_397) then 19 else
  if p.val = (false, vertices_961) then 25 else
  if p.val = (true, vertices_522) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_578) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_240) then 22 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_416) then 11 else
  if p.val = (true, vertices_672) then 12 else
  if p.val = (true, vertices_800) then 13 else
  0
cert_priority
cert_nodeAtPriority_46 522 530 578 770 84 164 536 296 776 560 592 416 672 800 199 331 397 240
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 8 598 22 3
cert_row_2 1 1 2 6 7 396
cert_row_2 2 3 4 5 6 240
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 0 1 5 2
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 22 598 3
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 834
cert_cover_2 3 5 0 7 8 322 834 3
cert_coverFacet 4 428
cert_cover_5 4 1 1 2 4 6 44 428 3
cert_coverFacet 5 244
cert_cover_5 5 2 1 3 4 5 52 244 3
cert_coverFacet 6 824
cert_cover_5 6 3 2 3 4 7 56 824 3
cert_coverFacet 7 752
cert_cover_5 7 2 3 4 5 8 240 752 3
cert_coverFacet 8 928
cert_cover_2 8 6 4 7 8 416 928 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0561

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_4685 : Certifies 4685 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0530.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4686 : Certifies 4686 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0531.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4687 : Certifies 4687 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0532.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4688 : Certifies 4688 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0533.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4689 : Certifies 4689 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0534.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4690 : Certifies 4690 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0535.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4691 : Certifies 4691 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0536.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4692 : Certifies 4692 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0537.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4693 : Certifies 4693 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0538.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4694 : Certifies 4694 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0539.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4695 : Certifies 4695 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0540.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4696 : Certifies 4696 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0541.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4697 : Certifies 4697 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0542.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4698 : Certifies 4698 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0543.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4699 : Certifies 4699 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0544.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4700 : Certifies 4700 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0546.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4701 : Certifies 4701 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0547.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4702 : Certifies 4702 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0549.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4703 : Certifies 4703 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0550.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4704 : Certifies 4704 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0551.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4705 : Certifies 4705 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0552.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4706 : Certifies 4706 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0553.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4707 : Certifies 4707 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0554.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4708 : Certifies 4708 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0555.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4709 : Certifies 4709 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0556.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4710 : Certifies 4710 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0557.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4711 : Certifies 4711 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0558.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4712 : Certifies 4712 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0559.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4713 : Certifies 4713 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0560.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4714 : Certifies 4714 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0561.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B155 (j : Fin 30) :
    Certifies (4685 + j.val) := by
  fin_cases j
  · exact projection_4685
  · exact projection_4686
  · exact projection_4687
  · exact projection_4688
  · exact projection_4689
  · exact projection_4690
  · exact projection_4691
  · exact projection_4692
  · exact projection_4693
  · exact projection_4694
  · exact projection_4695
  · exact projection_4696
  · exact projection_4697
  · exact projection_4698
  · exact projection_4699
  · exact projection_4700
  · exact projection_4701
  · exact projection_4702
  · exact projection_4703
  · exact projection_4704
  · exact projection_4705
  · exact projection_4706
  · exact projection_4707
  · exact projection_4708
  · exact projection_4709
  · exact projection_4710
  · exact projection_4711
  · exact projection_4712
  · exact projection_4713
  · exact projection_4714

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
