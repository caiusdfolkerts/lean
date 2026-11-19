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
/- Source: ProjectionCertificates/R_one_six_0562.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0562

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 653, 777, 961, 86, 794, 338, 172, 372, 484, 696, 944, 7, 11, 67, 13, 133, 265, 521, 193, 321, 641, 769, 22, 70, 26, 266, 82, 274, 322, 44, 140, 52, 84, 356, 164, 196, 56, 536, 168, 648, 776, 688, 304, 336, 784, 416, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_653, vertices_777, vertices_961, vertices_86, vertices_794, vertices_338, vertices_172, vertices_372, vertices_484, vertices_696, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_265, vertices_521, vertices_193, vertices_321, vertices_641, vertices_769, vertices_22, vertices_70, vertices_26, vertices_266, vertices_82, vertices_274, vertices_322, vertices_44, vertices_140, vertices_52, vertices_84, vertices_356, vertices_164, vertices_196, vertices_56, vertices_536, vertices_168, vertices_648, vertices_776, vertices_688, vertices_304, vertices_336, vertices_784, vertices_416, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_653), (false, vertices_777), (false, vertices_961), (true, vertices_82), (true, vertices_274), (true, vertices_84), (true, vertices_356), (true, vertices_164), (true, vertices_536), (true, vertices_168), (true, vertices_688), (true, vertices_304), (true, vertices_336), (true, vertices_784), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 18 19 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_331) then 13 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_356) then 17 else
  if p.val = (true, vertices_164) then 4 else
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
  | 0 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
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
cert_row_4 2 0 2 3 7 8 794 26 3
cert_rows_3
cert_pivot_3 4 1 0
cert_heightProof 3
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 794
cert_cover_5 1 2 0 2 3 7 26 794 3
cert_coverFacet 2 338
cert_cover_2 2 3 0 5 7 82 338 3
cert_coverFacet 3 172
cert_cover_2 3 2 1 4 6 44 172 3
cert_coverFacet 4 372
cert_cover_5 4 0 1 3 4 5 52 372 3
cert_coverFacet 5 484
cert_cover_5 5 0 1 4 5 6 356 484 3
cert_coverFacet 6 696
cert_cover_5 6 1 2 3 4 6 56 696 3
cert_coverFacet 7 944
cert_cover_5 7 1 3 4 6 7 688 944 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0562

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_one_six_0563.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0563

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 653, 777, 961, 342, 794, 172, 372, 228, 696, 944, 480, 7, 11, 67, 13, 133, 265, 521, 193, 321, 641, 769, 22, 70, 26, 266, 274, 322, 44, 140, 52, 340, 100, 164, 196, 56, 536, 168, 648, 776, 688, 304, 784, 224, 352, 416, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_653, vertices_777, vertices_961, vertices_342, vertices_794, vertices_172, vertices_372, vertices_228, vertices_696, vertices_944, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_265, vertices_521, vertices_193, vertices_321, vertices_641, vertices_769, vertices_22, vertices_70, vertices_26, vertices_266, vertices_274, vertices_322, vertices_44, vertices_140, vertices_52, vertices_340, vertices_100, vertices_164, vertices_196, vertices_56, vertices_536, vertices_168, vertices_648, vertices_776, vertices_688, vertices_304, vertices_784, vertices_224, vertices_352, vertices_416, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_653), (false, vertices_777), (false, vertices_961), (true, vertices_274), (true, vertices_340), (true, vertices_100), (true, vertices_164), (true, vertices_536), (true, vertices_168), (true, vertices_688), (true, vertices_304), (true, vertices_784), (true, vertices_224), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 18 19 21 22 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_331) then 13 else
  if p.val = (false, vertices_653) then 16 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (false, vertices_961) then 23 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_340) then 17 else
  if p.val = (true, vertices_100) then 2 else
  if p.val = (true, vertices_164) then 3 else
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
  | 0 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
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
cert_row_4 2 0 2 3 7 8 794 26 3
cert_rows_3
cert_pivot_3 4 1 0
cert_heightProof 3
cert_coverFacet 0 342
cert_cover_5 0 0 0 1 3 5 22 342 3
cert_coverFacet 1 794
cert_cover_5 1 2 0 2 3 7 26 794 3
cert_coverFacet 2 172
cert_cover_2 2 2 1 4 6 44 172 3
cert_coverFacet 3 372
cert_cover_5 3 0 1 3 4 5 52 372 3
cert_coverFacet 4 228
cert_cover_2 4 4 1 5 6 100 228 3
cert_coverFacet 5 696
cert_cover_5 5 1 2 3 4 6 56 696 3
cert_coverFacet 6 944
cert_cover_5 6 1 3 4 6 7 688 944 3
cert_coverFacet 7 480
cert_cover_2 7 5 4 6 7 224 480 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 3 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0563

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_one_six_0564.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0564

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 141, 905, 961, 278, 326, 794, 172, 372, 740, 696, 880, 7, 11, 67, 13, 133, 137, 265, 193, 321, 897, 22, 70, 262, 26, 266, 274, 322, 44, 140, 52, 276, 100, 164, 196, 324, 56, 536, 168, 648, 776, 368, 560, 784, 608, 672, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_141, vertices_905, vertices_961, vertices_278, vertices_326, vertices_794, vertices_172, vertices_372, vertices_740, vertices_696, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_137, vertices_265, vertices_193, vertices_321, vertices_897, vertices_22, vertices_70, vertices_262, vertices_26, vertices_266, vertices_274, vertices_322, vertices_44, vertices_140, vertices_52, vertices_276, vertices_100, vertices_164, vertices_196, vertices_324, vertices_56, vertices_536, vertices_168, vertices_648, vertices_776, vertices_368, vertices_560, vertices_784, vertices_608, vertices_672, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_141), (false, vertices_905), (false, vertices_961), (true, vertices_262), (true, vertices_274), (true, vertices_276), (true, vertices_100), (true, vertices_164), (true, vertices_324), (true, vertices_536), (true, vertices_168), (true, vertices_368), (true, vertices_560), (true, vertices_784), (true, vertices_608), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 19 21 22 23 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_331) then 15 else
  if p.val = (false, vertices_141) then 0 else
  if p.val = (false, vertices_905) then 24 else
  if p.val = (false, vertices_961) then 25 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_100) then 4 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_324) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_168) then 8 else
  if p.val = (true, vertices_368) then 20 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_608) then 11 else
  if p.val = (true, vertices_672) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_141), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(true, vertices_368), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 7 8 794 26 3
cert_row_2 1 3 4 5 7 368
cert_row_4 2 1 4 5 6 8 740 100 3
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
cert_coverFacet 3 172
cert_cover_2 3 2 1 4 6 44 172 3
cert_coverFacet 4 372
cert_cover_5 4 1 1 3 4 5 52 372 3
cert_coverFacet 5 740
cert_cover_5 5 2 1 4 5 6 100 740 3
cert_coverFacet 6 696
cert_cover_5 6 3 2 3 4 6 56 696 3
cert_coverFacet 7 880
cert_cover_5 7 1 3 4 5 8 368 880 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0564

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_one_six_0565.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0565

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 141, 905, 961, 342, 794, 172, 820, 228, 868, 696, 736, 7, 11, 67, 13, 133, 137, 265, 193, 321, 897, 22, 70, 26, 266, 274, 322, 44, 140, 52, 276, 100, 164, 804, 196, 324, 56, 536, 168, 648, 776, 560, 784, 224, 608, 672, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_141, vertices_905, vertices_961, vertices_342, vertices_794, vertices_172, vertices_820, vertices_228, vertices_868, vertices_696, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_137, vertices_265, vertices_193, vertices_321, vertices_897, vertices_22, vertices_70, vertices_26, vertices_266, vertices_274, vertices_322, vertices_44, vertices_140, vertices_52, vertices_276, vertices_100, vertices_164, vertices_804, vertices_196, vertices_324, vertices_56, vertices_536, vertices_168, vertices_648, vertices_776, vertices_560, vertices_784, vertices_224, vertices_608, vertices_672, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_141), (false, vertices_905), (false, vertices_961), (true, vertices_274), (true, vertices_276), (true, vertices_100), (true, vertices_164), (true, vertices_804), (true, vertices_324), (true, vertices_536), (true, vertices_168), (true, vertices_560), (true, vertices_784), (true, vertices_224), (true, vertices_608), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 20 21 22 23 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_331) then 15 else
  if p.val = (false, vertices_141) then 0 else
  if p.val = (false, vertices_905) then 24 else
  if p.val = (false, vertices_961) then 25 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_804) then 18 else
  if p.val = (true, vertices_324) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_608) then 11 else
  if p.val = (true, vertices_672) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_141), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_804), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 7 342 22 3
cert_row_2 1 1 4 7 8 804
cert_row_4 2 0 2 3 7 8 794 26 3
cert_row_4 3 2 3 4 6 8 696 56 3
cert_rows
cert_pivot_2 5 1 0 2
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 0 0 1 3 5 22 342 3
cert_coverFacet 1 794
cert_cover_5 1 2 0 2 3 7 26 794 3
cert_coverFacet 2 172
cert_cover_2 2 2 1 4 6 44 172 3
cert_coverFacet 3 820
cert_cover_5 3 1 1 3 4 7 52 820 3
cert_coverFacet 4 228
cert_cover_2 4 4 1 5 6 100 228 3
cert_coverFacet 5 868
cert_cover_5 5 1 1 4 5 7 100 868 3
cert_coverFacet 6 696
cert_cover_5 6 3 2 3 4 6 56 696 3
cert_coverFacet 7 736
cert_cover_2 7 5 4 6 8 224 736 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0565

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_one_six_0566.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0566

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 597, 537, 841, 270, 390, 962, 428, 244, 824, 752, 928, 7, 11, 67, 21, 69, 25, 329, 521, 529, 577, 14, 134, 262, 266, 194, 322, 386, 44, 268, 52, 84, 164, 196, 388, 56, 536, 296, 776, 240, 560, 592, 416, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_597, vertices_537, vertices_841, vertices_270, vertices_390, vertices_962, vertices_428, vertices_244, vertices_824, vertices_752, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_25, vertices_329, vertices_521, vertices_529, vertices_577, vertices_14, vertices_134, vertices_262, vertices_266, vertices_194, vertices_322, vertices_386, vertices_44, vertices_268, vertices_52, vertices_84, vertices_164, vertices_196, vertices_388, vertices_56, vertices_536, vertices_296, vertices_776, vertices_240, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_597), (false, vertices_537), (false, vertices_841), (true, vertices_262), (true, vertices_386), (true, vertices_268), (true, vertices_164), (true, vertices_388), (true, vertices_296), (true, vertices_240), (true, vertices_560), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_331) then 19 else
  if p.val = (false, vertices_597) then 17 else
  if p.val = (false, vertices_537) then 0 else
  if p.val = (false, vertices_841) then 20 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_388) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_240) then 22 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_537), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
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
cert_row_4 0 0 5 6 7 8 962 194 3
cert_row_2 1 3 4 5 6 240
cert_row_4 2 1 2 4 6 7 428 44 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 390
cert_cover_2 1 1 0 6 7 134 390 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 194 962 3
cert_coverFacet 3 428
cert_cover_5 3 2 1 2 4 6 44 428 3
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0566

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_one_six_0567.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0567

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 597, 537, 841, 142, 394, 962, 428, 244, 824, 752, 928, 7, 11, 67, 21, 69, 25, 329, 521, 529, 577, 14, 134, 138, 266, 194, 322, 386, 44, 140, 52, 84, 164, 196, 56, 536, 296, 392, 776, 240, 560, 592, 416, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_597, vertices_537, vertices_841, vertices_142, vertices_394, vertices_962, vertices_428, vertices_244, vertices_824, vertices_752, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_25, vertices_329, vertices_521, vertices_529, vertices_577, vertices_14, vertices_134, vertices_138, vertices_266, vertices_194, vertices_322, vertices_386, vertices_44, vertices_140, vertices_52, vertices_84, vertices_164, vertices_196, vertices_56, vertices_536, vertices_296, vertices_392, vertices_776, vertices_240, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_597), (false, vertices_537), (false, vertices_841), (true, vertices_138), (true, vertices_386), (true, vertices_140), (true, vertices_164), (true, vertices_296), (true, vertices_392), (true, vertices_240), (true, vertices_560), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_331) then 19 else
  if p.val = (false, vertices_597) then 17 else
  if p.val = (false, vertices_537) then 0 else
  if p.val = (false, vertices_841) then 20 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_296) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_240) then 22 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_416) then 8 else
  if p.val = (true, vertices_672) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_704) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_537), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
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
cert_row_4 0 0 5 6 7 8 962 194 3
cert_row_2 1 3 4 5 6 240
cert_row_4 2 1 2 4 6 7 428 44 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 394
cert_cover_2 1 2 0 6 7 138 394 3
cert_coverFacet 2 962
cert_cover_5 2 0 0 5 6 7 194 962 3
cert_coverFacet 3 428
cert_cover_5 3 2 1 2 4 6 44 428 3
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0567

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_one_six_0568.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0568

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 397, 961, 598, 538, 842, 172, 244, 824, 424, 752, 928, 7, 11, 67, 13, 133, 265, 193, 321, 385, 22, 70, 26, 330, 522, 530, 578, 44, 140, 52, 84, 164, 196, 56, 536, 168, 296, 392, 776, 240, 560, 592, 416, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_397, vertices_961, vertices_598, vertices_538, vertices_842, vertices_172, vertices_244, vertices_824, vertices_424, vertices_752, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_330, vertices_522, vertices_530, vertices_578, vertices_44, vertices_140, vertices_52, vertices_84, vertices_164, vertices_196, vertices_56, vertices_536, vertices_168, vertices_296, vertices_392, vertices_776, vertices_240, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_397), (false, vertices_961), (true, vertices_522), (true, vertices_530), (true, vertices_578), (true, vertices_84), (true, vertices_164), (true, vertices_536), (true, vertices_168), (true, vertices_296), (true, vertices_776), (true, vertices_240), (true, vertices_560), (true, vertices_592), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
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
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_168) then 6 else
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
cert_nodeAtPriority_46 522 530 578 84 164 536 168 296 776 560 592 416 672 800 199 331 397 240
cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 5 6 240
cert_row_4 1 0 1 3 5 8 598 22 3
cert_row_2 2 0 2 5 7 330
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 6 1 0 2
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 1 0 1 3 5 22 598 3
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 842
cert_cover_5 2 2 0 2 5 8 330 842 3
cert_coverFacet 3 172
cert_cover_2 3 2 1 4 6 44 172 3
cert_coverFacet 4 244
cert_cover_5 4 0 1 3 4 5 52 244 3
cert_coverFacet 5 824
cert_cover_5 5 3 2 3 4 7 56 824 3
cert_coverFacet 6 424
cert_cover_2 6 4 2 6 7 168 424 3
cert_coverFacet 7 752
cert_cover_5 7 0 3 4 5 8 240 752 3
cert_coverFacet 8 928
cert_cover_2 8 6 4 7 8 416 928 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0568

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_one_six_0569.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0569

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 397, 961, 86, 538, 842, 594, 300, 244, 932, 824, 752, 7, 11, 67, 13, 133, 265, 193, 321, 385, 22, 70, 26, 330, 522, 82, 530, 578, 44, 268, 52, 84, 164, 292, 196, 388, 56, 536, 296, 776, 240, 560, 592, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_397, vertices_961, vertices_86, vertices_538, vertices_842, vertices_594, vertices_300, vertices_244, vertices_932, vertices_824, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_330, vertices_522, vertices_82, vertices_530, vertices_578, vertices_44, vertices_268, vertices_52, vertices_84, vertices_164, vertices_292, vertices_196, vertices_388, vertices_56, vertices_536, vertices_296, vertices_776, vertices_240, vertices_560, vertices_592, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_397), (false, vertices_961), (true, vertices_522), (true, vertices_82), (true, vertices_530), (true, vertices_578), (true, vertices_84), (true, vertices_164), (true, vertices_292), (true, vertices_536), (true, vertices_296), (true, vertices_776), (true, vertices_240), (true, vertices_560), (true, vertices_592), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 21 23 24 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 18 else
  if p.val = (false, vertices_199) then 15 else
  if p.val = (false, vertices_331) then 16 else
  if p.val = (false, vertices_397) then 19 else
  if p.val = (false, vertices_961) then 25 else
  if p.val = (true, vertices_522) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_776) then 9 else
  if p.val = (true, vertices_240) then 22 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_672) then 12 else
  if p.val = (true, vertices_800) then 13 else
  0
cert_priority
cert_nodeAtPriority_46 522 82 530 578 84 164 292 536 296 776 560 592 672 800 199 331 397 240
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 7 330
cert_row_2 1 3 4 5 6 240
cert_row_4 2 1 4 6 7 8 932 164 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 842
cert_cover_5 2 0 0 2 5 8 330 842 3
cert_coverFacet 3 594
cert_cover_2 3 3 0 5 8 82 594 3
cert_coverFacet 4 300
cert_cover_2 4 2 1 4 7 44 300 3
cert_coverFacet 5 244
cert_cover_5 5 1 1 3 4 5 52 244 3
cert_coverFacet 6 932
cert_cover_5 6 2 1 4 6 7 164 932 3
cert_coverFacet 7 824
cert_cover_5 7 3 2 3 4 7 56 824 3
cert_coverFacet 8 752
cert_cover_5 8 1 3 4 5 8 240 752 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0569

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_one_six_0570.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0570

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 331, 397, 961, 598, 538, 842, 300, 244, 420, 824, 752, 928, 7, 11, 67, 13, 133, 265, 193, 321, 385, 22, 70, 26, 330, 522, 530, 578, 44, 268, 52, 84, 164, 292, 196, 388, 56, 536, 296, 776, 240, 560, 592, 416, 672, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_331, vertices_397, vertices_961, vertices_598, vertices_538, vertices_842, vertices_300, vertices_244, vertices_420, vertices_824, vertices_752, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_13, vertices_133, vertices_265, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_26, vertices_330, vertices_522, vertices_530, vertices_578, vertices_44, vertices_268, vertices_52, vertices_84, vertices_164, vertices_292, vertices_196, vertices_388, vertices_56, vertices_536, vertices_296, vertices_776, vertices_240, vertices_560, vertices_592, vertices_416, vertices_672, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_331), (false, vertices_397), (false, vertices_961), (true, vertices_522), (true, vertices_530), (true, vertices_578), (true, vertices_84), (true, vertices_164), (true, vertices_292), (true, vertices_536), (true, vertices_296), (true, vertices_776), (true, vertices_240), (true, vertices_560), (true, vertices_592), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
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
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_292) then 5 else
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
cert_nodeAtPriority_46 522 530 578 84 164 292 536 296 776 560 592 416 672 800 199 331 397 240
cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 5 6 240
cert_row_4 1 0 1 3 5 8 598 22 3
cert_row_2 2 0 2 5 7 330
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 6 1 0 2
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 1 0 1 3 5 22 598 3
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 842
cert_cover_5 2 2 0 2 5 8 330 842 3
cert_coverFacet 3 300
cert_cover_2 3 2 1 4 7 44 300 3
cert_coverFacet 4 244
cert_cover_5 4 0 1 3 4 5 52 244 3
cert_coverFacet 5 420
cert_cover_2 5 4 1 6 7 164 420 3
cert_coverFacet 6 824
cert_cover_5 6 3 2 3 4 7 56 824 3
cert_coverFacet 7 752
cert_cover_5 7 0 3 4 5 8 240 752 3
cert_coverFacet 8 928
cert_cover_2 8 6 4 7 8 416 928 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0570

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_one_six_0573.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0573

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 835, 653, 705, 86, 346, 556, 244, 932, 824, 496, 960, 7, 11, 67, 771, 13, 133, 521, 193, 577, 641, 22, 70, 26, 266, 82, 322, 44, 524, 52, 84, 164, 548, 196, 644, 56, 280, 552, 776, 240, 304, 336, 416, 800, 448, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_835, vertices_653, vertices_705, vertices_86, vertices_346, vertices_556, vertices_244, vertices_932, vertices_824, vertices_496, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_771, vertices_13, vertices_133, vertices_521, vertices_193, vertices_577, vertices_641, vertices_22, vertices_70, vertices_26, vertices_266, vertices_82, vertices_322, vertices_44, vertices_524, vertices_52, vertices_84, vertices_164, vertices_548, vertices_196, vertices_644, vertices_56, vertices_280, vertices_552, vertices_776, vertices_240, vertices_304, vertices_336, vertices_416, vertices_800, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_835), (false, vertices_653), (false, vertices_705), (true, vertices_82), (true, vertices_84), (true, vertices_164), (true, vertices_548), (true, vertices_280), (true, vertices_552), (true, vertices_240), (true, vertices_304), (true, vertices_336), (true, vertices_416), (true, vertices_800), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 13 20 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_835) then 19 else
  if p.val = (false, vertices_653) then 15 else
  if p.val = (false, vertices_705) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_240) then 22 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_416) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_448) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_705), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 20 => Sum.inl 2
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
cert_row_4 0 0 2 3 5 7 346 26 3
cert_row_2 1 3 4 5 6 240
cert_row_4 2 1 4 6 7 8 932 164 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 346
cert_cover_5 1 0 0 2 3 5 26 346 3
cert_coverFacet 2 556
cert_cover_2 2 2 1 4 8 44 556 3
cert_coverFacet 3 244
cert_cover_5 3 1 1 3 4 5 52 244 3
cert_coverFacet 4 932
cert_cover_5 4 2 1 4 6 7 164 932 3
cert_coverFacet 5 824
cert_cover_5 5 3 2 3 4 7 56 824 3
cert_coverFacet 6 496
cert_cover_5 6 1 3 4 5 7 240 496 3
cert_coverFacet 7 960
cert_cover_2 7 6 5 7 8 448 960 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0573

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_one_six_0574.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0574

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 899, 589, 705, 86, 282, 466, 812, 628, 440, 752, 928, 7, 11, 131, 771, 13, 69, 521, 193, 577, 641, 22, 70, 26, 266, 82, 274, 194, 386, 44, 524, 52, 84, 548, 580, 56, 280, 296, 776, 624, 176, 208, 400, 416, 672, 800, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_899, vertices_589, vertices_705, vertices_86, vertices_282, vertices_466, vertices_812, vertices_628, vertices_440, vertices_752, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_771, vertices_13, vertices_69, vertices_521, vertices_193, vertices_577, vertices_641, vertices_22, vertices_70, vertices_26, vertices_266, vertices_82, vertices_274, vertices_194, vertices_386, vertices_44, vertices_524, vertices_52, vertices_84, vertices_548, vertices_580, vertices_56, vertices_280, vertices_296, vertices_776, vertices_624, vertices_176, vertices_208, vertices_400, vertices_416, vertices_672, vertices_800, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_899), (false, vertices_589), (false, vertices_705), (true, vertices_82), (true, vertices_274), (true, vertices_84), (true, vertices_548), (true, vertices_280), (true, vertices_296), (true, vertices_624), (true, vertices_176), (true, vertices_208), (true, vertices_400), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 13 20 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_899) then 19 else
  if p.val = (false, vertices_589) then 15 else
  if p.val = (false, vertices_705) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_624) then 22 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_416) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_705), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 20 => Sum.inl 2
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
cert_row_4 0 0 3 5 6 7 466 82 3
cert_row_2 1 3 4 5 8 624
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 2 3 4 6 7 440 56 3
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 86
cert_cover_2 0 1 0 3 5 22 86 3
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 466
cert_cover_5 2 0 0 3 5 6 82 466 3
cert_coverFacet 3 812
cert_cover_5 3 2 1 2 4 7 44 812 3
cert_coverFacet 4 628
cert_cover_5 4 1 1 3 4 5 52 628 3
cert_coverFacet 5 440
cert_cover_5 5 3 2 3 4 6 56 440 3
cert_coverFacet 6 752
cert_cover_5 6 1 3 4 5 6 624 752 3
cert_coverFacet 7 928
cert_cover_2 7 6 4 7 8 416 928 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0574

end
end BundlePart10

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_4715 : Certifies 4715 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0562.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4716 : Certifies 4716 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0563.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4717 : Certifies 4717 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0564.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4718 : Certifies 4718 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0565.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4719 : Certifies 4719 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0566.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4720 : Certifies 4720 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0567.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4721 : Certifies 4721 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0568.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4722 : Certifies 4722 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0569.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4723 : Certifies 4723 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0570.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4724 : Certifies 4724 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0573.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_4725 : Certifies 4725 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_0574.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B156 (j : Fin 11) :
    Certifies (4715 + j.val) := by
  fin_cases j
  · exact projection_4715
  · exact projection_4716
  · exact projection_4717
  · exact projection_4718
  · exact projection_4719
  · exact projection_4720
  · exact projection_4721
  · exact projection_4722
  · exact projection_4723
  · exact projection_4724
  · exact projection_4725

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
