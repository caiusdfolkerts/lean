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
/- Source: ProjectionCertificates/R_one_six_1783.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1783

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 643, 93, 457, 897, 678, 554, 372, 484, 568, 856, 944, 7, 11, 131, 515, 29, 69, 73, 265, 193, 385, 641, 769, 38, 134, 42, 522, 546, 642, 52, 84, 356, 164, 196, 56, 88, 536, 552, 328, 776, 304, 560, 336, 784, 416, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_643, vertices_93, vertices_457, vertices_897, vertices_678, vertices_554, vertices_372, vertices_484, vertices_568, vertices_856, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_515, vertices_29, vertices_69, vertices_73, vertices_265, vertices_193, vertices_385, vertices_641, vertices_769, vertices_38, vertices_134, vertices_42, vertices_522, vertices_546, vertices_642, vertices_52, vertices_84, vertices_356, vertices_164, vertices_196, vertices_56, vertices_88, vertices_536, vertices_552, vertices_328, vertices_776, vertices_304, vertices_560, vertices_336, vertices_784, vertices_416, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_643), (false, vertices_93), (false, vertices_457), (false, vertices_897), (true, vertices_546), (true, vertices_356), (true, vertices_164), (true, vertices_536), (true, vertices_552), (true, vertices_304), (true, vertices_560), (true, vertices_336), (true, vertices_784), (true, vertices_416), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_93) then 17 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (false, vertices_897) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_356) then 18 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_416) then 10 else
  if p.val = (true, vertices_672) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_356), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1783

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_one_six_1784.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1784

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 643, 93, 457, 897, 678, 554, 820, 724, 376, 808, 976, 7, 11, 131, 515, 29, 69, 73, 265, 193, 385, 641, 769, 38, 134, 42, 522, 546, 642, 52, 84, 532, 548, 196, 644, 56, 88, 296, 552, 328, 776, 304, 720, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_643, vertices_93, vertices_457, vertices_897, vertices_678, vertices_554, vertices_820, vertices_724, vertices_376, vertices_808, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_515, vertices_29, vertices_69, vertices_73, vertices_265, vertices_193, vertices_385, vertices_641, vertices_769, vertices_38, vertices_134, vertices_42, vertices_522, vertices_546, vertices_642, vertices_52, vertices_84, vertices_532, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_296, vertices_552, vertices_328, vertices_776, vertices_304, vertices_720, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_643), (false, vertices_93), (false, vertices_457), (false, vertices_897), (true, vertices_546), (true, vertices_532), (true, vertices_548), (true, vertices_644), (true, vertices_296), (true, vertices_552), (true, vertices_304), (true, vertices_720), (true, vertices_336), (true, vertices_784), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_93) then 17 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (false, vertices_897) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_720) then 21 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(true, vertices_720), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1784

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_one_six_1785.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1785

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 643, 93, 457, 897, 678, 298, 802, 820, 724, 376, 976, 7, 11, 131, 515, 29, 69, 73, 265, 193, 385, 641, 769, 38, 134, 42, 266, 290, 546, 642, 770, 52, 84, 532, 548, 196, 644, 56, 88, 296, 328, 304, 720, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_643, vertices_93, vertices_457, vertices_897, vertices_678, vertices_298, vertices_802, vertices_820, vertices_724, vertices_376, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_515, vertices_29, vertices_69, vertices_73, vertices_265, vertices_193, vertices_385, vertices_641, vertices_769, vertices_38, vertices_134, vertices_42, vertices_266, vertices_290, vertices_546, vertices_642, vertices_770, vertices_52, vertices_84, vertices_532, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_296, vertices_328, vertices_304, vertices_720, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_643), (false, vertices_93), (false, vertices_457), (false, vertices_897), (true, vertices_290), (true, vertices_546), (true, vertices_532), (true, vertices_548), (true, vertices_644), (true, vertices_296), (true, vertices_304), (true, vertices_720), (true, vertices_336), (true, vertices_784), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_93) then 17 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (false, vertices_897) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_720) then 21 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(true, vertices_720), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
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
cert_coverFacet 1 298
cert_cover_2 1 2 0 4 7 42 298 3
cert_coverFacet 2 802
cert_cover_2 2 4 0 7 8 290 802 3
cert_coverFacet 3 820
cert_cover_5 3 2 1 3 4 7 52 820 3
cert_coverFacet 4 724
cert_cover_5 4 1 1 3 5 6 84 724 3
cert_coverFacet 5 376
cert_cover_5 5 3 2 3 4 5 56 376 3
cert_coverFacet 6 976
cert_cover_5 6 1 3 5 6 7 720 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1785

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_one_six_1786.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1786

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 267, 899, 93, 457, 166, 810, 674, 820, 724, 676, 376, 976, 7, 11, 131, 259, 29, 69, 73, 265, 193, 385, 38, 134, 42, 266, 162, 546, 642, 770, 52, 84, 532, 164, 548, 196, 644, 56, 88, 296, 328, 304, 720, 336, 784, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_267, vertices_899, vertices_93, vertices_457, vertices_166, vertices_810, vertices_674, vertices_820, vertices_724, vertices_676, vertices_376, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_29, vertices_69, vertices_73, vertices_265, vertices_193, vertices_385, vertices_38, vertices_134, vertices_42, vertices_266, vertices_162, vertices_546, vertices_642, vertices_770, vertices_52, vertices_84, vertices_532, vertices_164, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_296, vertices_328, vertices_304, vertices_720, vertices_336, vertices_784, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_267), (false, vertices_899), (false, vertices_93), (false, vertices_457), (true, vertices_162), (true, vertices_546), (true, vertices_532), (true, vertices_164), (true, vertices_548), (true, vertices_644), (true, vertices_296), (true, vertices_304), (true, vertices_720), (true, vertices_336), (true, vertices_784), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_899) then 15 else
  if p.val = (false, vertices_93) then 18 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_720) then 22 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 21 => Sum.inl 3
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
cert_row_4 1 0 2 4 7 8 810 42 3
cert_row_4 2 1 3 4 7 8 820 52 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 6 0 1 2
cert_heightProof 4
cert_coverFacet 0 166
cert_cover_2 0 1 0 4 6 38 166 3
cert_coverFacet 1 810
cert_cover_5 1 1 0 2 4 7 42 810 3
cert_coverFacet 2 674
cert_cover_2 2 4 0 6 8 162 674 3
cert_coverFacet 3 820
cert_cover_5 3 2 1 3 4 7 52 820 3
cert_coverFacet 4 724
cert_cover_5 4 0 1 3 5 6 84 724 3
cert_coverFacet 5 676
cert_cover_2 5 4 1 6 8 164 676 3
cert_coverFacet 6 376
cert_cover_5 6 3 2 3 4 5 56 376 3
cert_coverFacet 7 976
cert_cover_5 7 0 3 5 6 7 720 976 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1786

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_one_six_1787.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1787

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 267, 899, 93, 457, 166, 810, 674, 692, 852, 964, 376, 816, 7, 11, 131, 259, 29, 69, 73, 265, 193, 385, 38, 134, 42, 266, 162, 546, 642, 770, 52, 84, 532, 164, 196, 836, 644, 56, 88, 296, 328, 304, 560, 336, 784, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_267, vertices_899, vertices_93, vertices_457, vertices_166, vertices_810, vertices_674, vertices_692, vertices_852, vertices_964, vertices_376, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_29, vertices_69, vertices_73, vertices_265, vertices_193, vertices_385, vertices_38, vertices_134, vertices_42, vertices_266, vertices_162, vertices_546, vertices_642, vertices_770, vertices_52, vertices_84, vertices_532, vertices_164, vertices_196, vertices_836, vertices_644, vertices_56, vertices_88, vertices_296, vertices_328, vertices_304, vertices_560, vertices_336, vertices_784, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_267), (false, vertices_899), (false, vertices_93), (false, vertices_457), (true, vertices_162), (true, vertices_546), (true, vertices_532), (true, vertices_164), (true, vertices_836), (true, vertices_644), (true, vertices_296), (true, vertices_304), (true, vertices_560), (true, vertices_336), (true, vertices_784), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_899) then 15 else
  if p.val = (false, vertices_93) then 18 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_836) then 19 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
cert_nodeAtPriority_28 0 267 1 162 546 532 164 644 296 304 560 336 784 672 800 199 899 93 836 457
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 7 8 810 42 3
cert_row_4 1 1 3 4 6 8 692 52 3
cert_row_2 2 1 5 7 8 836
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 166
cert_cover_2 0 1 0 4 6 38 166 3
cert_coverFacet 1 810
cert_cover_5 1 0 0 2 4 7 42 810 3
cert_coverFacet 2 674
cert_cover_2 2 4 0 6 8 162 674 3
cert_coverFacet 3 692
cert_cover_5 3 1 1 3 4 6 52 692 3
cert_coverFacet 4 852
cert_cover_5 4 2 1 3 5 7 84 852 3
cert_coverFacet 5 964
cert_cover_5 5 2 1 5 6 7 196 964 3
cert_coverFacet 6 376
cert_cover_5 6 3 2 3 4 5 56 376 3
cert_coverFacet 7 816
cert_cover_2 7 4 3 7 8 304 816 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1787

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_one_six_1788.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1788

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 267, 899, 93, 457, 678, 554, 778, 372, 484, 568, 856, 944, 7, 11, 131, 259, 29, 69, 73, 265, 193, 385, 38, 134, 42, 266, 522, 546, 642, 770, 52, 84, 356, 164, 196, 56, 88, 536, 552, 328, 776, 304, 560, 336, 784, 416, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_267, vertices_899, vertices_93, vertices_457, vertices_678, vertices_554, vertices_778, vertices_372, vertices_484, vertices_568, vertices_856, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_29, vertices_69, vertices_73, vertices_265, vertices_193, vertices_385, vertices_38, vertices_134, vertices_42, vertices_266, vertices_522, vertices_546, vertices_642, vertices_770, vertices_52, vertices_84, vertices_356, vertices_164, vertices_196, vertices_56, vertices_88, vertices_536, vertices_552, vertices_328, vertices_776, vertices_304, vertices_560, vertices_336, vertices_784, vertices_416, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_267), (false, vertices_899), (false, vertices_93), (false, vertices_457), (true, vertices_522), (true, vertices_546), (true, vertices_356), (true, vertices_164), (true, vertices_536), (true, vertices_552), (true, vertices_776), (true, vertices_304), (true, vertices_560), (true, vertices_336), (true, vertices_784), (true, vertices_416), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_899) then 15 else
  if p.val = (false, vertices_93) then 18 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_356) then 19 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_416) then 11 else
  if p.val = (true, vertices_672) then 12 else
  0
cert_priority
cert_nodeAtPriority_28 0 267 1 522 546 164 536 552 776 304 560 336 784 416 672 199 899 93 356 457
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
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 372
cert_cover_5 3 1 1 3 4 5 52 372 3
cert_coverFacet 4 484
cert_cover_5 4 1 1 4 5 6 356 484 3
cert_coverFacet 5 568
cert_cover_2 5 3 2 4 8 56 568 3
cert_coverFacet 6 856
cert_cover_5 6 2 2 3 5 7 88 856 3
cert_coverFacet 7 944
cert_cover_5 7 3 3 4 6 7 304 944 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1788

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_one_six_1789.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1789

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 267, 899, 93, 457, 678, 554, 778, 820, 724, 376, 808, 976, 7, 11, 131, 259, 29, 69, 73, 265, 193, 385, 38, 134, 42, 266, 522, 546, 642, 770, 52, 84, 532, 548, 196, 644, 56, 88, 296, 552, 328, 776, 304, 720, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_267, vertices_899, vertices_93, vertices_457, vertices_678, vertices_554, vertices_778, vertices_820, vertices_724, vertices_376, vertices_808, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_29, vertices_69, vertices_73, vertices_265, vertices_193, vertices_385, vertices_38, vertices_134, vertices_42, vertices_266, vertices_522, vertices_546, vertices_642, vertices_770, vertices_52, vertices_84, vertices_532, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_296, vertices_552, vertices_328, vertices_776, vertices_304, vertices_720, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_267), (false, vertices_899), (false, vertices_93), (false, vertices_457), (true, vertices_522), (true, vertices_546), (true, vertices_532), (true, vertices_548), (true, vertices_644), (true, vertices_296), (true, vertices_552), (true, vertices_776), (true, vertices_304), (true, vertices_720), (true, vertices_336), (true, vertices_784), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_899) then 15 else
  if p.val = (false, vertices_93) then 18 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_720) then 22 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(true, vertices_720), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
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
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 820
cert_cover_5 3 2 1 3 4 7 52 820 3
cert_coverFacet 4 724
cert_cover_5 4 1 1 3 5 6 84 724 3
cert_coverFacet 5 376
cert_cover_5 5 3 2 3 4 5 56 376 3
cert_coverFacet 6 808
cert_cover_2 6 4 2 7 8 296 808 3
cert_coverFacet 7 976
cert_cover_5 7 1 3 5 6 7 720 976 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1789

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_one_six_1790.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1790

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 267, 899, 93, 457, 678, 810, 308, 724, 788, 804, 376, 976, 7, 11, 131, 259, 29, 69, 73, 265, 193, 385, 38, 134, 42, 266, 546, 642, 770, 52, 84, 276, 532, 292, 548, 196, 644, 772, 56, 88, 296, 328, 304, 720, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_267, vertices_899, vertices_93, vertices_457, vertices_678, vertices_810, vertices_308, vertices_724, vertices_788, vertices_804, vertices_376, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_259, vertices_29, vertices_69, vertices_73, vertices_265, vertices_193, vertices_385, vertices_38, vertices_134, vertices_42, vertices_266, vertices_546, vertices_642, vertices_770, vertices_52, vertices_84, vertices_276, vertices_532, vertices_292, vertices_548, vertices_196, vertices_644, vertices_772, vertices_56, vertices_88, vertices_296, vertices_328, vertices_304, vertices_720, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_267), (false, vertices_899), (false, vertices_93), (false, vertices_457), (true, vertices_546), (true, vertices_276), (true, vertices_532), (true, vertices_292), (true, vertices_548), (true, vertices_644), (true, vertices_772), (true, vertices_296), (true, vertices_304), (true, vertices_720), (true, vertices_336), (true, vertices_784), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_899) then 15 else
  if p.val = (false, vertices_93) then 18 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (true, vertices_546) then 1 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_720) then 22 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_267), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(true, vertices_720), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 38 3
cert_row_2 1 3 5 6 8 720
cert_row_4 2 0 2 4 7 8 810 42 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 38 678 3
cert_coverFacet 1 810
cert_cover_5 1 2 0 2 4 7 42 810 3
cert_coverFacet 2 308
cert_cover_2 2 3 1 4 7 52 308 3
cert_coverFacet 3 724
cert_cover_5 3 1 1 3 5 6 84 724 3
cert_coverFacet 4 788
cert_cover_2 4 3 1 7 8 276 788 3
cert_coverFacet 5 804
cert_cover_2 5 4 1 7 8 292 804 3
cert_coverFacet 6 376
cert_cover_5 6 3 2 3 4 5 56 376 3
cert_coverFacet 7 976
cert_cover_5 7 1 3 5 6 7 720 976 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1790

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_one_six_1791.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1791

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 523, 899, 93, 457, 777, 678, 554, 372, 484, 568, 856, 944, 7, 11, 131, 515, 29, 69, 73, 265, 521, 193, 385, 769, 38, 134, 42, 522, 546, 642, 52, 84, 356, 164, 196, 56, 88, 536, 552, 328, 776, 304, 560, 336, 784, 416, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_523, vertices_899, vertices_93, vertices_457, vertices_777, vertices_678, vertices_554, vertices_372, vertices_484, vertices_568, vertices_856, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_515, vertices_29, vertices_69, vertices_73, vertices_265, vertices_521, vertices_193, vertices_385, vertices_769, vertices_38, vertices_134, vertices_42, vertices_522, vertices_546, vertices_642, vertices_52, vertices_84, vertices_356, vertices_164, vertices_196, vertices_56, vertices_88, vertices_536, vertices_552, vertices_328, vertices_776, vertices_304, vertices_560, vertices_336, vertices_784, vertices_416, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_523), (false, vertices_899), (false, vertices_93), (false, vertices_457), (false, vertices_777), (true, vertices_546), (true, vertices_356), (true, vertices_164), (true, vertices_536), (true, vertices_552), (true, vertices_304), (true, vertices_560), (true, vertices_336), (true, vertices_784), (true, vertices_416), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_523) then 0 else
  if p.val = (false, vertices_899) then 14 else
  if p.val = (false, vertices_93) then 17 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (false, vertices_777) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_356) then 18 else
  if p.val = (true, vertices_164) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_416) then 10 else
  if p.val = (true, vertices_672) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_523), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_356), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1791

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_one_six_1792.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1792

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 523, 899, 93, 457, 777, 678, 554, 820, 724, 376, 808, 976, 7, 11, 131, 515, 29, 69, 73, 265, 521, 193, 385, 769, 38, 134, 42, 522, 546, 642, 52, 84, 532, 548, 196, 644, 56, 88, 296, 552, 328, 776, 304, 720, 336, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_523, vertices_899, vertices_93, vertices_457, vertices_777, vertices_678, vertices_554, vertices_820, vertices_724, vertices_376, vertices_808, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_515, vertices_29, vertices_69, vertices_73, vertices_265, vertices_521, vertices_193, vertices_385, vertices_769, vertices_38, vertices_134, vertices_42, vertices_522, vertices_546, vertices_642, vertices_52, vertices_84, vertices_532, vertices_548, vertices_196, vertices_644, vertices_56, vertices_88, vertices_296, vertices_552, vertices_328, vertices_776, vertices_304, vertices_720, vertices_336, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_523), (false, vertices_899), (false, vertices_93), (false, vertices_457), (false, vertices_777), (true, vertices_546), (true, vertices_532), (true, vertices_548), (true, vertices_644), (true, vertices_296), (true, vertices_552), (true, vertices_304), (true, vertices_720), (true, vertices_336), (true, vertices_784), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 16 else
  if p.val = (false, vertices_199) then 13 else
  if p.val = (false, vertices_523) then 0 else
  if p.val = (false, vertices_899) then 14 else
  if p.val = (false, vertices_93) then 17 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (false, vertices_777) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_720) then 21 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_800) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_523), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(true, vertices_720), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
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
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1792

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_one_six_1793.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1793

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 899, 93, 457, 678, 554, 372, 228, 568, 856, 944, 480, 7, 11, 131, 771, 29, 69, 73, 265, 193, 385, 38, 134, 42, 522, 546, 642, 52, 84, 100, 164, 196, 56, 88, 536, 552, 328, 776, 304, 560, 336, 784, 224, 352, 416, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_899, vertices_93, vertices_457, vertices_678, vertices_554, vertices_372, vertices_228, vertices_568, vertices_856, vertices_944, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_771, vertices_29, vertices_69, vertices_73, vertices_265, vertices_193, vertices_385, vertices_38, vertices_134, vertices_42, vertices_522, vertices_546, vertices_642, vertices_52, vertices_84, vertices_100, vertices_164, vertices_196, vertices_56, vertices_88, vertices_536, vertices_552, vertices_328, vertices_776, vertices_304, vertices_560, vertices_336, vertices_784, vertices_224, vertices_352, vertices_416, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_899), (false, vertices_93), (false, vertices_457), (true, vertices_546), (true, vertices_100), (true, vertices_164), (true, vertices_536), (true, vertices_552), (true, vertices_304), (true, vertices_560), (true, vertices_336), (true, vertices_784), (true, vertices_224), (true, vertices_352), (true, vertices_416), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 13 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_899) then 19 else
  if p.val = (false, vertices_93) then 15 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (true, vertices_546) then 0 else
  if p.val = (true, vertices_100) then 1 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_536) then 3 else
  if p.val = (true, vertices_552) then 4 else
  if p.val = (true, vertices_304) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_336) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_352) then 10 else
  if p.val = (true, vertices_416) then 11 else
  if p.val = (true, vertices_672) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 38 3
cert_row_4 1 1 3 4 5 7 372 52 3
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
cert_coverFacet 3 228
cert_cover_2 3 4 1 5 6 100 228 3
cert_coverFacet 4 568
cert_cover_2 4 3 2 4 8 56 568 3
cert_coverFacet 5 856
cert_cover_5 5 2 2 3 5 7 88 856 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 304 944 2
cert_coverFacet 7 480
cert_cover_2 7 5 4 6 7 224 480 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1793

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_one_six_1794.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1794

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 779, 899, 93, 457, 678, 554, 372, 420, 452, 568, 856, 944, 7, 11, 131, 771, 29, 69, 73, 265, 193, 385, 38, 134, 42, 522, 546, 642, 52, 84, 164, 292, 196, 324, 388, 56, 88, 536, 552, 328, 776, 304, 560, 336, 784, 416, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_779, vertices_899, vertices_93, vertices_457, vertices_678, vertices_554, vertices_372, vertices_420, vertices_452, vertices_568, vertices_856, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_131, vertices_771, vertices_29, vertices_69, vertices_73, vertices_265, vertices_193, vertices_385, vertices_38, vertices_134, vertices_42, vertices_522, vertices_546, vertices_642, vertices_52, vertices_84, vertices_164, vertices_292, vertices_196, vertices_324, vertices_388, vertices_56, vertices_88, vertices_536, vertices_552, vertices_328, vertices_776, vertices_304, vertices_560, vertices_336, vertices_784, vertices_416, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_779), (false, vertices_899), (false, vertices_93), (false, vertices_457), (true, vertices_546), (true, vertices_164), (true, vertices_292), (true, vertices_324), (true, vertices_388), (true, vertices_536), (true, vertices_552), (true, vertices_304), (true, vertices_560), (true, vertices_336), (true, vertices_784), (true, vertices_416), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 13 20 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 17 else
  if p.val = (false, vertices_199) then 14 else
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_899) then 19 else
  if p.val = (false, vertices_93) then 15 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (true, vertices_546) then 0 else
  if p.val = (true, vertices_164) then 1 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_324) then 3 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_416) then 11 else
  if p.val = (true, vertices_672) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 38 3
cert_row_4 1 1 3 4 5 7 372 52 3
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
cert_coverFacet 3 420
cert_cover_2 3 4 1 6 7 164 420 3
cert_coverFacet 4 452
cert_cover_2 4 5 1 6 7 196 452 3
cert_coverFacet 5 568
cert_cover_2 5 3 2 4 8 56 568 3
cert_coverFacet 6 856
cert_cover_5 6 2 2 3 5 7 88 856 3
cert_coverFacet 7 944
cert_cover_5 7 3 3 4 6 7 304 944 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1794

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_one_six_1797.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1797

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 211, 805, 433, 78, 198, 602, 620, 964, 824, 976, 7, 19, 131, 37, 261, 49, 145, 289, 385, 14, 70, 134, 26, 74, 82, 194, 44, 76, 548, 196, 580, 388, 772, 56, 536, 552, 584, 304, 208, 592, 400, 784, 800, 960]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_211, vertices_805, vertices_433, vertices_78, vertices_198, vertices_602, vertices_620, vertices_964, vertices_824, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_19, vertices_131, vertices_37, vertices_261, vertices_49, vertices_145, vertices_289, vertices_385, vertices_14, vertices_70, vertices_134, vertices_26, vertices_74, vertices_82, vertices_194, vertices_44, vertices_76, vertices_548, vertices_196, vertices_580, vertices_388, vertices_772, vertices_56, vertices_536, vertices_552, vertices_584, vertices_304, vertices_208, vertices_592, vertices_400, vertices_784, vertices_800, vertices_960] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_211), (false, vertices_805), (false, vertices_433), (true, vertices_70), (true, vertices_74), (true, vertices_76), (true, vertices_196), (true, vertices_580), (true, vertices_536), (true, vertices_552), (true, vertices_584), (true, vertices_592), (true, vertices_784), (true, vertices_960)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 16 17 19 20 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_391) then 11 else
  if p.val = (false, vertices_211) then 12 else
  if p.val = (false, vertices_805) then 15 else
  if p.val = (false, vertices_433) then 18 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_196) then 3 else
  if p.val = (true, vertices_580) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_584) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_784) then 9 else
  if p.val = (true, vertices_960) then 21 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inl 3
  | 18 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
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
cert_row_4 1 0 2 3 5 8 602 26 3
cert_row_4 2 1 2 4 5 8 620 44 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 6 0 1 2
cert_heightProof 4
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 602
cert_cover_5 2 1 0 2 3 5 26 602 3
cert_coverFacet 3 620
cert_cover_5 3 2 1 2 4 5 44 620 3
cert_coverFacet 4 964
cert_cover_5 4 0 1 5 6 7 196 964 3
cert_coverFacet 5 824
cert_cover_5 5 3 2 3 4 7 56 824 3
cert_coverFacet 6 976
cert_cover_5 6 0 3 5 6 7 208 976 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1797

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_one_six_1798.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1798

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 199, 595, 421, 817, 961, 78, 794, 842, 236, 440, 456, 7, 19, 67, 37, 133, 49, 529, 289, 193, 577, 385, 769, 14, 70, 26, 74, 778, 530, 578, 44, 76, 164, 196, 56, 280, 168, 200, 328, 392, 304, 784, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_199, vertices_595, vertices_421, vertices_817, vertices_961, vertices_78, vertices_794, vertices_842, vertices_236, vertices_440, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_19, vertices_67, vertices_37, vertices_133, vertices_49, vertices_529, vertices_289, vertices_193, vertices_577, vertices_385, vertices_769, vertices_14, vertices_70, vertices_26, vertices_74, vertices_778, vertices_530, vertices_578, vertices_44, vertices_76, vertices_164, vertices_196, vertices_56, vertices_280, vertices_168, vertices_200, vertices_328, vertices_392, vertices_304, vertices_784, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_199), (false, vertices_595), (false, vertices_421), (false, vertices_817), (false, vertices_961), (true, vertices_74), (true, vertices_778), (true, vertices_76), (true, vertices_280), (true, vertices_168), (true, vertices_200), (true, vertices_328), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 7 14 15 17 18 20 21 22
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 11 else
  if p.val = (false, vertices_199) then 8 else
  if p.val = (false, vertices_595) then 12 else
  if p.val = (false, vertices_421) then 9 else
  if p.val = (false, vertices_817) then 16 else
  if p.val = (false, vertices_961) then 19 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_778) then 13 else
  if p.val = (true, vertices_76) then 1 else
  if p.val = (true, vertices_280) then 2 else
  if p.val = (true, vertices_168) then 3 else
  if p.val = (true, vertices_200) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_392) then 6 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 7 => Sum.inl 1
  | 8 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 9 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_778), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 17 => Sum.inl 4
  | 18 => Sum.inl 5
  | 19 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 20 => Sum.inl 6
  | 21 => Sum.inl 7
  | 22 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 7 8 778
cert_row_4 1 1 2 4 5 6 236 44 3
cert_row_4 2 2 3 4 6 7 440 56 3
cert_rows_3
cert_pivot_3 1 0 2
cert_heightProof 3
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 794
cert_cover_5 1 0 0 2 3 7 26 794 3
cert_coverFacet 2 842
cert_cover_5 2 0 0 2 5 7 74 842 3
cert_coverFacet 3 236
cert_cover_5 3 1 1 2 4 5 44 236 3
cert_coverFacet 4 440
cert_cover_5 4 2 2 3 4 6 56 440 3
cert_coverFacet 5 456
cert_cover_2 5 5 2 6 7 200 456 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 3 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1798

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_one_six_1799.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1799

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 229, 681, 342, 346, 692, 916, 452, 824, 968, 7, 11, 67, 37, 69, 41, 137, 161, 193, 22, 70, 26, 74, 338, 52, 660, 276, 164, 196, 324, 388, 56, 280, 552, 200, 328, 648, 776, 560, 784, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_229, vertices_681, vertices_342, vertices_346, vertices_692, vertices_916, vertices_452, vertices_824, vertices_968] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_37, vertices_69, vertices_41, vertices_137, vertices_161, vertices_193, vertices_22, vertices_70, vertices_26, vertices_74, vertices_338, vertices_52, vertices_660, vertices_276, vertices_164, vertices_196, vertices_324, vertices_388, vertices_56, vertices_280, vertices_552, vertices_200, vertices_328, vertices_648, vertices_776, vertices_560, vertices_784, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_229), (false, vertices_681), (true, vertices_338), (true, vertices_660), (true, vertices_276), (true, vertices_324), (true, vertices_388), (true, vertices_280), (true, vertices_328), (true, vertices_776), (true, vertices_560), (true, vertices_784), (true, vertices_448), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 18 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 12 else
  if p.val = (false, vertices_229) then 16 else
  if p.val = (false, vertices_681) then 19 else
  if p.val = (true, vertices_338) then 13 else
  if p.val = (true, vertices_660) then 17 else
  if p.val = (true, vertices_276) then 1 else
  if p.val = (true, vertices_324) then 2 else
  if p.val = (true, vertices_388) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_784) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_896) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_338), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_660), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 5 7 338
cert_row_2 1 1 3 6 8 660
cert_row_4 2 2 3 4 7 8 824 56 3
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
cert_coverFacet 4 452
cert_cover_2 4 5 1 6 7 196 452 3
cert_coverFacet 5 824
cert_cover_5 5 2 2 3 4 7 56 824 3
cert_coverFacet 6 968
cert_cover_5 6 3 2 5 6 7 200 968 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1799

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_one_six_1800.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1800

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 677, 453, 681, 342, 346, 564, 916, 824, 968, 7, 11, 67, 37, 69, 133, 41, 137, 673, 193, 22, 70, 26, 74, 338, 52, 276, 532, 548, 324, 388, 644, 56, 280, 552, 200, 328, 648, 776, 560, 784, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_677, vertices_453, vertices_681, vertices_342, vertices_346, vertices_564, vertices_916, vertices_824, vertices_968] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_37, vertices_69, vertices_133, vertices_41, vertices_137, vertices_673, vertices_193, vertices_22, vertices_70, vertices_26, vertices_74, vertices_338, vertices_52, vertices_276, vertices_532, vertices_548, vertices_324, vertices_388, vertices_644, vertices_56, vertices_280, vertices_552, vertices_200, vertices_328, vertices_648, vertices_776, vertices_560, vertices_784, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_677), (false, vertices_453), (false, vertices_681), (true, vertices_338), (true, vertices_276), (true, vertices_532), (true, vertices_280), (true, vertices_328), (true, vertices_776), (true, vertices_560), (true, vertices_784), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 15 16 17 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 10 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_453) then 14 else
  if p.val = (false, vertices_681) then 19 else
  if p.val = (true, vertices_338) then 11 else
  if p.val = (true, vertices_276) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_280) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_896) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_338), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inl 3
  | 17 => Sum.inl 4
  | 18 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 5 7 338
cert_row_4 1 1 3 6 7 8 916 276 2
cert_row_4 2 2 3 4 7 8 824 56 3
cert_row_4 3 2 5 6 7 8 968 200 3
cert_rows
cert_pivot_2 0 1 3 2
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 0 0 1 3 5 22 342 3
cert_coverFacet 1 346
cert_cover_5 1 0 0 2 3 5 26 346 3
cert_coverFacet 2 564
cert_cover_2 2 3 1 4 8 52 564 3
cert_coverFacet 3 916
cert_cover_5 3 1 1 3 6 7 276 916 2
cert_coverFacet 4 824
cert_cover_5 4 2 2 3 4 7 56 824 3
cert_coverFacet 5 968
cert_cover_5 5 3 2 5 6 7 200 968 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1800

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_one_six_1801.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1801

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 165, 453, 681, 342, 346, 692, 916, 824, 968, 7, 11, 67, 37, 69, 133, 41, 137, 161, 193, 22, 70, 26, 74, 338, 52, 660, 276, 164, 324, 388, 56, 280, 552, 200, 328, 648, 776, 560, 784, 672, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_165, vertices_453, vertices_681, vertices_342, vertices_346, vertices_692, vertices_916, vertices_824, vertices_968] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_37, vertices_69, vertices_133, vertices_41, vertices_137, vertices_161, vertices_193, vertices_22, vertices_70, vertices_26, vertices_74, vertices_338, vertices_52, vertices_660, vertices_276, vertices_164, vertices_324, vertices_388, vertices_56, vertices_280, vertices_552, vertices_200, vertices_328, vertices_648, vertices_776, vertices_560, vertices_784, vertices_672, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_165), (false, vertices_453), (false, vertices_681), (true, vertices_338), (true, vertices_660), (true, vertices_276), (true, vertices_280), (true, vertices_328), (true, vertices_776), (true, vertices_560), (true, vertices_784), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 12 16 18 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 10 else
  if p.val = (false, vertices_165) then 1 else
  if p.val = (false, vertices_453) then 14 else
  if p.val = (false, vertices_681) then 17 else
  if p.val = (true, vertices_338) then 11 else
  if p.val = (true, vertices_660) then 15 else
  if p.val = (true, vertices_276) then 2 else
  if p.val = (true, vertices_280) then 3 else
  if p.val = (true, vertices_328) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_784) then 7 else
  if p.val = (true, vertices_896) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_165), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_338), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_660), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 5 7 338
cert_row_2 1 1 3 6 8 660
cert_row_4 2 2 3 4 7 8 824 56 3
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
cert_coverFacet 4 824
cert_cover_5 4 2 2 3 4 7 56 824 3
cert_coverFacet 5 968
cert_cover_5 5 3 2 5 6 7 200 968 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1801

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_one_six_1802.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1802

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 229, 681, 342, 346, 692, 788, 964, 824, 968, 7, 11, 67, 37, 69, 41, 137, 161, 193, 22, 70, 26, 74, 338, 52, 276, 532, 164, 196, 324, 644, 772, 56, 280, 552, 200, 328, 648, 776, 560, 784, 672, 960]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_229, vertices_681, vertices_342, vertices_346, vertices_692, vertices_788, vertices_964, vertices_824, vertices_968] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_37, vertices_69, vertices_41, vertices_137, vertices_161, vertices_193, vertices_22, vertices_70, vertices_26, vertices_74, vertices_338, vertices_52, vertices_276, vertices_532, vertices_164, vertices_196, vertices_324, vertices_644, vertices_772, vertices_56, vertices_280, vertices_552, vertices_200, vertices_328, vertices_648, vertices_776, vertices_560, vertices_784, vertices_672, vertices_960] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_229), (false, vertices_681), (true, vertices_338), (true, vertices_276), (true, vertices_532), (true, vertices_324), (true, vertices_644), (true, vertices_772), (true, vertices_280), (true, vertices_328), (true, vertices_776), (true, vertices_560), (true, vertices_784), (true, vertices_960)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 12 else
  if p.val = (false, vertices_229) then 16 else
  if p.val = (false, vertices_681) then 18 else
  if p.val = (true, vertices_338) then 13 else
  if p.val = (true, vertices_276) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_324) then 3 else
  if p.val = (true, vertices_644) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_328) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_960) then 22 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_338), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(true, vertices_960), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 5 7 338
cert_row_2 1 5 6 7 8 960
cert_row_4 2 1 3 4 6 8 692 52 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 0 0 1 3 5 22 342 3
cert_coverFacet 1 346
cert_cover_5 1 0 0 2 3 5 26 346 3
cert_coverFacet 2 692
cert_cover_5 2 2 1 3 4 6 52 692 3
cert_coverFacet 3 788
cert_cover_2 3 3 1 7 8 276 788 3
cert_coverFacet 4 964
cert_cover_5 4 1 1 5 6 7 196 964 3
cert_coverFacet 5 824
cert_cover_5 5 3 2 3 4 7 56 824 3
cert_coverFacet 6 968
cert_cover_5 6 1 2 5 6 7 200 968 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1802

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_one_six_1803.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1803

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 789, 837, 601, 230, 426, 308, 484, 824, 968, 7, 11, 67, 21, 69, 773, 25, 73, 529, 577, 38, 70, 42, 138, 162, 194, 52, 276, 228, 292, 324, 56, 536, 296, 200, 584, 392, 776, 304, 784, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_789, vertices_837, vertices_601, vertices_230, vertices_426, vertices_308, vertices_484, vertices_824, vertices_968] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_773, vertices_25, vertices_73, vertices_529, vertices_577, vertices_38, vertices_70, vertices_42, vertices_138, vertices_162, vertices_194, vertices_52, vertices_276, vertices_228, vertices_292, vertices_324, vertices_56, vertices_536, vertices_296, vertices_200, vertices_584, vertices_392, vertices_776, vertices_304, vertices_784, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_789), (false, vertices_837), (false, vertices_601), (true, vertices_162), (true, vertices_228), (true, vertices_292), (true, vertices_296), (true, vertices_392), (true, vertices_776), (true, vertices_304), (true, vertices_416), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 9 14 11 18 19 20 21 22 23
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 10 else
  if p.val = (false, vertices_789) then 15 else
  if p.val = (false, vertices_837) then 16 else
  if p.val = (false, vertices_601) then 13 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_228) then 17 else
  if p.val = (true, vertices_292) then 2 else
  if p.val = (true, vertices_296) then 3 else
  if p.val = (true, vertices_392) then 4 else
  if p.val = (true, vertices_776) then 5 else
  if p.val = (true, vertices_304) then 6 else
  if p.val = (true, vertices_416) then 7 else
  if p.val = (true, vertices_448) then 8 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inl 0
  | 10 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 11 => Sum.inl 2
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_228), by decide +kernel⟩
  | 18 => Sum.inl 3
  | 19 => Sum.inl 4
  | 20 => Sum.inl 5
  | 21 => Sum.inl 6
  | 22 => Sum.inl 7
  | 23 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 5 6 228
cert_row_4 1 0 2 4 6 7 426 42 3
cert_row_4 2 2 3 4 7 8 824 56 3
cert_row_4 3 2 5 6 7 8 968 200 3
cert_rows
cert_pivot_2 1 0 3 2
cert_heightProof 4
cert_coverFacet 0 230
cert_cover_5 0 0 0 1 4 5 38 230 3
cert_coverFacet 1 426
cert_cover_5 1 1 0 2 4 6 42 426 3
cert_coverFacet 2 308
cert_cover_2 2 3 1 4 7 52 308 3
cert_coverFacet 3 484
cert_cover_5 3 0 1 4 5 7 228 484 3
cert_coverFacet 4 824
cert_cover_5 4 2 2 3 4 7 56 824 3
cert_coverFacet 5 968
cert_cover_5 5 3 2 5 6 7 200 968 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1803

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_one_six_1804.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1804

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 659, 451, 357, 817, 897, 78, 218, 812, 716, 964, 696, 7, 19, 67, 131, 37, 69, 49, 529, 289, 321, 385, 641, 769, 14, 70, 26, 74, 146, 194, 44, 76, 524, 292, 708, 324, 772, 56, 152, 552, 200, 648, 560, 656, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_659, vertices_451, vertices_357, vertices_817, vertices_897, vertices_78, vertices_218, vertices_812, vertices_716, vertices_964, vertices_696] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_19, vertices_67, vertices_131, vertices_37, vertices_69, vertices_49, vertices_529, vertices_289, vertices_321, vertices_385, vertices_641, vertices_769, vertices_14, vertices_70, vertices_26, vertices_74, vertices_146, vertices_194, vertices_44, vertices_76, vertices_524, vertices_292, vertices_708, vertices_324, vertices_772, vertices_56, vertices_152, vertices_552, vertices_200, vertices_648, vertices_560, vertices_656, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_659), (false, vertices_451), (false, vertices_357), (false, vertices_817), (false, vertices_897), (true, vertices_74), (true, vertices_76), (true, vertices_524), (true, vertices_708), (true, vertices_772), (true, vertices_152), (true, vertices_552), (true, vertices_200), (true, vertices_648)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 13 17 18 20 21 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_659) then 11 else
  if p.val = (false, vertices_451) then 12 else
  if p.val = (false, vertices_357) then 15 else
  if p.val = (false, vertices_817) then 19 else
  if p.val = (false, vertices_897) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_708) then 16 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_648) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 12 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_708), by decide +kernel⟩
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
cert_row_4 0 0 2 3 5 6 218 26 3
cert_row_2 1 1 5 6 8 708
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 2 3 4 6 8 696 56 3
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 218
cert_cover_5 1 0 0 2 3 5 26 218 3
cert_coverFacet 2 812
cert_cover_5 2 2 1 2 4 7 44 812 3
cert_coverFacet 3 716
cert_cover_5 3 1 1 2 5 6 76 716 3
cert_coverFacet 4 964
cert_cover_5 4 1 1 5 6 7 708 964 3
cert_coverFacet 5 696
cert_cover_5 5 3 2 3 4 6 56 696 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1804

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_one_six_1805.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1805

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 203, 275, 899, 681, 817, 78, 86, 466, 812, 716, 372, 964, 11, 19, 131, 259, 41, 137, 49, 273, 545, 641, 769, 14, 22, 70, 74, 82, 274, 194, 386, 44, 76, 524, 52, 84, 292, 708, 324, 772, 552, 200, 648, 304, 336, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_203, vertices_275, vertices_899, vertices_681, vertices_817, vertices_78, vertices_86, vertices_466, vertices_812, vertices_716, vertices_372, vertices_964] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_131, vertices_259, vertices_41, vertices_137, vertices_49, vertices_273, vertices_545, vertices_641, vertices_769, vertices_14, vertices_22, vertices_70, vertices_74, vertices_82, vertices_274, vertices_194, vertices_386, vertices_44, vertices_76, vertices_524, vertices_52, vertices_84, vertices_292, vertices_708, vertices_324, vertices_772, vertices_552, vertices_200, vertices_648, vertices_304, vertices_336, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_203), (false, vertices_275), (false, vertices_899), (false, vertices_681), (false, vertices_817), (true, vertices_70), (true, vertices_82), (true, vertices_76), (true, vertices_524), (true, vertices_84), (true, vertices_292), (true, vertices_708), (true, vertices_324), (true, vertices_772), (true, vertices_336), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_203) then 12 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_899) then 13 else
  if p.val = (false, vertices_681) then 18 else
  if p.val = (false, vertices_817) then 20 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_708) then 16 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_448) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_708), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 6 7 466 82 3
cert_row_2 1 1 5 6 8 708
cert_row_4 2 1 2 4 7 8 812 44 3
cert_row_4 3 1 3 4 5 7 372 52 3
cert_rows
cert_pivot_2 0 6 2 1
cert_heightProof 4
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 86
cert_cover_2 1 1 0 3 5 22 86 3
cert_coverFacet 2 466
cert_cover_5 2 0 0 3 5 6 82 466 3
cert_coverFacet 3 812
cert_cover_5 3 2 1 2 4 7 44 812 3
cert_coverFacet 4 716
cert_cover_5 4 1 1 2 5 6 76 716 3
cert_coverFacet 5 372
cert_cover_5 5 3 1 3 4 5 52 372 3
cert_coverFacet 6 964
cert_cover_5 6 1 1 5 6 7 708 964 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1805

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_one_six_1806.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1806

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 391, 211, 805, 625, 961, 78, 198, 602, 428, 204, 824, 968, 7, 19, 131, 37, 261, 49, 81, 545, 193, 577, 385, 769, 14, 70, 134, 26, 74, 82, 194, 44, 76, 140, 292, 196, 388, 56, 536, 296, 200, 584, 392, 776, 560, 592, 800, 960]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_391, vertices_211, vertices_805, vertices_625, vertices_961, vertices_78, vertices_198, vertices_602, vertices_428, vertices_204, vertices_824, vertices_968] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_19, vertices_131, vertices_37, vertices_261, vertices_49, vertices_81, vertices_545, vertices_193, vertices_577, vertices_385, vertices_769, vertices_14, vertices_70, vertices_134, vertices_26, vertices_74, vertices_82, vertices_194, vertices_44, vertices_76, vertices_140, vertices_292, vertices_196, vertices_388, vertices_56, vertices_536, vertices_296, vertices_200, vertices_584, vertices_392, vertices_776, vertices_560, vertices_592, vertices_800, vertices_960] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_391), (false, vertices_211), (false, vertices_805), (false, vertices_625), (false, vertices_961), (true, vertices_70), (true, vertices_74), (true, vertices_76), (true, vertices_140), (true, vertices_196), (true, vertices_536), (true, vertices_296), (true, vertices_200), (true, vertices_584), (true, vertices_392), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 18 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_391) then 12 else
  if p.val = (false, vertices_211) then 13 else
  if p.val = (false, vertices_805) then 16 else
  if p.val = (false, vertices_625) then 19 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_196) then 4 else
  if p.val = (true, vertices_536) then 5 else
  if p.val = (true, vertices_296) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_584) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_776) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inl 3
  | 19 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 20 => Sum.inl 4
  | 21 => Sum.inl 5
  | 22 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 8 602 26 3
cert_row_2 1 5 6 7 8 960
cert_row_4 2 1 2 4 6 7 428 44 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 602
cert_cover_5 2 0 0 2 3 5 26 602 3
cert_coverFacet 3 428
cert_cover_5 3 2 1 2 4 6 44 428 3
cert_coverFacet 4 204
cert_cover_2 4 2 1 5 6 76 204 3
cert_coverFacet 5 824
cert_cover_5 5 3 2 3 4 7 56 824 3
cert_coverFacet 6 968
cert_cover_5 6 1 2 5 6 7 200 968 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1806

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_one_six_1807.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1807

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 357, 425, 961, 534, 838, 602, 436, 916, 696, 712, 7, 11, 67, 37, 69, 41, 137, 289, 193, 321, 385, 22, 70, 518, 26, 74, 530, 578, 52, 404, 532, 292, 324, 772, 56, 536, 168, 200, 584, 648, 176, 656, 416, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_357, vertices_425, vertices_961, vertices_534, vertices_838, vertices_602, vertices_436, vertices_916, vertices_696, vertices_712] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_37, vertices_69, vertices_41, vertices_137, vertices_289, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_518, vertices_26, vertices_74, vertices_530, vertices_578, vertices_52, vertices_404, vertices_532, vertices_292, vertices_324, vertices_772, vertices_56, vertices_536, vertices_168, vertices_200, vertices_584, vertices_648, vertices_176, vertices_656, vertices_416, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_357), (false, vertices_425), (false, vertices_961), (true, vertices_518), (true, vertices_530), (true, vertices_578), (true, vertices_404), (true, vertices_532), (true, vertices_772), (true, vertices_536), (true, vertices_584), (true, vertices_648), (true, vertices_176), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 17 19 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 12 else
  if p.val = (false, vertices_357) then 15 else
  if p.val = (false, vertices_425) then 18 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_404) then 16 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_772) then 5 else
  if p.val = (true, vertices_536) then 6 else
  if p.val = (true, vertices_584) then 7 else
  if p.val = (true, vertices_648) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_656) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_404), by decide +kernel⟩
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
cert_row_4 0 2 3 4 6 8 696 56 3
cert_row_2 1 1 3 6 7 404
cert_row_4 2 0 1 5 7 8 838 70 3
cert_row_4 3 0 2 3 5 8 602 26 3
cert_rows
cert_pivot_2 4 6 1 0
cert_heightProof 4
cert_coverFacet 0 534
cert_cover_2 0 1 0 3 8 22 534 3
cert_coverFacet 1 838
cert_cover_5 1 2 0 1 5 7 70 838 3
cert_coverFacet 2 602
cert_cover_5 2 3 0 2 3 5 26 602 3
cert_coverFacet 3 436
cert_cover_5 3 1 1 3 4 6 52 436 3
cert_coverFacet 4 916
cert_cover_5 4 1 1 3 6 8 404 916 3
cert_coverFacet 5 696
cert_cover_5 5 0 2 3 4 6 56 696 3
cert_coverFacet 6 712
cert_cover_2 6 5 2 6 8 200 712 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1807

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_one_six_1808.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1808

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 357, 425, 961, 790, 838, 602, 436, 696, 712, 912, 7, 11, 67, 37, 69, 41, 137, 289, 193, 321, 385, 22, 70, 774, 26, 74, 530, 578, 52, 276, 292, 324, 56, 536, 168, 200, 584, 648, 176, 400, 656, 784, 416, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_357, vertices_425, vertices_961, vertices_790, vertices_838, vertices_602, vertices_436, vertices_696, vertices_712, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_37, vertices_69, vertices_41, vertices_137, vertices_289, vertices_193, vertices_321, vertices_385, vertices_22, vertices_70, vertices_774, vertices_26, vertices_74, vertices_530, vertices_578, vertices_52, vertices_276, vertices_292, vertices_324, vertices_56, vertices_536, vertices_168, vertices_200, vertices_584, vertices_648, vertices_176, vertices_400, vertices_656, vertices_784, vertices_416, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_357), (false, vertices_425), (false, vertices_961), (true, vertices_774), (true, vertices_530), (true, vertices_578), (true, vertices_276), (true, vertices_536), (true, vertices_584), (true, vertices_648), (true, vertices_176), (true, vertices_400), (true, vertices_656), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 19 20 21 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 12 else
  if p.val = (false, vertices_357) then 16 else
  if p.val = (false, vertices_425) then 18 else
  if p.val = (false, vertices_961) then 22 else
  if p.val = (true, vertices_774) then 13 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_578) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_176) then 7 else
  if p.val = (true, vertices_400) then 8 else
  if p.val = (true, vertices_656) then 9 else
  if p.val = (true, vertices_784) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
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
cert_row_4 0 0 2 3 5 8 602 26 3
cert_row_2 1 0 1 7 8 774
cert_row_4 2 1 3 4 6 7 436 52 3
cert_row_4 3 2 3 4 6 8 696 56 3
cert_rows
cert_pivot_2 5 0 1 2
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 1 0 1 3 7 22 790 3
cert_coverFacet 1 838
cert_cover_5 1 1 0 1 5 7 70 838 3
cert_coverFacet 2 602
cert_cover_5 2 0 0 2 3 5 26 602 3
cert_coverFacet 3 436
cert_cover_5 3 2 1 3 4 6 52 436 3
cert_coverFacet 4 696
cert_cover_5 4 3 2 3 4 6 56 696 3
cert_coverFacet 5 712
cert_cover_2 5 5 2 6 8 200 712 3
cert_coverFacet 6 912
cert_cover_2 6 6 3 7 8 400 912 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1808

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_one_six_1809.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1809

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 75, 805, 709, 361, 961, 214, 154, 458, 692, 824, 920, 7, 11, 67, 37, 69, 517, 41, 73, 289, 705, 321, 769, 22, 70, 26, 74, 138, 146, 194, 52, 148, 548, 196, 644, 56, 152, 792, 296, 328, 392, 560, 656, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_75, vertices_805, vertices_709, vertices_361, vertices_961, vertices_214, vertices_154, vertices_458, vertices_692, vertices_824, vertices_920] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_37, vertices_69, vertices_517, vertices_41, vertices_73, vertices_289, vertices_705, vertices_321, vertices_769, vertices_22, vertices_70, vertices_26, vertices_74, vertices_138, vertices_146, vertices_194, vertices_52, vertices_148, vertices_548, vertices_196, vertices_644, vertices_56, vertices_152, vertices_792, vertices_296, vertices_328, vertices_392, vertices_560, vertices_656, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_75), (false, vertices_805), (false, vertices_709), (false, vertices_361), (false, vertices_961), (true, vertices_138), (true, vertices_146), (true, vertices_194), (true, vertices_148), (true, vertices_152), (true, vertices_792), (true, vertices_392), (true, vertices_560), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 11 14 17 18 19 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 12 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_75) then 1 else
  if p.val = (false, vertices_805) then 13 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_361) then 15 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_792) then 16 else
  if p.val = (true, vertices_392) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_656) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_75), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_792), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 4 6 8 692 52 3
cert_row_2 1 2 3 7 8 792
cert_row_4 2 0 1 3 5 6 214 22 3
cert_row_4 3 0 2 5 6 7 458 74 3
cert_rows
cert_pivot_2 4 8 1 0
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 2 0 1 3 5 22 214 3
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 458
cert_cover_5 2 3 0 2 5 6 74 458 3
cert_coverFacet 3 692
cert_cover_5 3 0 1 3 4 6 52 692 3
cert_coverFacet 4 824
cert_cover_5 4 1 2 3 4 7 56 824 3
cert_coverFacet 5 920
cert_cover_5 5 1 2 3 6 7 152 920 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1809

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_one_six_1810.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1810

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 75, 805, 709, 361, 961, 214, 410, 458, 692, 824, 912, 7, 11, 67, 37, 69, 517, 41, 73, 289, 705, 321, 769, 22, 70, 26, 74, 394, 146, 194, 52, 148, 548, 196, 644, 56, 280, 296, 328, 560, 400, 656, 784, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_75, vertices_805, vertices_709, vertices_361, vertices_961, vertices_214, vertices_410, vertices_458, vertices_692, vertices_824, vertices_912] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_37, vertices_69, vertices_517, vertices_41, vertices_73, vertices_289, vertices_705, vertices_321, vertices_769, vertices_22, vertices_70, vertices_26, vertices_74, vertices_394, vertices_146, vertices_194, vertices_52, vertices_148, vertices_548, vertices_196, vertices_644, vertices_56, vertices_280, vertices_296, vertices_328, vertices_560, vertices_400, vertices_656, vertices_784, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_75), (false, vertices_805), (false, vertices_709), (false, vertices_361), (false, vertices_961), (true, vertices_394), (true, vertices_146), (true, vertices_194), (true, vertices_148), (true, vertices_280), (true, vertices_560), (true, vertices_400), (true, vertices_656), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 10 12 15 17 18 19 22 23 24
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 13 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_75) then 1 else
  if p.val = (false, vertices_805) then 14 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_361) then 16 else
  if p.val = (false, vertices_961) then 21 else
  if p.val = (true, vertices_394) then 11 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_148) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_400) then 7 else
  if p.val = (true, vertices_656) then 8 else
  if p.val = (true, vertices_784) then 9 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_75), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 10 => Sum.inl 0
  | 11 => Sum.inr ⟨(true, vertices_394), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 17 => Sum.inl 3
  | 18 => Sum.inl 4
  | 19 => Sum.inl 5
  | 20 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 22 => Sum.inl 6
  | 23 => Sum.inl 7
  | 24 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 6 214 22 3
cert_row_2 1 0 2 6 7 394
cert_row_4 2 1 3 4 6 8 692 52 3
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 5 0 1 2
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 5 22 214 3
cert_coverFacet 1 410
cert_cover_5 1 1 0 2 3 6 26 410 3
cert_coverFacet 2 458
cert_cover_5 2 1 0 2 5 6 74 458 3
cert_coverFacet 3 692
cert_cover_5 3 2 1 3 4 6 52 692 3
cert_coverFacet 4 824
cert_cover_5 4 3 2 3 4 7 56 824 3
cert_coverFacet 5 912
cert_cover_2 5 6 3 7 8 400 912 3
cert_coveringFacets
cert_coveringProof_6
cert_certificate 4 6
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1810

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_one_six_1811.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1811

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 211, 677, 709, 433, 78, 410, 458, 556, 844, 824, 992, 7, 19, 67, 37, 69, 645, 49, 145, 161, 193, 14, 70, 26, 74, 394, 146, 194, 44, 76, 524, 548, 580, 56, 280, 552, 328, 776, 304, 400, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_211, vertices_677, vertices_709, vertices_433, vertices_78, vertices_410, vertices_458, vertices_556, vertices_844, vertices_824, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_19, vertices_67, vertices_37, vertices_69, vertices_645, vertices_49, vertices_145, vertices_161, vertices_193, vertices_14, vertices_70, vertices_26, vertices_74, vertices_394, vertices_146, vertices_194, vertices_44, vertices_76, vertices_524, vertices_548, vertices_580, vertices_56, vertices_280, vertices_552, vertices_328, vertices_776, vertices_304, vertices_400, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_211), (false, vertices_677), (false, vertices_709), (false, vertices_433), (true, vertices_74), (true, vertices_394), (true, vertices_76), (true, vertices_524), (true, vertices_280), (true, vertices_552), (true, vertices_328), (true, vertices_776), (true, vertices_800), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 18 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_211) then 12 else
  if p.val = (false, vertices_677) then 16 else
  if p.val = (false, vertices_709) then 17 else
  if p.val = (false, vertices_433) then 20 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_394) then 13 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_280) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_776) then 7 else
  if p.val = (true, vertices_800) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_394), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inl 7
  | 25 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 6 7 394
cert_row_4 1 1 2 5 7 8 844 76 3
cert_row_4 2 2 3 4 7 8 824 56 3
cert_row_4 3 4 5 6 7 8 992 416 1
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 78
cert_cover_2 0 1 0 2 5 14 78 3
cert_coverFacet 1 410
cert_cover_5 1 0 0 2 3 6 26 410 3
cert_coverFacet 2 458
cert_cover_5 2 0 0 2 5 6 74 458 3
cert_coverFacet 3 556
cert_cover_2 3 2 1 4 8 44 556 3
cert_coverFacet 4 844
cert_cover_5 4 1 1 2 5 7 76 844 3
cert_coverFacet 5 824
cert_cover_5 5 2 2 3 4 7 56 824 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 416 992 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1811

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_one_six_1812.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1812

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 341, 793, 841, 358, 170, 930, 962, 820, 696, 712, 7, 11, 67, 21, 69, 25, 73, 777, 273, 321, 38, 70, 42, 138, 162, 290, 194, 322, 898, 52, 276, 292, 324, 56, 536, 168, 200, 584, 648, 560, 784, 672, 800, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_341, vertices_793, vertices_841, vertices_358, vertices_170, vertices_930, vertices_962, vertices_820, vertices_696, vertices_712] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_25, vertices_73, vertices_777, vertices_273, vertices_321, vertices_38, vertices_70, vertices_42, vertices_138, vertices_162, vertices_290, vertices_194, vertices_322, vertices_898, vertices_52, vertices_276, vertices_292, vertices_324, vertices_56, vertices_536, vertices_168, vertices_200, vertices_584, vertices_648, vertices_560, vertices_784, vertices_672, vertices_800, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_341), (false, vertices_793), (false, vertices_841), (true, vertices_162), (true, vertices_290), (true, vertices_322), (true, vertices_898), (true, vertices_292), (true, vertices_168), (true, vertices_648), (true, vertices_560), (true, vertices_672), (true, vertices_800), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 14 17 20 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 15 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 12 else
  if p.val = (false, vertices_341) then 16 else
  if p.val = (false, vertices_793) then 18 else
  if p.val = (false, vertices_841) then 19 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_898) then 13 else
  if p.val = (true, vertices_292) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_800) then 9 else
  if p.val = (true, vertices_704) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_71), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_898), by decide +kernel⟩
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
cert_row_4 0 0 1 4 5 7 358 38 3
cert_row_2 1 0 6 7 8 898
cert_row_4 2 1 3 4 7 8 820 52 3
cert_row_4 3 2 3 4 6 8 696 56 3
cert_rows
cert_pivot_2 5 0 1 2
cert_heightProof 4
cert_coverFacet 0 358
cert_cover_5 0 0 0 1 4 5 38 358 3
cert_coverFacet 1 170
cert_cover_2 1 2 0 4 6 42 170 3
cert_coverFacet 2 930
cert_cover_5 2 1 0 4 6 7 162 930 3
cert_coverFacet 3 962
cert_cover_5 3 1 0 5 6 7 194 962 3
cert_coverFacet 4 820
cert_cover_5 4 2 1 3 4 7 52 820 3
cert_coverFacet 5 696
cert_cover_5 5 3 2 3 4 6 56 696 3
cert_coverFacet 6 712
cert_cover_2 6 5 2 6 8 200 712 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1812

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_one_six_1813.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1813

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 341, 793, 841, 422, 454, 170, 820, 696, 712, 992, 7, 11, 67, 21, 69, 25, 73, 777, 273, 321, 38, 70, 390, 42, 138, 162, 194, 52, 276, 292, 324, 56, 536, 168, 200, 584, 648, 560, 784, 416, 672, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_341, vertices_793, vertices_841, vertices_422, vertices_454, vertices_170, vertices_820, vertices_696, vertices_712, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_25, vertices_73, vertices_777, vertices_273, vertices_321, vertices_38, vertices_70, vertices_390, vertices_42, vertices_138, vertices_162, vertices_194, vertices_52, vertices_276, vertices_292, vertices_324, vertices_56, vertices_536, vertices_168, vertices_200, vertices_584, vertices_648, vertices_560, vertices_784, vertices_416, vertices_672, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_341), (false, vertices_793), (false, vertices_841), (true, vertices_390), (true, vertices_162), (true, vertices_292), (true, vertices_168), (true, vertices_648), (true, vertices_560), (true, vertices_416), (true, vertices_672), (true, vertices_800), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
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
  if p.val = (true, vertices_168) then 3 else
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
  | 3 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
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
cert_row_2 0 0 1 6 7 390
cert_row_4 1 1 3 4 7 8 820 52 3
cert_row_4 2 2 3 4 6 8 696 56 3
cert_row_4 3 4 5 6 7 8 992 416 1
cert_rows
cert_pivot_2 0 1 2 4
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 0 0 1 4 6 38 422 3
cert_coverFacet 1 454
cert_cover_5 1 0 0 1 5 6 70 454 3
cert_coverFacet 2 170
cert_cover_2 2 2 0 4 6 42 170 3
cert_coverFacet 3 820
cert_cover_5 3 1 1 3 4 7 52 820 3
cert_coverFacet 4 696
cert_cover_5 4 2 2 3 4 6 56 696 3
cert_coverFacet 5 712
cert_cover_2 5 5 2 6 8 200 712 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 416 992 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1813

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_one_six_1814.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1814

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [63, 71, 203, 341, 793, 841, 230, 682, 436, 964, 568, 712, 944, 7, 11, 67, 21, 69, 25, 73, 777, 273, 321, 38, 70, 42, 138, 162, 194, 52, 276, 164, 196, 324, 388, 56, 536, 552, 200, 584, 648, 432, 560, 784, 672, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_63, vertices_71, vertices_203, vertices_341, vertices_793, vertices_841, vertices_230, vertices_682, vertices_436, vertices_964, vertices_568, vertices_712, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_67, vertices_21, vertices_69, vertices_25, vertices_73, vertices_777, vertices_273, vertices_321, vertices_38, vertices_70, vertices_42, vertices_138, vertices_162, vertices_194, vertices_52, vertices_276, vertices_164, vertices_196, vertices_324, vertices_388, vertices_56, vertices_536, vertices_552, vertices_200, vertices_584, vertices_648, vertices_432, vertices_560, vertices_784, vertices_672, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_63), (false, vertices_71), (false, vertices_203), (false, vertices_341), (false, vertices_793), (false, vertices_841), (true, vertices_162), (true, vertices_164), (true, vertices_196), (true, vertices_388), (true, vertices_552), (true, vertices_648), (true, vertices_432), (true, vertices_560), (true, vertices_672), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 13 16 19 21 22 23 24 25
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_63) then 14 else
  if p.val = (false, vertices_71) then 0 else
  if p.val = (false, vertices_203) then 12 else
  if p.val = (false, vertices_341) then 15 else
  if p.val = (false, vertices_793) then 17 else
  if p.val = (false, vertices_841) then 18 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_196) then 3 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_648) then 6 else
  if p.val = (true, vertices_432) then 20 else
  if p.val = (true, vertices_560) then 7 else
  if p.val = (true, vertices_672) then 8 else
  if p.val = (true, vertices_704) then 9 else
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
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_63), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
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
cert_row_4 1 0 2 4 6 8 682 42 3
cert_row_4 2 0 1 4 5 6 230 38 3
cert_row_4 3 1 5 6 7 8 964 196 3
cert_rows
cert_pivot_2 3 2 0 1
cert_heightProof 4
cert_coverFacet 0 230
cert_cover_5 0 2 0 1 4 5 38 230 3
cert_coverFacet 1 682
cert_cover_5 1 1 0 2 4 6 42 682 3
cert_coverFacet 2 436
cert_cover_5 2 0 1 3 4 6 52 436 3
cert_coverFacet 3 964
cert_cover_5 3 3 1 5 6 7 196 964 3
cert_coverFacet 4 568
cert_cover_2 4 3 2 4 8 56 568 3
cert_coverFacet 5 712
cert_cover_2 5 5 2 6 8 200 712 3
cert_coverFacet 6 944
cert_cover_5 6 0 3 4 6 8 432 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1814

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_1920 : Certifies 1920 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1783.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1921 : Certifies 1921 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1784.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1922 : Certifies 1922 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1785.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1923 : Certifies 1923 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1786.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1924 : Certifies 1924 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1787.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1925 : Certifies 1925 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1788.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1926 : Certifies 1926 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1789.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1927 : Certifies 1927 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1790.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1928 : Certifies 1928 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1791.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1929 : Certifies 1929 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1792.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1930 : Certifies 1930 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1793.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1931 : Certifies 1931 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1794.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1932 : Certifies 1932 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1797.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1933 : Certifies 1933 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1798.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1934 : Certifies 1934 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1799.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1935 : Certifies 1935 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1800.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1936 : Certifies 1936 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1801.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1937 : Certifies 1937 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1802.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1938 : Certifies 1938 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1803.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1939 : Certifies 1939 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1804.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1940 : Certifies 1940 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1805.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1941 : Certifies 1941 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1806.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1942 : Certifies 1942 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1807.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1943 : Certifies 1943 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1808.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1944 : Certifies 1944 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1809.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1945 : Certifies 1945 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1810.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1946 : Certifies 1946 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1811.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1947 : Certifies 1947 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1812.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1948 : Certifies 1948 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1813.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_1949 : Certifies 1949 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1814.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B064 (j : Fin 30) :
    Certifies (1920 + j.val) := by
  fin_cases j
  · exact projection_1920
  · exact projection_1921
  · exact projection_1922
  · exact projection_1923
  · exact projection_1924
  · exact projection_1925
  · exact projection_1926
  · exact projection_1927
  · exact projection_1928
  · exact projection_1929
  · exact projection_1930
  · exact projection_1931
  · exact projection_1932
  · exact projection_1933
  · exact projection_1934
  · exact projection_1935
  · exact projection_1936
  · exact projection_1937
  · exact projection_1938
  · exact projection_1939
  · exact projection_1940
  · exact projection_1941
  · exact projection_1942
  · exact projection_1943
  · exact projection_1944
  · exact projection_1945
  · exact projection_1946
  · exact projection_1947
  · exact projection_1948
  · exact projection_1949

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
