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
/- Source: ProjectionCertificates/R_m15e11q2_0041.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0041

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 99, 291, 707, 357, 665, 465, 806, 234, 682, 572, 412, 108, 460, 788, 35, 67, 259, 515, 145, 273, 529, 97, 289, 193, 321, 641, 170, 98, 290, 546, 194, 642, 770, 28, 44, 76, 396, 276, 532, 100, 292, 548, 324, 772, 152, 536, 104, 552, 200, 648, 400, 784, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_99, vertices_291, vertices_707, vertices_357, vertices_665, vertices_465, vertices_806, vertices_234, vertices_682, vertices_572, vertices_412, vertices_108, vertices_460, vertices_788] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_259, vertices_515, vertices_145, vertices_273, vertices_529, vertices_97, vertices_289, vertices_193, vertices_321, vertices_641, vertices_170, vertices_98, vertices_290, vertices_546, vertices_194, vertices_642, vertices_770, vertices_28, vertices_44, vertices_76, vertices_396, vertices_276, vertices_532, vertices_100, vertices_292, vertices_548, vertices_324, vertices_772, vertices_152, vertices_536, vertices_104, vertices_552, vertices_200, vertices_648, vertices_400, vertices_784, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_99), (false, vertices_291), (false, vertices_707), (false, vertices_357), (false, vertices_665), (false, vertices_465), (true, vertices_170), (true, vertices_546), (true, vertices_28), (true, vertices_44), (true, vertices_76), (true, vertices_396), (true, vertices_276), (true, vertices_532), (true, vertices_548), (true, vertices_772), (true, vertices_104), (true, vertices_552), (true, vertices_200)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_99) then 0 else
  if p.val = (false, vertices_291) then 1 else
  if p.val = (false, vertices_707) then 15 else
  if p.val = (false, vertices_357) then 18 else
  if p.val = (false, vertices_665) then 21 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (true, vertices_170) then 16 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_28) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_396) then 19 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_200) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_99), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_291), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_170), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 4 8 572 28 3
cert_row_4 1 0 1 4 7 8 806 290 1
cert_row_2 2 0 2 4 6 170
cert_row_2 3 1 2 6 7 396
cert_rows
cert_pivot_2 3 8 0 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 1 0 1 4 7 290 806 1
cert_coverFacet 1 234
cert_cover_5 1 2 0 2 4 5 170 234 3
cert_coverFacet 2 682
cert_cover_5 2 2 0 2 4 8 170 682 3
cert_coverFacet 3 572
cert_cover_5 3 0 1 2 3 4 28 572 3
cert_coverFacet 4 412
cert_cover_5 4 3 1 2 3 6 28 412 3
cert_coverFacet 5 108
cert_cover_2 5 2 1 4 5 44 108 3
cert_coverFacet 6 460
cert_cover_5 6 3 1 2 5 6 76 460 3
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0041

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e11q2_0042.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0042

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 285, 541, 677, 453, 849, 558, 122, 586, 434, 466, 674, 428, 312, 600, 29, 133, 261, 517, 273, 529, 193, 321, 577, 641, 42, 74, 522, 50, 82, 402, 162, 546, 194, 578, 642, 44, 268, 524, 164, 548, 388, 56, 88, 280, 536, 296, 584, 304, 336, 592, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_285, vertices_541, vertices_677, vertices_453, vertices_849, vertices_558, vertices_122, vertices_586, vertices_434, vertices_466, vertices_674, vertices_428, vertices_312, vertices_600] (by decide +kernel)
  polygons := literalFinset [vertices_29, vertices_133, vertices_261, vertices_517, vertices_273, vertices_529, vertices_193, vertices_321, vertices_577, vertices_641, vertices_42, vertices_74, vertices_522, vertices_50, vertices_82, vertices_402, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_44, vertices_268, vertices_524, vertices_164, vertices_548, vertices_388, vertices_56, vertices_88, vertices_280, vertices_536, vertices_296, vertices_584, vertices_304, vertices_336, vertices_592, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_285), (false, vertices_541), (false, vertices_677), (false, vertices_453), (false, vertices_849), (true, vertices_42), (true, vertices_74), (true, vertices_522), (true, vertices_50), (true, vertices_82), (true, vertices_402), (true, vertices_162), (true, vertices_546), (true, vertices_44), (true, vertices_56), (true, vertices_88), (true, vertices_296), (true, vertices_584), (true, vertices_304), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 20 17 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 15 else
  if p.val = (false, vertices_285) then 18 else
  if p.val = (false, vertices_541) then 19 else
  if p.val = (false, vertices_677) then 21 else
  if p.val = (false, vertices_453) then 22 else
  if p.val = (false, vertices_849) then 24 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_402) then 16 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_44) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_402), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 8 558 42 1
cert_row_4 1 0 2 3 4 5 122 42 2
cert_row_2 2 0 3 6 7 402
cert_row_4 3 1 2 4 6 7 428 44 3
cert_rows
cert_pivot_2 8 5 0 1
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 0 0 1 2 4 42 558 1
cert_coverFacet 1 122
cert_cover_5 1 1 0 2 3 4 42 122 2
cert_coverFacet 2 586
cert_cover_2 2 2 0 5 8 74 586 3
cert_coverFacet 3 434
cert_cover_5 3 2 0 3 4 6 50 434 3
cert_coverFacet 4 466
cert_cover_5 4 2 0 3 5 6 82 466 3
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 428
cert_cover_5 6 3 1 2 4 6 44 428 3
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coverFacet 8 600
cert_cover_2 8 3 2 5 8 88 600 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0042

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e11q2_0043.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0043

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [171, 555, 787, 451, 341, 601, 201, 678, 898, 124, 572, 916, 356, 420, 488, 43, 131, 259, 515, 73, 137, 521, 81, 273, 529, 193, 321, 162, 546, 386, 642, 770, 60, 84, 276, 532, 100, 164, 292, 548, 324, 388, 644, 88, 536, 104, 168, 552, 200, 784, 352, 416, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_171, vertices_555, vertices_787, vertices_451, vertices_341, vertices_601, vertices_201, vertices_678, vertices_898, vertices_124, vertices_572, vertices_916, vertices_356, vertices_420, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_43, vertices_131, vertices_259, vertices_515, vertices_73, vertices_137, vertices_521, vertices_81, vertices_273, vertices_529, vertices_193, vertices_321, vertices_162, vertices_546, vertices_386, vertices_642, vertices_770, vertices_60, vertices_84, vertices_276, vertices_532, vertices_100, vertices_164, vertices_292, vertices_548, vertices_324, vertices_388, vertices_644, vertices_88, vertices_536, vertices_104, vertices_168, vertices_552, vertices_200, vertices_784, vertices_352, vertices_416, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_171), (false, vertices_555), (false, vertices_787), (false, vertices_451), (false, vertices_341), (false, vertices_601), (false, vertices_201), (true, vertices_642), (true, vertices_60), (true, vertices_532), (true, vertices_100), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_388), (true, vertices_644), (true, vertices_104), (true, vertices_352), (true, vertices_416), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 20 13 16 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_171) then 17 else
  if p.val = (false, vertices_555) then 18 else
  if p.val = (false, vertices_787) then 21 else
  if p.val = (false, vertices_451) then 22 else
  if p.val = (false, vertices_341) then 14 else
  if p.val = (false, vertices_601) then 19 else
  if p.val = (false, vertices_201) then 0 else
  if p.val = (true, vertices_642) then 1 else
  if p.val = (true, vertices_60) then 15 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_352) then 10 else
  if p.val = (true, vertices_416) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_201), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_60), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_171), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 20 => Sum.inl 0
  | 21 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 162 1
cert_row_4 1 1 3 6 7 8 916 276 2
cert_row_2 2 1 2 3 4 60
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 162 678 1
cert_coverFacet 1 898
cert_cover_2 1 6 0 7 8 386 898 3
cert_coverFacet 2 124
cert_cover_5 2 2 1 2 3 5 60 124 3
cert_coverFacet 3 572
cert_cover_5 3 2 1 2 3 8 60 572 3
cert_coverFacet 4 916
cert_cover_5 4 1 1 3 6 7 276 916 2
cert_coverFacet 5 356
cert_cover_2 5 4 1 5 7 100 356 3
cert_coverFacet 6 420
cert_cover_2 6 4 1 6 7 164 420 3
cert_coverFacet 7 488
cert_cover_5 7 3 2 4 5 6 104 488 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0043

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e11q2_0044.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0044

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 227, 547, 323, 677, 345, 721, 806, 426, 458, 316, 604, 172, 716, 788, 35, 67, 259, 515, 81, 273, 529, 161, 545, 193, 321, 641, 394, 162, 290, 546, 194, 322, 770, 28, 44, 588, 140, 276, 532, 164, 292, 548, 644, 772, 88, 280, 168, 296, 200, 328, 592, 784, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_227, vertices_547, vertices_323, vertices_677, vertices_345, vertices_721, vertices_806, vertices_426, vertices_458, vertices_316, vertices_604, vertices_172, vertices_716, vertices_788] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_259, vertices_515, vertices_81, vertices_273, vertices_529, vertices_161, vertices_545, vertices_193, vertices_321, vertices_641, vertices_394, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_770, vertices_28, vertices_44, vertices_588, vertices_140, vertices_276, vertices_532, vertices_164, vertices_292, vertices_548, vertices_644, vertices_772, vertices_88, vertices_280, vertices_168, vertices_296, vertices_200, vertices_328, vertices_592, vertices_784, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_227), (false, vertices_547), (false, vertices_323), (false, vertices_677), (false, vertices_345), (false, vertices_721), (true, vertices_394), (true, vertices_290), (true, vertices_28), (true, vertices_44), (true, vertices_588), (true, vertices_140), (true, vertices_276), (true, vertices_532), (true, vertices_292), (true, vertices_772), (true, vertices_168), (true, vertices_296), (true, vertices_200)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_227) then 15 else
  if p.val = (false, vertices_547) then 0 else
  if p.val = (false, vertices_323) then 1 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_345) then 21 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (true, vertices_394) then 16 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_28) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_588) then 19 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_200) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_547), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_394), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_588), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 5 8 588
cert_row_2 1 0 2 6 7 394
cert_row_4 2 0 1 4 7 8 806 290 1
cert_row_4 3 1 2 3 4 7 316 28 3
cert_rows
cert_pivot_2 5 6 0 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 2 0 1 4 7 290 806 1
cert_coverFacet 1 426
cert_cover_5 1 1 0 2 4 6 394 426 2
cert_coverFacet 2 458
cert_cover_5 2 1 0 2 5 6 394 458 2
cert_coverFacet 3 316
cert_cover_5 3 3 1 2 3 4 28 316 3
cert_coverFacet 4 604
cert_cover_5 4 0 1 2 3 5 28 604 3
cert_coverFacet 5 172
cert_cover_2 5 2 1 4 6 44 172 3
cert_coverFacet 6 716
cert_cover_5 6 0 1 2 5 6 588 716 3
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0044

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e11q2_0045.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0045

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 589, 565, 85, 305, 465, 737, 782, 234, 618, 394, 818, 220, 412, 788, 21, 69, 517, 49, 81, 273, 161, 289, 545, 193, 577, 385, 106, 138, 266, 522, 162, 290, 546, 386, 770, 156, 76, 268, 524, 84, 276, 532, 772, 200, 584, 392, 304, 560, 208, 400, 784, 224, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_589, vertices_565, vertices_85, vertices_305, vertices_465, vertices_737, vertices_782, vertices_234, vertices_618, vertices_394, vertices_818, vertices_220, vertices_412, vertices_788] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_517, vertices_49, vertices_81, vertices_273, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_106, vertices_138, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_386, vertices_770, vertices_156, vertices_76, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_772, vertices_200, vertices_584, vertices_392, vertices_304, vertices_560, vertices_208, vertices_400, vertices_784, vertices_224, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_589), (false, vertices_565), (false, vertices_85), (false, vertices_305), (false, vertices_465), (false, vertices_737), (true, vertices_106), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_546), (true, vertices_770), (true, vertices_156), (true, vertices_268), (true, vertices_276), (true, vertices_772), (true, vertices_200), (true, vertices_392), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 21 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 14 else
  if p.val = (false, vertices_589) then 17 else
  if p.val = (false, vertices_565) then 18 else
  if p.val = (false, vertices_85) then 0 else
  if p.val = (false, vertices_305) then 1 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (false, vertices_737) then 24 else
  if p.val = (true, vertices_106) then 15 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_156) then 19 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_784) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_85), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_305), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_106), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_156), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 4 5 106
cert_row_2 1 1 2 3 6 156
cert_row_4 2 0 1 2 7 8 782 266 1
cert_row_4 3 0 3 4 7 8 818 290 1
cert_rows
cert_pivot_2 5 6 1 0
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 2 0 1 2 7 266 782 1
cert_coverFacet 1 234
cert_cover_5 1 0 0 2 4 6 106 234 3
cert_coverFacet 2 618
cert_cover_5 2 0 0 2 4 8 106 618 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 818
cert_cover_5 4 3 0 3 4 7 290 818 1
cert_coverFacet 5 220
cert_cover_5 5 1 1 2 3 5 156 220 3
cert_coverFacet 6 412
cert_cover_5 6 1 1 2 3 7 156 412 3
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0045

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e11q2_0046.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0046

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [83, 787, 227, 643, 117, 905, 433, 94, 542, 714, 812, 460, 564, 484, 816, 19, 67, 131, 515, 49, 81, 273, 97, 161, 385, 641, 769, 30, 74, 522, 82, 530, 194, 642, 76, 268, 524, 52, 84, 532, 100, 292, 548, 452, 200, 392, 648, 776, 304, 560, 784, 224, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_83, vertices_787, vertices_227, vertices_643, vertices_117, vertices_905, vertices_433, vertices_94, vertices_542, vertices_714, vertices_812, vertices_460, vertices_564, vertices_484, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_131, vertices_515, vertices_49, vertices_81, vertices_273, vertices_97, vertices_161, vertices_385, vertices_641, vertices_769, vertices_30, vertices_74, vertices_522, vertices_82, vertices_530, vertices_194, vertices_642, vertices_76, vertices_268, vertices_524, vertices_52, vertices_84, vertices_532, vertices_100, vertices_292, vertices_548, vertices_452, vertices_200, vertices_392, vertices_648, vertices_776, vertices_304, vertices_560, vertices_784, vertices_224, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_83), (false, vertices_787), (false, vertices_227), (false, vertices_643), (false, vertices_117), (false, vertices_905), (false, vertices_433), (true, vertices_30), (true, vertices_74), (true, vertices_522), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_532), (true, vertices_292), (true, vertices_548), (true, vertices_452), (true, vertices_200), (true, vertices_560), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_83) then 0 else
  if p.val = (false, vertices_787) then 14 else
  if p.val = (false, vertices_227) then 15 else
  if p.val = (false, vertices_643) then 1 else
  if p.val = (false, vertices_117) then 18 else
  if p.val = (false, vertices_905) then 21 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (true, vertices_30) then 16 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_452) then 19 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_83), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_30), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_452), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 3 30
cert_row_4 1 0 2 5 6 8 714 74 3
cert_row_2 2 1 5 6 7 452
cert_row_4 3 1 2 4 7 8 812 268 2
cert_rows
cert_pivot_2 3 0 5 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 5 30 94 3
cert_coverFacet 1 542
cert_cover_5 1 0 0 1 2 8 30 542 3
cert_coverFacet 2 714
cert_cover_5 2 1 0 2 5 6 74 714 3
cert_coverFacet 3 812
cert_cover_5 3 3 1 2 4 7 268 812 2
cert_coverFacet 4 460
cert_cover_5 4 2 1 2 5 6 76 460 3
cert_coverFacet 5 564
cert_cover_2 5 3 1 4 8 52 564 3
cert_coverFacet 6 484
cert_cover_5 6 2 1 4 5 6 100 484 3
cert_coverFacet 7 816
cert_cover_2 7 4 3 7 8 304 816 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0046

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e11q2_0047.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0047

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [555, 115, 659, 653, 409, 297, 369, 614, 850, 236, 556, 916, 452, 836, 488, 19, 35, 515, 41, 137, 265, 521, 113, 145, 273, 289, 641, 82, 530, 98, 546, 578, 44, 140, 524, 100, 548, 196, 324, 580, 388, 644, 772, 232, 296, 552, 392, 336, 400, 656, 784, 352, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_555, vertices_115, vertices_659, vertices_653, vertices_409, vertices_297, vertices_369, vertices_614, vertices_850, vertices_236, vertices_556, vertices_916, vertices_452, vertices_836, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_515, vertices_41, vertices_137, vertices_265, vertices_521, vertices_113, vertices_145, vertices_273, vertices_289, vertices_641, vertices_82, vertices_530, vertices_98, vertices_546, vertices_578, vertices_44, vertices_140, vertices_524, vertices_100, vertices_548, vertices_196, vertices_324, vertices_580, vertices_388, vertices_644, vertices_772, vertices_232, vertices_296, vertices_552, vertices_392, vertices_336, vertices_400, vertices_656, vertices_784, vertices_352, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_555), (false, vertices_115), (false, vertices_659), (false, vertices_653), (false, vertices_409), (false, vertices_297), (false, vertices_369), (true, vertices_578), (true, vertices_44), (true, vertices_100), (true, vertices_548), (true, vertices_196), (true, vertices_324), (true, vertices_580), (true, vertices_388), (true, vertices_772), (true, vertices_232), (true, vertices_784), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 21 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_555) then 14 else
  if p.val = (false, vertices_115) then 22 else
  if p.val = (false, vertices_659) then 15 else
  if p.val = (false, vertices_653) then 17 else
  if p.val = (false, vertices_409) then 19 else
  if p.val = (false, vertices_297) then 0 else
  if p.val = (false, vertices_369) then 23 else
  if p.val = (true, vertices_578) then 1 else
  if p.val = (true, vertices_44) then 2 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_324) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_232) then 20 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_448) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_297), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_232), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_115), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 4 5 6 232
cert_row_4 1 0 1 4 5 8 614 98 1
cert_row_4 2 0 3 5 7 8 850 82 3
cert_row_4 3 1 3 6 7 8 916 388 1
cert_rows
cert_pivot_2 2 4 0 1
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_5 0 1 0 1 4 5 98 614 1
cert_coverFacet 1 850
cert_cover_5 1 2 0 3 5 7 82 850 3
cert_coverFacet 2 236
cert_cover_5 2 0 1 2 4 5 44 236 3
cert_coverFacet 3 556
cert_cover_2 3 2 1 4 8 44 556 3
cert_coverFacet 4 916
cert_cover_5 4 3 1 3 6 7 388 916 1
cert_coverFacet 5 452
cert_cover_2 5 5 1 6 7 196 452 3
cert_coverFacet 6 836
cert_cover_2 6 5 1 7 8 324 836 3
cert_coverFacet 7 488
cert_cover_5 7 0 2 4 5 7 232 488 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0047

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e11q2_0048.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0048

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 173, 313, 601, 649, 465, 417, 654, 230, 358, 774, 850, 572, 820, 480, 25, 41, 137, 521, 81, 273, 161, 289, 193, 577, 385, 641, 102, 134, 262, 518, 194, 322, 578, 642, 770, 44, 140, 524, 564, 164, 292, 772, 56, 536, 648, 304, 336, 592, 784, 224, 352, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_173, vertices_313, vertices_601, vertices_649, vertices_465, vertices_417, vertices_654, vertices_230, vertices_358, vertices_774, vertices_850, vertices_572, vertices_820, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_137, vertices_521, vertices_81, vertices_273, vertices_161, vertices_289, vertices_193, vertices_577, vertices_385, vertices_641, vertices_102, vertices_134, vertices_262, vertices_518, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_44, vertices_140, vertices_524, vertices_564, vertices_164, vertices_292, vertices_772, vertices_56, vertices_536, vertices_648, vertices_304, vertices_336, vertices_592, vertices_784, vertices_224, vertices_352, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_173), (false, vertices_313), (false, vertices_601), (false, vertices_649), (false, vertices_465), (false, vertices_417), (true, vertices_102), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_322), (true, vertices_770), (true, vertices_524), (true, vertices_564), (true, vertices_292), (true, vertices_772), (true, vertices_784), (true, vertices_224), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 14 else
  if p.val = (false, vertices_173) then 17 else
  if p.val = (false, vertices_313) then 20 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_649) then 0 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (false, vertices_417) then 1 else
  if p.val = (true, vertices_102) then 15 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_564) then 18 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_352) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_649), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_417), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_102), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_564), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 134 2
cert_row_4 1 0 3 5 7 8 850 322 1
cert_row_2 2 1 3 4 8 564
cert_row_2 3 0 1 4 5 102
cert_rows
cert_pivot_2 2 7 3 0
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 134 654 2
cert_coverFacet 1 230
cert_cover_5 1 3 0 1 4 6 102 230 3
cert_coverFacet 2 358
cert_cover_5 2 3 0 1 4 7 102 358 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 850
cert_cover_5 4 1 0 3 5 7 322 850 1
cert_coverFacet 5 572
cert_cover_5 5 2 1 2 3 4 44 572 2
cert_coverFacet 6 820
cert_cover_5 6 2 1 3 4 7 564 820 3
cert_coverFacet 7 480
cert_cover_2 7 5 4 6 7 224 480 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0048

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e11q2_0049.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0049

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [167, 295, 787, 707, 389, 601, 465, 682, 802, 124, 172, 716, 372, 452, 824, 39, 131, 259, 515, 133, 261, 81, 273, 529, 193, 577, 385, 162, 290, 546, 642, 770, 44, 76, 140, 116, 164, 292, 196, 324, 388, 56, 88, 536, 168, 552, 584, 648, 304, 336, 784, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_167, vertices_295, vertices_787, vertices_707, vertices_389, vertices_601, vertices_465, vertices_682, vertices_802, vertices_124, vertices_172, vertices_716, vertices_372, vertices_452, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_39, vertices_131, vertices_259, vertices_515, vertices_133, vertices_261, vertices_81, vertices_273, vertices_529, vertices_193, vertices_577, vertices_385, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_44, vertices_76, vertices_140, vertices_116, vertices_164, vertices_292, vertices_196, vertices_324, vertices_388, vertices_56, vertices_88, vertices_536, vertices_168, vertices_552, vertices_584, vertices_648, vertices_304, vertices_336, vertices_784, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_167), (false, vertices_295), (false, vertices_787), (false, vertices_707), (false, vertices_389), (false, vertices_601), (false, vertices_465), (true, vertices_546), (true, vertices_44), (true, vertices_76), (true, vertices_140), (true, vertices_116), (true, vertices_196), (true, vertices_324), (true, vertices_56), (true, vertices_168), (true, vertices_552), (true, vertices_648), (true, vertices_304), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 23 13 15 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_167) then 20 else
  if p.val = (false, vertices_295) then 21 else
  if p.val = (false, vertices_787) then 16 else
  if p.val = (false, vertices_707) then 22 else
  if p.val = (false, vertices_389) then 0 else
  if p.val = (false, vertices_601) then 14 else
  if p.val = (false, vertices_465) then 17 else
  if p.val = (true, vertices_546) then 1 else
  if p.val = (true, vertices_44) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_116) then 18 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_324) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_168) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 15 => Sum.inl 3
  | 16 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_116), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_167), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 23 => Sum.inl 1
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 8 682 162 1
cert_row_4 1 1 2 5 6 8 716 76 3
cert_row_2 2 1 3 4 5 116
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 682
cert_cover_5 0 0 0 2 4 6 162 682 1
cert_coverFacet 1 802
cert_cover_2 1 4 0 7 8 290 802 3
cert_coverFacet 2 124
cert_cover_5 2 2 1 2 3 4 44 124 2
cert_coverFacet 3 172
cert_cover_2 3 2 1 4 6 44 172 3
cert_coverFacet 4 716
cert_cover_5 4 1 1 2 5 6 76 716 3
cert_coverFacet 5 372
cert_cover_5 5 2 1 3 4 7 116 372 3
cert_coverFacet 6 452
cert_cover_2 6 5 1 6 7 196 452 3
cert_coverFacet 7 824
cert_cover_5 7 3 2 3 4 7 56 824 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0049

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m15e11q2_0050.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0050

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 173, 781, 421, 713, 465, 62, 542, 358, 774, 114, 722, 696, 368, 432, 13, 165, 261, 137, 521, 193, 321, 577, 385, 769, 30, 38, 262, 518, 50, 82, 530, 98, 322, 578, 770, 44, 524, 292, 772, 56, 536, 168, 648, 112, 176, 304, 208, 336, 400, 656, 352, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_173, vertices_781, vertices_421, vertices_713, vertices_465, vertices_62, vertices_542, vertices_358, vertices_774, vertices_114, vertices_722, vertices_696, vertices_368, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_165, vertices_261, vertices_137, vertices_521, vertices_193, vertices_321, vertices_577, vertices_385, vertices_769, vertices_30, vertices_38, vertices_262, vertices_518, vertices_50, vertices_82, vertices_530, vertices_98, vertices_322, vertices_578, vertices_770, vertices_44, vertices_524, vertices_292, vertices_772, vertices_56, vertices_536, vertices_168, vertices_648, vertices_112, vertices_176, vertices_304, vertices_208, vertices_336, vertices_400, vertices_656, vertices_352, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_173), (false, vertices_781), (false, vertices_421), (false, vertices_713), (false, vertices_465), (true, vertices_30), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_50), (true, vertices_82), (true, vertices_530), (true, vertices_98), (true, vertices_56), (true, vertices_536), (true, vertices_112), (true, vertices_176), (true, vertices_304), (true, vertices_656), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 15 else
  if p.val = (false, vertices_173) then 18 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_421) then 20 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (true, vertices_30) then 16 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_98) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_352) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_30), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 5 7 358 38 3
cert_row_2 1 0 1 2 3 30
cert_row_4 2 0 3 5 6 8 722 82 3
cert_row_4 3 2 3 4 6 8 696 56 3
cert_rows
cert_pivot_2 7 1 0 2
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 1 0 1 2 4 30 62 3
cert_coverFacet 1 542
cert_cover_5 1 1 0 1 2 8 30 542 3
cert_coverFacet 2 358
cert_cover_5 2 0 0 1 4 5 38 358 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 114
cert_cover_2 4 3 0 4 5 50 114 3
cert_coverFacet 5 722
cert_cover_5 5 2 0 3 5 6 82 722 3
cert_coverFacet 6 696
cert_cover_5 6 3 2 3 4 6 56 696 3
cert_coverFacet 7 368
cert_cover_2 7 4 3 5 7 112 368 3
cert_coverFacet 8 432
cert_cover_2 8 4 3 6 7 176 432 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0050

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m15e11q2_0051.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0051

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 837, 617, 689, 465, 225, 590, 142, 406, 774, 186, 570, 364, 428, 480, 145, 273, 529, 97, 161, 545, 193, 321, 577, 769, 14, 134, 262, 518, 58, 138, 522, 146, 274, 530, 770, 300, 76, 140, 324, 580, 388, 772, 104, 168, 552, 584, 176, 560, 400, 224, 352, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_837, vertices_617, vertices_689, vertices_465, vertices_225, vertices_590, vertices_142, vertices_406, vertices_774, vertices_186, vertices_570, vertices_364, vertices_428, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_145, vertices_273, vertices_529, vertices_97, vertices_161, vertices_545, vertices_193, vertices_321, vertices_577, vertices_769, vertices_14, vertices_134, vertices_262, vertices_518, vertices_58, vertices_138, vertices_522, vertices_146, vertices_274, vertices_530, vertices_770, vertices_300, vertices_76, vertices_140, vertices_324, vertices_580, vertices_388, vertices_772, vertices_104, vertices_168, vertices_552, vertices_584, vertices_176, vertices_560, vertices_400, vertices_224, vertices_352, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_837), (false, vertices_617), (false, vertices_689), (false, vertices_465), (false, vertices_225), (true, vertices_14), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_58), (true, vertices_138), (true, vertices_522), (true, vertices_146), (true, vertices_300), (true, vertices_76), (true, vertices_140), (true, vertices_388), (true, vertices_168), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 15 else
  if p.val = (false, vertices_837) then 18 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_689) then 23 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (false, vertices_225) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_58) then 16 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_146) then 7 else
  if p.val = (true, vertices_300) then 19 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_140) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_352) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_225), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_58), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_300), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 14 3
cert_row_4 1 0 1 3 6 7 406 134 2
cert_row_2 2 1 2 4 7 300
cert_row_2 3 0 2 3 4 58
cert_rows
cert_pivot_2 5 6 1 0
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 14 590 3
cert_coverFacet 1 142
cert_cover_2 1 1 0 2 6 14 142 3
cert_coverFacet 2 406
cert_cover_5 2 1 0 1 3 6 134 406 2
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 186
cert_cover_5 4 3 0 2 3 6 58 186 3
cert_coverFacet 5 570
cert_cover_5 5 3 0 2 3 8 58 570 3
cert_coverFacet 6 364
cert_cover_5 6 2 1 2 4 5 300 364 3
cert_coverFacet 7 428
cert_cover_5 7 2 1 2 4 6 300 428 3
cert_coverFacet 8 480
cert_cover_2 8 5 4 6 7 224 480 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0051

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m15e11q2_0052.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0052

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [155, 531, 707, 541, 457, 777, 865, 118, 598, 178, 482, 412, 812, 436, 612, 19, 131, 515, 25, 137, 265, 521, 529, 193, 321, 577, 769, 86, 50, 146, 530, 98, 162, 194, 578, 28, 268, 524, 52, 404, 532, 100, 292, 548, 580, 152, 392, 776, 176, 352, 608, 416, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_155, vertices_531, vertices_707, vertices_541, vertices_457, vertices_777, vertices_865, vertices_118, vertices_598, vertices_178, vertices_482, vertices_412, vertices_812, vertices_436, vertices_612] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_515, vertices_25, vertices_137, vertices_265, vertices_521, vertices_529, vertices_193, vertices_321, vertices_577, vertices_769, vertices_86, vertices_50, vertices_146, vertices_530, vertices_98, vertices_162, vertices_194, vertices_578, vertices_28, vertices_268, vertices_524, vertices_52, vertices_404, vertices_532, vertices_100, vertices_292, vertices_548, vertices_580, vertices_152, vertices_392, vertices_776, vertices_176, vertices_352, vertices_608, vertices_416, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_155), (false, vertices_531), (false, vertices_707), (false, vertices_541), (false, vertices_457), (false, vertices_777), (false, vertices_865), (true, vertices_86), (true, vertices_50), (true, vertices_98), (true, vertices_162), (true, vertices_268), (true, vertices_52), (true, vertices_404), (true, vertices_100), (true, vertices_292), (true, vertices_548), (true, vertices_580), (true, vertices_176), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_155) then 14 else
  if p.val = (false, vertices_531) then 0 else
  if p.val = (false, vertices_707) then 15 else
  if p.val = (false, vertices_541) then 18 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_777) then 1 else
  if p.val = (false, vertices_865) then 24 else
  if p.val = (true, vertices_86) then 16 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_404) then 19 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_416) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_531), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_155), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_86), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_404), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 4 7 8 812 268 2
cert_row_4 1 0 4 5 6 7 482 98 3
cert_row_2 2 0 1 3 5 86
cert_row_2 3 1 3 6 7 404
cert_rows
cert_pivot_2 2 4 0 1
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 2 0 1 3 4 86 118 3
cert_coverFacet 1 598
cert_cover_5 1 2 0 1 3 8 86 598 3
cert_coverFacet 2 178
cert_cover_2 2 3 0 4 6 50 178 3
cert_coverFacet 3 482
cert_cover_5 3 1 0 4 5 6 98 482 3
cert_coverFacet 4 412
cert_cover_5 4 3 1 2 3 6 28 412 3
cert_coverFacet 5 812
cert_cover_5 5 0 1 2 4 7 268 812 2
cert_coverFacet 6 436
cert_cover_5 6 3 1 3 4 6 52 436 3
cert_coverFacet 7 612
cert_cover_2 7 4 1 5 8 100 612 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0052

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m15e11q2_0053.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0053

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 285, 557, 453, 581, 537, 913, 614, 186, 682, 370, 466, 364, 312, 664, 13, 69, 261, 517, 25, 521, 273, 529, 193, 577, 385, 641, 170, 50, 338, 146, 98, 546, 194, 578, 642, 44, 268, 100, 548, 324, 580, 56, 152, 280, 536, 296, 552, 648, 304, 400, 656, 352, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_285, vertices_557, vertices_453, vertices_581, vertices_537, vertices_913, vertices_614, vertices_186, vertices_682, vertices_370, vertices_466, vertices_364, vertices_312, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_261, vertices_517, vertices_25, vertices_521, vertices_273, vertices_529, vertices_193, vertices_577, vertices_385, vertices_641, vertices_170, vertices_50, vertices_338, vertices_146, vertices_98, vertices_546, vertices_194, vertices_578, vertices_642, vertices_44, vertices_268, vertices_100, vertices_548, vertices_324, vertices_580, vertices_56, vertices_152, vertices_280, vertices_536, vertices_296, vertices_552, vertices_648, vertices_304, vertices_400, vertices_656, vertices_352, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_285), (false, vertices_557), (false, vertices_453), (false, vertices_581), (false, vertices_537), (false, vertices_913), (true, vertices_170), (true, vertices_50), (true, vertices_338), (true, vertices_146), (true, vertices_98), (true, vertices_546), (true, vertices_100), (true, vertices_56), (true, vertices_152), (true, vertices_296), (true, vertices_648), (true, vertices_304), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 13 17 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 20 else
  if p.val = (false, vertices_285) then 14 else
  if p.val = (false, vertices_557) then 15 else
  if p.val = (false, vertices_453) then 16 else
  if p.val = (false, vertices_581) then 0 else
  if p.val = (false, vertices_537) then 1 else
  if p.val = (false, vertices_913) then 23 else
  if p.val = (true, vertices_170) then 18 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_338) then 21 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_352) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_581), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_537), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(true, vertices_170), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_338), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 5 7 338
cert_row_2 1 0 2 4 6 170
cert_row_4 2 0 1 4 5 8 614 98 1
cert_row_4 3 1 2 4 5 7 364 44 3
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_5 0 2 0 1 4 5 98 614 1
cert_coverFacet 1 186
cert_cover_5 1 1 0 2 3 4 170 186 2
cert_coverFacet 2 682
cert_cover_5 2 1 0 2 4 8 170 682 3
cert_coverFacet 3 370
cert_cover_5 3 0 0 3 4 5 50 370 3
cert_coverFacet 4 466
cert_cover_5 4 0 0 3 5 6 338 466 3
cert_coverFacet 5 364
cert_cover_5 5 3 1 2 4 5 44 364 3
cert_coverFacet 6 312
cert_cover_2 6 3 2 4 7 56 312 3
cert_coverFacet 7 664
cert_cover_2 7 3 2 6 8 152 664 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0053

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m15e11q2_0054.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0054

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 589, 781, 313, 233, 625, 334, 662, 198, 774, 458, 434, 740, 424, 688, 525, 41, 73, 265, 49, 273, 529, 97, 577, 769, 70, 134, 262, 518, 330, 146, 274, 530, 194, 386, 770, 76, 268, 196, 580, 644, 772, 168, 296, 200, 392, 176, 304, 560, 656, 224, 608, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_589, vertices_781, vertices_313, vertices_233, vertices_625, vertices_334, vertices_662, vertices_198, vertices_774, vertices_458, vertices_434, vertices_740, vertices_424, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_525, vertices_41, vertices_73, vertices_265, vertices_49, vertices_273, vertices_529, vertices_97, vertices_577, vertices_769, vertices_70, vertices_134, vertices_262, vertices_518, vertices_330, vertices_146, vertices_274, vertices_530, vertices_194, vertices_386, vertices_770, vertices_76, vertices_268, vertices_196, vertices_580, vertices_644, vertices_772, vertices_168, vertices_296, vertices_200, vertices_392, vertices_176, vertices_304, vertices_560, vertices_656, vertices_224, vertices_608, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_589), (false, vertices_781), (false, vertices_313), (false, vertices_233), (false, vertices_625), (true, vertices_70), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_330), (true, vertices_146), (true, vertices_194), (true, vertices_386), (true, vertices_196), (true, vertices_644), (true, vertices_392), (true, vertices_176), (true, vertices_656), (true, vertices_416), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 15 else
  if p.val = (false, vertices_589) then 18 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_313) then 21 else
  if p.val = (false, vertices_233) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_330) then 16 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_656) then 11 else
  if p.val = (true, vertices_416) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_330), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 7 330
cert_row_4 1 0 3 4 6 7 434 146 2
cert_row_4 2 0 1 3 6 8 662 134 2
cert_row_4 3 1 4 5 6 8 740 196 1
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 5 70 334 2
cert_coverFacet 1 662
cert_cover_5 1 2 0 1 3 6 134 662 2
cert_coverFacet 2 198
cert_cover_2 2 1 0 5 6 70 198 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 458
cert_cover_5 4 0 0 2 5 6 330 458 3
cert_coverFacet 5 434
cert_cover_5 5 1 0 3 4 6 146 434 2
cert_coverFacet 6 740
cert_cover_5 6 3 1 4 5 6 196 740 1
cert_coverFacet 7 424
cert_cover_2 7 4 2 6 7 168 424 3
cert_coverFacet 8 688
cert_cover_2 8 4 3 6 8 176 688 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0054

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m15e11q2_0055.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0055

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 709, 345, 665, 201, 865, 662, 614, 166, 186, 314, 802, 428, 460, 356, 25, 73, 137, 273, 529, 193, 321, 577, 641, 769, 38, 134, 518, 58, 146, 274, 530, 162, 290, 546, 770, 396, 100, 164, 292, 196, 324, 580, 644, 152, 280, 168, 296, 200, 328, 656, 352, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_709, vertices_345, vertices_665, vertices_201, vertices_865, vertices_662, vertices_614, vertices_166, vertices_186, vertices_314, vertices_802, vertices_428, vertices_460, vertices_356] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_137, vertices_273, vertices_529, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_38, vertices_134, vertices_518, vertices_58, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_770, vertices_396, vertices_100, vertices_164, vertices_292, vertices_196, vertices_324, vertices_580, vertices_644, vertices_152, vertices_280, vertices_168, vertices_296, vertices_200, vertices_328, vertices_656, vertices_352, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_709), (false, vertices_345), (false, vertices_665), (false, vertices_201), (false, vertices_865), (true, vertices_38), (true, vertices_134), (true, vertices_518), (true, vertices_58), (true, vertices_146), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_396), (true, vertices_100), (true, vertices_164), (true, vertices_292), (true, vertices_324), (true, vertices_168), (true, vertices_296)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 15 else
  if p.val = (false, vertices_709) then 18 else
  if p.val = (false, vertices_345) then 21 else
  if p.val = (false, vertices_665) then 22 else
  if p.val = (false, vertices_201) then 0 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_58) then 16 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_396) then 19 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_164) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_324) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_296) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_201), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_58), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_396), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 7 396
cert_row_2 1 0 2 3 4 58
cert_row_4 2 0 1 3 6 8 662 134 2
cert_row_4 3 0 1 4 5 8 614 38 3
cert_rows
cert_pivot_2 7 2 3 0
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 2 0 1 3 6 134 662 2
cert_coverFacet 1 614
cert_cover_5 1 3 0 1 4 5 38 614 3
cert_coverFacet 2 166
cert_cover_2 2 1 0 4 6 38 166 3
cert_coverFacet 3 186
cert_cover_5 3 1 0 2 3 6 58 186 3
cert_coverFacet 4 314
cert_cover_5 4 1 0 2 3 7 58 314 3
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 428
cert_cover_5 6 0 1 2 4 6 396 428 2
cert_coverFacet 7 460
cert_cover_5 7 0 1 2 5 6 396 460 2
cert_coverFacet 8 356
cert_cover_2 8 4 1 5 7 100 356 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0055

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m15e11q2_0056.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0056

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 613, 665, 425, 553, 849, 353, 30, 206, 790, 838, 154, 482, 572, 236, 41, 137, 521, 145, 273, 529, 97, 289, 545, 321, 577, 385, 14, 22, 70, 774, 26, 138, 146, 274, 194, 322, 386, 28, 44, 204, 532, 100, 548, 580, 152, 536, 168, 552, 784, 224, 352, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_613, vertices_665, vertices_425, vertices_553, vertices_849, vertices_353, vertices_30, vertices_206, vertices_790, vertices_838, vertices_154, vertices_482, vertices_572, vertices_236] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_137, vertices_521, vertices_145, vertices_273, vertices_529, vertices_97, vertices_289, vertices_545, vertices_321, vertices_577, vertices_385, vertices_14, vertices_22, vertices_70, vertices_774, vertices_26, vertices_138, vertices_146, vertices_274, vertices_194, vertices_322, vertices_386, vertices_28, vertices_44, vertices_204, vertices_532, vertices_100, vertices_548, vertices_580, vertices_152, vertices_536, vertices_168, vertices_552, vertices_784, vertices_224, vertices_352, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_613), (false, vertices_665), (false, vertices_425), (false, vertices_553), (false, vertices_849), (false, vertices_353), (true, vertices_14), (true, vertices_22), (true, vertices_70), (true, vertices_774), (true, vertices_26), (true, vertices_138), (true, vertices_194), (true, vertices_322), (true, vertices_28), (true, vertices_44), (true, vertices_204), (true, vertices_532), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 14 else
  if p.val = (false, vertices_613) then 17 else
  if p.val = (false, vertices_665) then 20 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_849) then 23 else
  if p.val = (false, vertices_353) then 1 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_22) then 3 else
  if p.val = (true, vertices_70) then 4 else
  if p.val = (true, vertices_774) then 15 else
  if p.val = (true, vertices_26) then 5 else
  if p.val = (true, vertices_138) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_322) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_44) then 10 else
  if p.val = (true, vertices_204) then 18 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_224) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_353), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 4 8 572 28 3
cert_row_2 1 0 1 7 8 774
cert_row_2 2 1 2 5 6 204
cert_row_4 3 0 4 5 6 7 482 194 1
cert_rows
cert_pivot_2 3 8 1 0
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 206
cert_cover_5 1 2 0 1 2 5 14 206 3
cert_coverFacet 2 790
cert_cover_5 2 1 0 1 3 7 22 790 3
cert_coverFacet 3 838
cert_cover_5 3 1 0 1 5 7 70 838 3
cert_coverFacet 4 154
cert_cover_2 4 2 0 3 6 26 154 3
cert_coverFacet 5 482
cert_cover_5 5 3 0 4 5 6 194 482 1
cert_coverFacet 6 572
cert_cover_5 6 0 1 2 3 4 28 572 3
cert_coverFacet 7 236
cert_cover_5 7 2 1 2 4 5 44 236 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0056

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e11q2_0057.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0057

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [583, 779, 211, 403, 397, 525, 229, 818, 594, 124, 604, 172, 568, 936, 496, 147, 67, 259, 515, 13, 69, 133, 517, 265, 521, 193, 385, 82, 274, 530, 578, 770, 92, 44, 140, 524, 100, 164, 580, 56, 536, 168, 552, 392, 776, 112, 304, 560, 208, 592, 400, 224, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_583, vertices_779, vertices_211, vertices_403, vertices_397, vertices_525, vertices_229, vertices_818, vertices_594, vertices_124, vertices_604, vertices_172, vertices_568, vertices_936, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_147, vertices_67, vertices_259, vertices_515, vertices_13, vertices_69, vertices_133, vertices_517, vertices_265, vertices_521, vertices_193, vertices_385, vertices_82, vertices_274, vertices_530, vertices_578, vertices_770, vertices_92, vertices_44, vertices_140, vertices_524, vertices_100, vertices_164, vertices_580, vertices_56, vertices_536, vertices_168, vertices_552, vertices_392, vertices_776, vertices_112, vertices_304, vertices_560, vertices_208, vertices_592, vertices_400, vertices_224, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_583), (false, vertices_779), (false, vertices_211), (false, vertices_403), (false, vertices_397), (false, vertices_525), (false, vertices_229), (true, vertices_530), (true, vertices_92), (true, vertices_44), (true, vertices_56), (true, vertices_536), (true, vertices_168), (true, vertices_552), (true, vertices_112), (true, vertices_304), (true, vertices_560), (true, vertices_592), (true, vertices_416), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 13 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_583) then 18 else
  if p.val = (false, vertices_779) then 14 else
  if p.val = (false, vertices_211) then 19 else
  if p.val = (false, vertices_403) then 20 else
  if p.val = (false, vertices_397) then 15 else
  if p.val = (false, vertices_525) then 0 else
  if p.val = (false, vertices_229) then 22 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_92) then 16 else
  if p.val = (true, vertices_44) then 2 else
  if p.val = (true, vertices_56) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_168) then 5 else
  if p.val = (true, vertices_552) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_304) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_416) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_92), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 5 92
cert_row_4 1 0 3 4 7 8 818 274 2
cert_row_4 2 2 4 6 7 8 936 168 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 1 0 2 3
cert_heightProof 4
cert_coverFacet 0 818
cert_cover_5 0 1 0 3 4 7 274 818 2
cert_coverFacet 1 594
cert_cover_2 1 3 0 5 8 82 594 3
cert_coverFacet 2 124
cert_cover_5 2 0 1 2 3 4 92 124 3
cert_coverFacet 3 604
cert_cover_5 3 0 1 2 3 8 92 604 3
cert_coverFacet 4 172
cert_cover_2 4 2 1 4 6 44 172 3
cert_coverFacet 5 568
cert_cover_2 5 3 2 4 8 56 568 3
cert_coverFacet 6 936
cert_cover_5 6 2 2 4 6 7 168 936 3
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 112 496 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0057

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e11q2_0058.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0058

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 53, 597, 357, 569, 929, 454, 218, 602, 682, 898, 316, 412, 212, 424, 21, 37, 69, 49, 529, 289, 545, 321, 577, 769, 90, 138, 522, 194, 322, 578, 386, 642, 770, 284, 52, 84, 148, 292, 196, 324, 388, 56, 152, 536, 168, 296, 552, 392, 208, 592, 416, 672, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_53, vertices_597, vertices_357, vertices_569, vertices_929, vertices_454, vertices_218, vertices_602, vertices_682, vertices_898, vertices_316, vertices_412, vertices_212, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_69, vertices_49, vertices_529, vertices_289, vertices_545, vertices_321, vertices_577, vertices_769, vertices_90, vertices_138, vertices_522, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_284, vertices_52, vertices_84, vertices_148, vertices_292, vertices_196, vertices_324, vertices_388, vertices_56, vertices_152, vertices_536, vertices_168, vertices_296, vertices_552, vertices_392, vertices_208, vertices_592, vertices_416, vertices_672, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_53), (false, vertices_597), (false, vertices_357), (false, vertices_569), (false, vertices_929), (true, vertices_90), (true, vertices_138), (true, vertices_522), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_284), (true, vertices_148), (true, vertices_196), (true, vertices_388), (true, vertices_152), (true, vertices_168), (true, vertices_296), (true, vertices_392), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 15 else
  if p.val = (false, vertices_53) then 0 else
  if p.val = (false, vertices_597) then 18 else
  if p.val = (false, vertices_357) then 19 else
  if p.val = (false, vertices_569) then 22 else
  if p.val = (false, vertices_929) then 25 else
  if p.val = (true, vertices_90) then 16 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_284) then 20 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_208) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_53), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_90), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_284), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 8 682 138 2
cert_row_4 1 0 1 5 6 7 454 194 1
cert_row_2 2 0 2 3 5 90
cert_row_2 3 1 2 3 7 284
cert_rows
cert_pivot_2 4 6 0 1
cert_heightProof 4
cert_coverFacet 0 454
cert_cover_5 0 1 0 1 5 6 194 454 1
cert_coverFacet 1 218
cert_cover_5 1 2 0 2 3 6 90 218 3
cert_coverFacet 2 602
cert_cover_5 2 2 0 2 3 8 90 602 3
cert_coverFacet 3 682
cert_cover_5 3 0 0 2 4 6 138 682 2
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 316
cert_cover_5 5 3 1 2 3 4 284 316 3
cert_coverFacet 6 412
cert_cover_5 6 3 1 2 3 6 284 412 3
cert_coverFacet 7 212
cert_cover_2 7 3 1 5 6 84 212 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0058

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e11q2_0059.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0059

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 157, 789, 709, 433, 481, 782, 122, 346, 554, 738, 284, 684, 184, 368, 21, 133, 517, 145, 273, 417, 193, 321, 577, 769, 90, 42, 266, 522, 98, 546, 322, 578, 770, 28, 140, 268, 524, 276, 644, 772, 56, 152, 280, 168, 552, 112, 176, 304, 336, 224, 352, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_157, vertices_789, vertices_709, vertices_433, vertices_481, vertices_782, vertices_122, vertices_346, vertices_554, vertices_738, vertices_284, vertices_684, vertices_184, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_517, vertices_145, vertices_273, vertices_417, vertices_193, vertices_321, vertices_577, vertices_769, vertices_90, vertices_42, vertices_266, vertices_522, vertices_98, vertices_546, vertices_322, vertices_578, vertices_770, vertices_28, vertices_140, vertices_268, vertices_524, vertices_276, vertices_644, vertices_772, vertices_56, vertices_152, vertices_280, vertices_168, vertices_552, vertices_112, vertices_176, vertices_304, vertices_336, vertices_224, vertices_352, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_157), (false, vertices_789), (false, vertices_709), (false, vertices_433), (false, vertices_481), (true, vertices_90), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_98), (true, vertices_546), (true, vertices_268), (true, vertices_524), (true, vertices_56), (true, vertices_280), (true, vertices_168), (true, vertices_552), (true, vertices_112), (true, vertices_336), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 22 23 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 15 else
  if p.val = (false, vertices_157) then 18 else
  if p.val = (false, vertices_789) then 19 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_90) then 16 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_90), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 5 90
cert_row_4 1 0 1 2 7 8 782 266 1
cert_row_4 2 0 4 5 6 8 738 98 3
cert_row_4 3 1 2 4 6 8 684 140 2
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 266 782 1
cert_coverFacet 1 122
cert_cover_5 1 0 0 2 3 4 90 122 3
cert_coverFacet 2 346
cert_cover_5 2 0 0 2 3 7 90 346 3
cert_coverFacet 3 554
cert_cover_2 3 2 0 4 8 42 554 3
cert_coverFacet 4 738
cert_cover_5 4 2 0 4 5 6 98 738 3
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 684
cert_cover_5 6 3 1 2 4 6 140 684 2
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coverFacet 8 368
cert_cover_2 8 4 3 5 7 112 368 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0059

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e11q2_0060.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0060

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 173, 653, 309, 837, 481, 598, 570, 346, 458, 650, 556, 564, 340, 440, 141, 37, 261, 517, 161, 289, 193, 321, 577, 641, 26, 330, 138, 522, 82, 530, 194, 578, 642, 44, 524, 52, 84, 276, 532, 548, 324, 580, 56, 280, 168, 552, 392, 648, 304, 560, 336, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_173, vertices_653, vertices_309, vertices_837, vertices_481, vertices_598, vertices_570, vertices_346, vertices_458, vertices_650, vertices_556, vertices_564, vertices_340, vertices_440] (by decide +kernel)
  polygons := literalFinset [vertices_141, vertices_37, vertices_261, vertices_517, vertices_161, vertices_289, vertices_193, vertices_321, vertices_577, vertices_641, vertices_26, vertices_330, vertices_138, vertices_522, vertices_82, vertices_530, vertices_194, vertices_578, vertices_642, vertices_44, vertices_524, vertices_52, vertices_84, vertices_276, vertices_532, vertices_548, vertices_324, vertices_580, vertices_56, vertices_280, vertices_168, vertices_552, vertices_392, vertices_648, vertices_304, vertices_560, vertices_336, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_173), (false, vertices_653), (false, vertices_309), (false, vertices_837), (false, vertices_481), (true, vertices_26), (true, vertices_330), (true, vertices_138), (true, vertices_522), (true, vertices_82), (true, vertices_530), (true, vertices_84), (true, vertices_532), (true, vertices_548), (true, vertices_56), (true, vertices_280), (true, vertices_552), (true, vertices_392), (true, vertices_560), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 20 17 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 15 else
  if p.val = (false, vertices_173) then 18 else
  if p.val = (false, vertices_653) then 19 else
  if p.val = (false, vertices_309) then 21 else
  if p.val = (false, vertices_837) then 22 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_330) then 16 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_336) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_330), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 8 598 82 1
cert_row_2 1 0 2 5 7 330
cert_row_4 2 0 2 3 4 8 570 26 3
cert_row_4 3 2 3 4 6 7 440 56 3
cert_rows
cert_pivot_2 1 5 0 2
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 82 598 1
cert_coverFacet 1 570
cert_cover_5 1 2 0 2 3 4 26 570 3
cert_coverFacet 2 346
cert_cover_5 2 1 0 2 3 5 26 346 3
cert_coverFacet 3 458
cert_cover_5 3 1 0 2 5 6 330 458 3
cert_coverFacet 4 650
cert_cover_2 4 2 0 6 8 138 650 3
cert_coverFacet 5 556
cert_cover_2 5 2 1 4 8 44 556 3
cert_coverFacet 6 564
cert_cover_2 6 3 1 4 8 52 564 3
cert_coverFacet 7 340
cert_cover_2 7 3 1 5 7 84 340 3
cert_coverFacet 8 440
cert_cover_5 8 3 2 3 4 6 56 440 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0060

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e11q2_0061.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0061

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 29, 653, 309, 229, 57, 617, 214, 342, 410, 906, 866, 156, 356, 824, 13, 21, 37, 133, 25, 41, 521, 49, 97, 193, 577, 641, 86, 394, 146, 274, 194, 322, 578, 642, 770, 28, 140, 148, 276, 100, 292, 196, 324, 56, 152, 280, 552, 648, 776, 304, 352, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_29, vertices_653, vertices_309, vertices_229, vertices_57, vertices_617, vertices_214, vertices_342, vertices_410, vertices_906, vertices_866, vertices_156, vertices_356, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_37, vertices_133, vertices_25, vertices_41, vertices_521, vertices_49, vertices_97, vertices_193, vertices_577, vertices_641, vertices_86, vertices_394, vertices_146, vertices_274, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_28, vertices_140, vertices_148, vertices_276, vertices_100, vertices_292, vertices_196, vertices_324, vertices_56, vertices_152, vertices_280, vertices_552, vertices_648, vertices_776, vertices_304, vertices_352, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_29), (false, vertices_653), (false, vertices_309), (false, vertices_229), (false, vertices_57), (false, vertices_617), (true, vertices_86), (true, vertices_394), (true, vertices_146), (true, vertices_274), (true, vertices_322), (true, vertices_770), (true, vertices_148), (true, vertices_324), (true, vertices_152), (true, vertices_280), (true, vertices_776), (true, vertices_352), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 13 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 18 else
  if p.val = (false, vertices_29) then 0 else
  if p.val = (false, vertices_653) then 14 else
  if p.val = (false, vertices_309) then 21 else
  if p.val = (false, vertices_229) then 22 else
  if p.val = (false, vertices_57) then 1 else
  if p.val = (false, vertices_617) then 15 else
  if p.val = (true, vertices_86) then 19 else
  if p.val = (true, vertices_394) then 16 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_800) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_29), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_57), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inl 2
  | 14 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_394), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_86), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 5 86
cert_row_2 1 0 2 6 7 394
cert_row_4 2 0 4 5 7 8 866 322 1
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 6 86 214 3
cert_coverFacet 1 342
cert_cover_5 1 0 0 1 3 7 86 342 3
cert_coverFacet 2 410
cert_cover_5 2 1 0 2 3 6 394 410 2
cert_coverFacet 3 906
cert_cover_5 3 1 0 2 6 8 394 906 3
cert_coverFacet 4 866
cert_cover_5 4 2 0 4 5 7 322 866 1
cert_coverFacet 5 156
cert_cover_2 5 2 1 3 6 28 156 3
cert_coverFacet 6 356
cert_cover_2 6 4 1 5 7 100 356 3
cert_coverFacet 7 824
cert_cover_5 7 3 2 3 4 7 56 824 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0061

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m15e11q2_0062.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0062

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 403, 611, 675, 589, 901, 186, 306, 354, 124, 540, 372, 788, 920, 744, 547, 67, 131, 259, 69, 261, 517, 577, 385, 641, 50, 146, 274, 98, 162, 290, 322, 28, 76, 524, 116, 276, 532, 324, 772, 56, 152, 536, 104, 168, 584, 648, 304, 400, 784, 352, 608, 672, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_403, vertices_611, vertices_675, vertices_589, vertices_901, vertices_186, vertices_306, vertices_354, vertices_124, vertices_540, vertices_372, vertices_788, vertices_920, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_547, vertices_67, vertices_131, vertices_259, vertices_69, vertices_261, vertices_517, vertices_577, vertices_385, vertices_641, vertices_50, vertices_146, vertices_274, vertices_98, vertices_162, vertices_290, vertices_322, vertices_28, vertices_76, vertices_524, vertices_116, vertices_276, vertices_532, vertices_324, vertices_772, vertices_56, vertices_152, vertices_536, vertices_104, vertices_168, vertices_584, vertices_648, vertices_304, vertices_400, vertices_784, vertices_352, vertices_608, vertices_672, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_403), (false, vertices_611), (false, vertices_675), (false, vertices_589), (false, vertices_901), (true, vertices_50), (true, vertices_290), (true, vertices_28), (true, vertices_116), (true, vertices_276), (true, vertices_532), (true, vertices_56), (true, vertices_152), (true, vertices_536), (true, vertices_104), (true, vertices_168), (true, vertices_648), (true, vertices_304), (true, vertices_784), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 20 16 14 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 17 else
  if p.val = (false, vertices_403) then 21 else
  if p.val = (false, vertices_611) then 22 else
  if p.val = (false, vertices_675) then 23 else
  if p.val = (false, vertices_589) then 15 else
  if p.val = (false, vertices_901) then 18 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_290) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_116) then 19 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_56) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_784) then 12 else
  if p.val = (true, vertices_352) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_116), by decide +kernel⟩
  | 20 => Sum.inl 0
  | 21 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 4 5 116
cert_row_4 1 0 2 3 4 6 186 50 1
cert_row_4 2 2 3 6 7 8 920 152 3
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 1 0 3 2
cert_heightProof 4
cert_coverFacet 0 186
cert_cover_5 0 1 0 2 3 4 50 186 1
cert_coverFacet 1 306
cert_cover_2 1 3 0 4 7 50 306 3
cert_coverFacet 2 354
cert_cover_2 2 4 0 5 7 98 354 3
cert_coverFacet 3 124
cert_cover_5 3 0 1 2 3 4 28 124 3
cert_coverFacet 4 540
cert_cover_2 4 2 1 3 8 28 540 3
cert_coverFacet 5 372
cert_cover_5 5 0 1 3 4 7 116 372 3
cert_coverFacet 6 788
cert_cover_2 6 3 1 7 8 276 788 3
cert_coverFacet 7 920
cert_cover_5 7 2 2 3 6 7 152 920 3
cert_coverFacet 8 744
cert_cover_5 8 3 2 4 5 6 104 744 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0062

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m15e11q2_0063.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0063

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [551, 651, 307, 403, 809, 457, 118, 534, 658, 220, 668, 844, 612, 496, 864, 275, 35, 131, 515, 137, 265, 521, 289, 545, 385, 22, 38, 518, 50, 146, 530, 642, 156, 76, 524, 84, 532, 100, 548, 580, 200, 328, 648, 776, 112, 304, 208, 400, 656, 352, 608, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_551, vertices_651, vertices_307, vertices_403, vertices_809, vertices_457, vertices_118, vertices_534, vertices_658, vertices_220, vertices_668, vertices_844, vertices_612, vertices_496, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_275, vertices_35, vertices_131, vertices_515, vertices_137, vertices_265, vertices_521, vertices_289, vertices_545, vertices_385, vertices_22, vertices_38, vertices_518, vertices_50, vertices_146, vertices_530, vertices_642, vertices_156, vertices_76, vertices_524, vertices_84, vertices_532, vertices_100, vertices_548, vertices_580, vertices_200, vertices_328, vertices_648, vertices_776, vertices_112, vertices_304, vertices_208, vertices_400, vertices_656, vertices_352, vertices_608, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_551), (false, vertices_651), (false, vertices_307), (false, vertices_403), (false, vertices_809), (false, vertices_457), (true, vertices_22), (true, vertices_530), (true, vertices_156), (true, vertices_76), (true, vertices_524), (true, vertices_84), (true, vertices_532), (true, vertices_100), (true, vertices_580), (true, vertices_112), (true, vertices_208), (true, vertices_656), (true, vertices_352), (true, vertices_608), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 14 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_551) then 15 else
  if p.val = (false, vertices_651) then 18 else
  if p.val = (false, vertices_307) then 19 else
  if p.val = (false, vertices_403) then 20 else
  if p.val = (false, vertices_809) then 22 else
  if p.val = (false, vertices_457) then 23 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_156) then 16 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_656) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_832) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_156), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 5 118 22 3
cert_row_4 1 1 2 5 7 8 844 76 3
cert_row_2 2 1 2 3 6 156
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 8 1 3
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 0 0 1 3 4 22 118 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 658
cert_cover_2 2 3 0 6 8 146 658 3
cert_coverFacet 3 220
cert_cover_5 3 2 1 2 3 5 156 220 3
cert_coverFacet 4 668
cert_cover_5 4 2 1 2 3 8 156 668 3
cert_coverFacet 5 844
cert_cover_5 5 1 1 2 5 7 76 844 3
cert_coverFacet 6 612
cert_cover_2 6 4 1 5 8 100 612 3
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 112 496 3
cert_coverFacet 8 864
cert_cover_2 8 5 4 7 8 352 864 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0063

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m15e11q2_0064.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0064

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [355, 653, 185, 601, 305, 337, 737, 782, 230, 294, 710, 850, 412, 436, 792, 25, 137, 521, 49, 81, 273, 97, 161, 289, 321, 577, 641, 38, 198, 262, 518, 98, 290, 322, 578, 770, 140, 268, 524, 404, 164, 292, 644, 152, 280, 536, 776, 176, 304, 336, 592, 784, 224, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_355, vertices_653, vertices_185, vertices_601, vertices_305, vertices_337, vertices_737, vertices_782, vertices_230, vertices_294, vertices_710, vertices_850, vertices_412, vertices_436, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_521, vertices_49, vertices_81, vertices_273, vertices_97, vertices_161, vertices_289, vertices_321, vertices_577, vertices_641, vertices_38, vertices_198, vertices_262, vertices_518, vertices_98, vertices_290, vertices_322, vertices_578, vertices_770, vertices_140, vertices_268, vertices_524, vertices_404, vertices_164, vertices_292, vertices_644, vertices_152, vertices_280, vertices_536, vertices_776, vertices_176, vertices_304, vertices_336, vertices_592, vertices_784, vertices_224, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_355), (false, vertices_653), (false, vertices_185), (false, vertices_601), (false, vertices_305), (false, vertices_337), (false, vertices_737), (true, vertices_38), (true, vertices_198), (true, vertices_262), (true, vertices_518), (true, vertices_578), (true, vertices_770), (true, vertices_268), (true, vertices_404), (true, vertices_164), (true, vertices_292), (true, vertices_280), (true, vertices_776), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_355) then 14 else
  if p.val = (false, vertices_653) then 17 else
  if p.val = (false, vertices_185) then 20 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_305) then 0 else
  if p.val = (false, vertices_337) then 1 else
  if p.val = (false, vertices_737) then 24 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_198) then 15 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_404) then 18 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_784) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_305), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_337), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_198), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_404), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 262 2
cert_row_4 1 0 3 5 7 8 850 322 1
cert_row_2 2 0 1 5 6 198
cert_row_2 3 1 3 6 7 404
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 262 782 2
cert_coverFacet 1 230
cert_cover_5 1 2 0 1 4 5 38 230 3
cert_coverFacet 2 294
cert_cover_2 2 1 0 4 7 38 294 3
cert_coverFacet 3 710
cert_cover_5 3 2 0 1 5 8 198 710 3
cert_coverFacet 4 850
cert_cover_5 4 1 0 3 5 7 322 850 1
cert_coverFacet 5 412
cert_cover_5 5 3 1 2 3 6 140 412 2
cert_coverFacet 6 436
cert_cover_5 6 3 1 3 4 6 404 436 2
cert_coverFacet 7 792
cert_cover_2 7 3 2 7 8 280 792 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0064

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m15e11q2_0065.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0065

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 453, 841, 241, 593, 929, 46, 334, 678, 902, 58, 794, 188, 220, 600, 49, 81, 529, 161, 545, 193, 321, 577, 385, 769, 14, 38, 646, 262, 26, 42, 266, 50, 530, 546, 770, 156, 44, 76, 164, 196, 324, 388, 56, 88, 536, 328, 584, 776, 176, 208, 592, 672, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_453, vertices_841, vertices_241, vertices_593, vertices_929, vertices_46, vertices_334, vertices_678, vertices_902, vertices_58, vertices_794, vertices_188, vertices_220, vertices_600] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_81, vertices_529, vertices_161, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_769, vertices_14, vertices_38, vertices_646, vertices_262, vertices_26, vertices_42, vertices_266, vertices_50, vertices_530, vertices_546, vertices_770, vertices_156, vertices_44, vertices_76, vertices_164, vertices_196, vertices_324, vertices_388, vertices_56, vertices_88, vertices_536, vertices_328, vertices_584, vertices_776, vertices_176, vertices_208, vertices_592, vertices_672, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_453), (false, vertices_841), (false, vertices_241), (false, vertices_593), (false, vertices_929), (true, vertices_14), (true, vertices_38), (true, vertices_646), (true, vertices_262), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_770), (true, vertices_156), (true, vertices_44), (true, vertices_76), (true, vertices_164), (true, vertices_56), (true, vertices_88), (true, vertices_536)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 15 else
  if p.val = (false, vertices_453) then 18 else
  if p.val = (false, vertices_841) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (false, vertices_593) then 0 else
  if p.val = (false, vertices_929) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_646) then 16 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_42) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_156) then 19 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_76) then 9 else
  if p.val = (true, vertices_164) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_88) then 12 else
  if p.val = (true, vertices_536) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_593), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_646), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_156), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 7 334 14 3
cert_row_4 1 0 2 3 7 8 794 26 3
cert_row_2 2 0 1 6 8 646
cert_row_2 3 1 2 3 6 156
cert_rows
cert_pivot_2 5 7 0 1
cert_heightProof 4
cert_coverFacet 0 46
cert_cover_2 0 1 0 2 4 14 46 3
cert_coverFacet 1 334
cert_cover_5 1 0 0 1 2 5 14 334 3
cert_coverFacet 2 678
cert_cover_5 2 2 0 1 4 6 38 678 3
cert_coverFacet 3 902
cert_cover_5 3 2 0 1 6 7 646 902 3
cert_coverFacet 4 58
cert_cover_2 4 2 0 3 4 26 58 3
cert_coverFacet 5 794
cert_cover_5 5 1 0 2 3 7 26 794 3
cert_coverFacet 6 188
cert_cover_5 6 3 1 2 3 4 156 188 3
cert_coverFacet 7 220
cert_cover_5 7 3 1 2 3 5 156 220 3
cert_coverFacet 8 600
cert_cover_2 8 3 2 5 8 88 600 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0065

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m15e11q2_0066.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0066

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [227, 285, 537, 425, 713, 369, 593, 542, 342, 358, 550, 722, 674, 908, 932, 25, 137, 265, 521, 81, 273, 529, 97, 161, 289, 193, 577, 22, 38, 326, 518, 82, 530, 98, 162, 546, 194, 642, 28, 268, 524, 276, 292, 548, 900, 536, 392, 648, 336, 592, 352, 416, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_227, vertices_285, vertices_537, vertices_425, vertices_713, vertices_369, vertices_593, vertices_542, vertices_342, vertices_358, vertices_550, vertices_722, vertices_674, vertices_908, vertices_932] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_265, vertices_521, vertices_81, vertices_273, vertices_529, vertices_97, vertices_161, vertices_289, vertices_193, vertices_577, vertices_22, vertices_38, vertices_326, vertices_518, vertices_82, vertices_530, vertices_98, vertices_162, vertices_546, vertices_194, vertices_642, vertices_28, vertices_268, vertices_524, vertices_276, vertices_292, vertices_548, vertices_900, vertices_536, vertices_392, vertices_648, vertices_336, vertices_592, vertices_352, vertices_416, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_227), (false, vertices_285), (false, vertices_537), (false, vertices_425), (false, vertices_713), (false, vertices_369), (false, vertices_593), (true, vertices_22), (true, vertices_38), (true, vertices_326), (true, vertices_518), (true, vertices_82), (true, vertices_530), (true, vertices_546), (true, vertices_642), (true, vertices_524), (true, vertices_292), (true, vertices_548), (true, vertices_900), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_227) then 14 else
  if p.val = (false, vertices_285) then 17 else
  if p.val = (false, vertices_537) then 0 else
  if p.val = (false, vertices_425) then 20 else
  if p.val = (false, vertices_713) then 21 else
  if p.val = (false, vertices_369) then 23 else
  if p.val = (false, vertices_593) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_38) then 3 else
  if p.val = (true, vertices_326) then 15 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_900) then 18 else
  if p.val = (true, vertices_672) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_537), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_593), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_326), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_900), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 8 542 22 2
cert_row_4 1 0 3 5 6 8 722 82 3
cert_row_2 2 0 1 5 7 326
cert_row_2 3 1 6 7 8 900
cert_rows
cert_pivot_2 2 3 0 1
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 22 542 2
cert_coverFacet 1 342
cert_cover_5 1 2 0 1 3 5 22 342 3
cert_coverFacet 2 358
cert_cover_5 2 2 0 1 4 5 38 358 3
cert_coverFacet 3 550
cert_cover_2 3 1 0 4 8 38 550 3
cert_coverFacet 4 722
cert_cover_5 4 1 0 3 5 6 82 722 3
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 908
cert_cover_5 6 3 1 2 6 7 268 908 2
cert_coverFacet 7 932
cert_cover_5 7 3 1 4 6 7 292 932 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0066

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m15e11q2_0067.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0067

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 589, 345, 905, 689, 593, 110, 782, 182, 902, 362, 306, 740, 368, 624, 73, 265, 521, 81, 145, 273, 529, 577, 385, 641, 14, 38, 134, 774, 106, 266, 50, 146, 274, 290, 386, 76, 524, 100, 164, 580, 644, 328, 776, 112, 176, 304, 560, 336, 592, 352, 608, 672, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_589, vertices_345, vertices_905, vertices_689, vertices_593, vertices_110, vertices_782, vertices_182, vertices_902, vertices_362, vertices_306, vertices_740, vertices_368, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_265, vertices_521, vertices_81, vertices_145, vertices_273, vertices_529, vertices_577, vertices_385, vertices_641, vertices_14, vertices_38, vertices_134, vertices_774, vertices_106, vertices_266, vertices_50, vertices_146, vertices_274, vertices_290, vertices_386, vertices_76, vertices_524, vertices_100, vertices_164, vertices_580, vertices_644, vertices_328, vertices_776, vertices_112, vertices_176, vertices_304, vertices_560, vertices_336, vertices_592, vertices_352, vertices_608, vertices_672, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_589), (false, vertices_345), (false, vertices_905), (false, vertices_689), (false, vertices_593), (true, vertices_14), (true, vertices_38), (true, vertices_134), (true, vertices_774), (true, vertices_106), (true, vertices_266), (true, vertices_50), (true, vertices_290), (true, vertices_100), (true, vertices_164), (true, vertices_644), (true, vertices_112), (true, vertices_304), (true, vertices_352), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 14 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 18 else
  if p.val = (false, vertices_589) then 15 else
  if p.val = (false, vertices_345) then 21 else
  if p.val = (false, vertices_905) then 22 else
  if p.val = (false, vertices_689) then 24 else
  if p.val = (false, vertices_593) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_774) then 16 else
  if p.val = (true, vertices_106) then 19 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_352) then 12 else
  if p.val = (true, vertices_608) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_593), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_774), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_106), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 7 8 774
cert_row_2 1 0 2 4 5 106
cert_row_4 2 0 1 3 4 6 182 38 2
cert_row_4 3 1 4 5 6 8 740 100 3
cert_rows
cert_pivot_2 7 2 0 1
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 1 0 1 2 4 14 110 3
cert_coverFacet 1 782
cert_cover_5 1 0 0 1 2 7 14 782 3
cert_coverFacet 2 182
cert_cover_5 2 2 0 1 3 4 38 182 2
cert_coverFacet 3 902
cert_cover_5 3 0 0 1 6 7 134 902 3
cert_coverFacet 4 362
cert_cover_5 4 1 0 2 4 7 106 362 3
cert_coverFacet 5 306
cert_cover_2 5 3 0 4 7 50 306 3
cert_coverFacet 6 740
cert_cover_5 6 3 1 4 5 6 100 740 3
cert_coverFacet 7 368
cert_cover_2 7 4 3 5 7 112 368 3
cert_coverFacet 8 624
cert_cover_2 8 4 3 5 8 112 624 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0067

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e11q2_0068.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0068

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [551, 595, 291, 451, 217, 689, 417, 302, 774, 834, 348, 668, 684, 852, 488, 35, 67, 259, 515, 81, 145, 529, 161, 289, 545, 193, 385, 38, 262, 518, 290, 322, 578, 770, 28, 44, 652, 268, 340, 532, 548, 772, 88, 152, 168, 296, 200, 328, 592, 656, 416, 672, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_551, vertices_595, vertices_291, vertices_451, vertices_217, vertices_689, vertices_417, vertices_302, vertices_774, vertices_834, vertices_348, vertices_668, vertices_684, vertices_852, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_259, vertices_515, vertices_81, vertices_145, vertices_529, vertices_161, vertices_289, vertices_545, vertices_193, vertices_385, vertices_38, vertices_262, vertices_518, vertices_290, vertices_322, vertices_578, vertices_770, vertices_28, vertices_44, vertices_652, vertices_268, vertices_340, vertices_532, vertices_548, vertices_772, vertices_88, vertices_152, vertices_168, vertices_296, vertices_200, vertices_328, vertices_592, vertices_656, vertices_416, vertices_672, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_551), (false, vertices_595), (false, vertices_291), (false, vertices_451), (false, vertices_217), (false, vertices_689), (false, vertices_417), (true, vertices_262), (true, vertices_770), (true, vertices_28), (true, vertices_44), (true, vertices_652), (true, vertices_268), (true, vertices_340), (true, vertices_532), (true, vertices_772), (true, vertices_168), (true, vertices_296), (true, vertices_328), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 20 17 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_551) then 14 else
  if p.val = (false, vertices_595) then 15 else
  if p.val = (false, vertices_291) then 0 else
  if p.val = (false, vertices_451) then 16 else
  if p.val = (false, vertices_217) then 18 else
  if p.val = (false, vertices_689) then 23 else
  if p.val = (false, vertices_417) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_44) then 5 else
  if p.val = (true, vertices_652) then 19 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_340) then 21 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_291), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_417), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_551), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_652), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(true, vertices_340), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 5 7 340
cert_row_2 1 1 2 6 8 652
cert_row_4 2 0 1 2 4 7 302 38 2
cert_row_4 3 2 4 5 6 7 488 168 2
cert_rows
cert_pivot_2 3 8 0 2
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 2 0 1 2 4 38 302 2
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 834
cert_cover_2 2 5 0 7 8 322 834 3
cert_coverFacet 3 348
cert_cover_5 3 0 1 2 3 5 28 348 3
cert_coverFacet 4 668
cert_cover_5 4 1 1 2 3 6 28 668 3
cert_coverFacet 5 684
cert_cover_5 5 1 1 2 4 6 44 684 3
cert_coverFacet 6 852
cert_cover_5 6 0 1 3 5 8 340 852 3
cert_coverFacet 7 488
cert_cover_5 7 3 2 4 5 6 168 488 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0068

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e11q2_0069.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0069

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 707, 653, 805, 453, 369, 542, 58, 234, 650, 818, 412, 788, 120, 472, 579, 133, 261, 517, 97, 289, 545, 193, 321, 641, 26, 42, 138, 522, 50, 530, 98, 546, 194, 642, 28, 140, 524, 276, 532, 388, 772, 56, 88, 408, 104, 200, 648, 112, 304, 336, 784, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_707, vertices_653, vertices_805, vertices_453, vertices_369, vertices_542, vertices_58, vertices_234, vertices_650, vertices_818, vertices_412, vertices_788, vertices_120, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_579, vertices_133, vertices_261, vertices_517, vertices_97, vertices_289, vertices_545, vertices_193, vertices_321, vertices_641, vertices_26, vertices_42, vertices_138, vertices_522, vertices_50, vertices_530, vertices_98, vertices_546, vertices_194, vertices_642, vertices_28, vertices_140, vertices_524, vertices_276, vertices_532, vertices_388, vertices_772, vertices_56, vertices_88, vertices_408, vertices_104, vertices_200, vertices_648, vertices_112, vertices_304, vertices_336, vertices_784, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_707), (false, vertices_653), (false, vertices_805), (false, vertices_453), (false, vertices_369), (true, vertices_26), (true, vertices_42), (true, vertices_138), (true, vertices_522), (true, vertices_50), (true, vertices_530), (true, vertices_28), (true, vertices_276), (true, vertices_532), (true, vertices_56), (true, vertices_88), (true, vertices_408), (true, vertices_104), (true, vertices_200), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 15 else
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_453) then 20 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_408) then 22 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_784) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 8 542 26 1
cert_row_4 1 0 2 4 5 6 234 42 3
cert_row_2 2 2 3 6 7 408
cert_row_4 3 0 3 4 7 8 818 50 3
cert_rows
cert_pivot_2 1 5 2 0
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 26 542 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 234
cert_cover_5 2 1 0 2 4 5 42 234 3
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 818
cert_cover_5 4 3 0 3 4 7 50 818 3
cert_coverFacet 5 412
cert_cover_5 5 2 1 2 3 6 28 412 3
cert_coverFacet 6 788
cert_cover_2 6 3 1 7 8 276 788 3
cert_coverFacet 7 120
cert_cover_2 7 3 2 4 5 56 120 3
cert_coverFacet 8 472
cert_cover_5 8 2 2 3 5 6 88 472 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0069

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e11q2_0070.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0070

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [115, 901, 57, 89, 681, 841, 481, 158, 790, 422, 186, 850, 354, 604, 652, 25, 41, 73, 521, 49, 81, 97, 161, 321, 385, 641, 769, 22, 134, 262, 154, 50, 82, 786, 98, 162, 290, 322, 28, 140, 524, 532, 388, 644, 772, 56, 88, 168, 584, 648, 592, 352, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_115, vertices_901, vertices_57, vertices_89, vertices_681, vertices_841, vertices_481, vertices_158, vertices_790, vertices_422, vertices_186, vertices_850, vertices_354, vertices_604, vertices_652] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_73, vertices_521, vertices_49, vertices_81, vertices_97, vertices_161, vertices_321, vertices_385, vertices_641, vertices_769, vertices_22, vertices_134, vertices_262, vertices_154, vertices_50, vertices_82, vertices_786, vertices_98, vertices_162, vertices_290, vertices_322, vertices_28, vertices_140, vertices_524, vertices_532, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_168, vertices_584, vertices_648, vertices_592, vertices_352, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_115), (false, vertices_901), (false, vertices_57), (false, vertices_89), (false, vertices_681), (false, vertices_841), (false, vertices_481), (true, vertices_22), (true, vertices_134), (true, vertices_262), (true, vertices_154), (true, vertices_786), (true, vertices_162), (true, vertices_290), (true, vertices_322), (true, vertices_28), (true, vertices_140), (true, vertices_524), (true, vertices_532), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 13 15 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_115) then 20 else
  if p.val = (false, vertices_901) then 14 else
  if p.val = (false, vertices_57) then 0 else
  if p.val = (false, vertices_89) then 1 else
  if p.val = (false, vertices_681) then 16 else
  if p.val = (false, vertices_841) then 17 else
  if p.val = (false, vertices_481) then 24 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_262) then 4 else
  if p.val = (true, vertices_154) then 18 else
  if p.val = (true, vertices_786) then 21 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_140) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_592) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_57), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_89), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 15 => Sum.inl 2
  | 16 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_154), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_115), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_786), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 7 422 134 2
cert_row_2 1 0 2 3 6 154
cert_row_2 2 0 3 7 8 786
cert_row_4 3 1 2 3 5 8 604 28 3
cert_rows
cert_pivot_2 4 6 0 1
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 1 0 1 2 3 22 158 2
cert_coverFacet 1 790
cert_cover_5 1 2 0 1 3 7 22 790 3
cert_coverFacet 2 422
cert_cover_5 2 0 0 1 4 6 134 422 2
cert_coverFacet 3 186
cert_cover_5 3 1 0 2 3 4 154 186 3
cert_coverFacet 4 850
cert_cover_5 4 2 0 3 5 7 82 850 3
cert_coverFacet 5 354
cert_cover_2 5 4 0 5 7 98 354 3
cert_coverFacet 6 604
cert_cover_5 6 3 1 2 3 5 28 604 3
cert_coverFacet 7 652
cert_cover_2 7 2 1 6 8 140 652 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0070

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_3843 : Certifies 3843 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0041.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3844 : Certifies 3844 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0042.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3845 : Certifies 3845 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0043.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3846 : Certifies 3846 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0044.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3847 : Certifies 3847 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0045.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3848 : Certifies 3848 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0046.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3849 : Certifies 3849 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0047.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3850 : Certifies 3850 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0048.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3851 : Certifies 3851 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0049.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3852 : Certifies 3852 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0050.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3853 : Certifies 3853 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0051.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3854 : Certifies 3854 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0052.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3855 : Certifies 3855 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0053.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3856 : Certifies 3856 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0054.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3857 : Certifies 3857 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0055.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3858 : Certifies 3858 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0056.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3859 : Certifies 3859 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0057.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3860 : Certifies 3860 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0058.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3861 : Certifies 3861 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0059.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3862 : Certifies 3862 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0060.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3863 : Certifies 3863 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0061.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3864 : Certifies 3864 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0062.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3865 : Certifies 3865 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0063.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3866 : Certifies 3866 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0064.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3867 : Certifies 3867 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0065.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3868 : Certifies 3868 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0066.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3869 : Certifies 3869 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0067.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3870 : Certifies 3870 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0068.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3871 : Certifies 3871 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0069.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3872 : Certifies 3872 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e11q2_0070.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B127 (j : Fin 30) :
    Certifies (3843 + j.val) := by
  fin_cases j
  · exact projection_3843
  · exact projection_3844
  · exact projection_3845
  · exact projection_3846
  · exact projection_3847
  · exact projection_3848
  · exact projection_3849
  · exact projection_3850
  · exact projection_3851
  · exact projection_3852
  · exact projection_3853
  · exact projection_3854
  · exact projection_3855
  · exact projection_3856
  · exact projection_3857
  · exact projection_3858
  · exact projection_3859
  · exact projection_3860
  · exact projection_3861
  · exact projection_3862
  · exact projection_3863
  · exact projection_3864
  · exact projection_3865
  · exact projection_3866
  · exact projection_3867
  · exact projection_3868
  · exact projection_3869
  · exact projection_3870
  · exact projection_3871
  · exact projection_3872

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
