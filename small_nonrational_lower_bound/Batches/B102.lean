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
/- Source: ProjectionCertificates/R_m15e10q1_0492.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0492

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 333, 653, 597, 425, 449, 310, 186, 666, 850, 482, 60, 540, 300, 340, 13, 69, 517, 137, 265, 193, 321, 577, 385, 641, 154, 50, 274, 530, 162, 290, 194, 322, 578, 642, 28, 44, 268, 524, 52, 84, 276, 532, 292, 324, 56, 536, 168, 296, 648, 336, 592, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_333, vertices_653, vertices_597, vertices_425, vertices_449, vertices_310, vertices_186, vertices_666, vertices_850, vertices_482, vertices_60, vertices_540, vertices_300, vertices_340] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_517, vertices_137, vertices_265, vertices_193, vertices_321, vertices_577, vertices_385, vertices_641, vertices_154, vertices_50, vertices_274, vertices_530, vertices_162, vertices_290, vertices_194, vertices_322, vertices_578, vertices_642, vertices_28, vertices_44, vertices_268, vertices_524, vertices_52, vertices_84, vertices_276, vertices_532, vertices_292, vertices_324, vertices_56, vertices_536, vertices_168, vertices_296, vertices_648, vertices_336, vertices_592, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_333), (false, vertices_653), (false, vertices_597), (false, vertices_425), (false, vertices_449), (true, vertices_154), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_290), (true, vertices_322), (true, vertices_28), (true, vertices_44), (true, vertices_52), (true, vertices_276), (true, vertices_292), (true, vertices_56), (true, vertices_536), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_333) then 19 else
  if p.val = (false, vertices_653) then 20 else
  if p.val = (false, vertices_597) then 21 else
  if p.val = (false, vertices_425) then 23 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_154) then 17 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_292) then 11 else
  if p.val = (true, vertices_56) then 12 else
  if p.val = (true, vertices_536) then 13 else
  if p.val = (true, vertices_336) then 14 else
  0
cert_priority
cert_nodeAtPriority_51 449 50 274 530 162 290 322 28 44 52 276 292 56 536 336 707 154 333 653 597 425
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 6 154
cert_row_4 1 0 1 3 4 7 310 50 1
cert_row_4 2 0 3 5 7 8 850 274 2
cert_row_4 3 0 4 5 6 7 482 162 2
cert_rows
cert_pivot_2 2 1 3 0
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 1 0 1 3 4 50 310 1
cert_coverFacet 1 186
cert_cover_5 1 0 0 2 3 4 154 186 3
cert_coverFacet 2 666
cert_cover_5 2 0 0 2 3 8 154 666 3
cert_coverFacet 3 850
cert_cover_5 3 2 0 3 5 7 274 850 2
cert_coverFacet 4 482
cert_cover_5 4 3 0 4 5 6 162 482 2
cert_coverFacet 5 60
cert_cover_2 5 2 1 3 4 28 60 3
cert_coverFacet 6 540
cert_cover_2 6 2 1 3 8 28 540 3
cert_coverFacet 7 300
cert_cover_2 7 2 1 4 7 44 300 3
cert_coverFacet 8 340
cert_cover_2 8 3 1 5 7 84 340 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0492

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e10q1_0493.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0493

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 229, 713, 369, 689, 833, 302, 526, 182, 662, 842, 306, 460, 652, 356, 49, 273, 529, 97, 161, 193, 321, 577, 641, 769, 14, 150, 38, 518, 266, 522, 50, 274, 530, 290, 770, 140, 268, 524, 100, 164, 292, 196, 324, 644, 200, 328, 584, 648, 176, 304, 656, 352, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_229, vertices_713, vertices_369, vertices_689, vertices_833, vertices_302, vertices_526, vertices_182, vertices_662, vertices_842, vertices_306, vertices_460, vertices_652, vertices_356] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_273, vertices_529, vertices_97, vertices_161, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_14, vertices_150, vertices_38, vertices_518, vertices_266, vertices_522, vertices_50, vertices_274, vertices_530, vertices_290, vertices_770, vertices_140, vertices_268, vertices_524, vertices_100, vertices_164, vertices_292, vertices_196, vertices_324, vertices_644, vertices_200, vertices_328, vertices_584, vertices_648, vertices_176, vertices_304, vertices_656, vertices_352, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_229), (false, vertices_713), (false, vertices_369), (false, vertices_689), (false, vertices_833), (true, vertices_14), (true, vertices_150), (true, vertices_38), (true, vertices_518), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_290), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_292), (true, vertices_324), (true, vertices_644), (true, vertices_328)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 16 else
  if p.val = (false, vertices_229) then 19 else
  if p.val = (false, vertices_713) then 21 else
  if p.val = (false, vertices_369) then 23 else
  if p.val = (false, vertices_689) then 24 else
  if p.val = (false, vertices_833) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_150) then 17 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_50) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_292) then 11 else
  if p.val = (true, vertices_324) then 12 else
  if p.val = (true, vertices_644) then 13 else
  if p.val = (true, vertices_328) then 14 else
  0
cert_priority
cert_nodeAtPriority_40 833 14 38 518 266 522 50 290 140 268 524 292 324 644 328 787 150 229 713 369 689
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 6 150
cert_row_4 1 0 1 2 4 7 302 14 3
cert_row_4 2 0 2 5 7 8 842 266 2
cert_row_4 3 1 2 5 6 7 460 140 2
cert_rows
cert_pivot_2 3 4 0 1
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 1 0 1 2 4 14 302 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 182
cert_cover_5 2 0 0 1 3 4 150 182 3
cert_coverFacet 3 662
cert_cover_5 3 0 0 1 3 8 150 662 3
cert_coverFacet 4 842
cert_cover_5 4 2 0 2 5 7 266 842 2
cert_coverFacet 5 306
cert_cover_2 5 3 0 4 7 50 306 3
cert_coverFacet 6 460
cert_cover_5 6 3 1 2 5 6 140 460 2
cert_coverFacet 7 652
cert_cover_2 7 2 1 6 8 140 652 3
cert_coverFacet 8 356
cert_cover_2 8 4 1 5 7 100 356 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0493

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e10q1_0494.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0494

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 613, 409, 689, 481, 833, 174, 590, 662, 154, 282, 842, 364, 676, 424, 145, 273, 529, 97, 161, 545, 321, 577, 385, 769, 14, 134, 518, 26, 586, 138, 266, 146, 274, 530, 770, 44, 76, 100, 164, 548, 580, 644, 152, 280, 168, 296, 328, 392, 656, 352, 416, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_613, vertices_409, vertices_689, vertices_481, vertices_833, vertices_174, vertices_590, vertices_662, vertices_154, vertices_282, vertices_842, vertices_364, vertices_676, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_145, vertices_273, vertices_529, vertices_97, vertices_161, vertices_545, vertices_321, vertices_577, vertices_385, vertices_769, vertices_14, vertices_134, vertices_518, vertices_26, vertices_586, vertices_138, vertices_266, vertices_146, vertices_274, vertices_530, vertices_770, vertices_44, vertices_76, vertices_100, vertices_164, vertices_548, vertices_580, vertices_644, vertices_152, vertices_280, vertices_168, vertices_296, vertices_328, vertices_392, vertices_656, vertices_352, vertices_416, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_613), (false, vertices_409), (false, vertices_689), (false, vertices_481), (false, vertices_833), (true, vertices_14), (true, vertices_134), (true, vertices_518), (true, vertices_26), (true, vertices_586), (true, vertices_138), (true, vertices_266), (true, vertices_146), (true, vertices_44), (true, vertices_76), (true, vertices_164), (true, vertices_644), (true, vertices_168), (true, vertices_296), (true, vertices_328)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 16 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_409) then 21 else
  if p.val = (false, vertices_689) then 23 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (false, vertices_833) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_586) then 17 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_146) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_76) then 9 else
  if p.val = (true, vertices_164) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_328) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 833 14 134 518 26 138 266 146 44 76 164 644 168 296 328 787 586 613 409 689 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 8 662 134 2
cert_row_2 1 0 2 5 8 586
cert_row_4 2 0 1 2 4 6 174 14 3
cert_row_4 3 1 2 4 5 7 364 44 3
cert_rows
cert_pivot_2 3 8 0 1
cert_heightProof 4
cert_coverFacet 0 174
cert_cover_5 0 2 0 1 2 4 14 174 3
cert_coverFacet 1 590
cert_cover_5 1 1 0 1 2 5 14 590 3
cert_coverFacet 2 662
cert_cover_5 2 0 0 1 3 6 134 662 2
cert_coverFacet 3 154
cert_cover_2 3 2 0 3 6 26 154 3
cert_coverFacet 4 282
cert_cover_2 4 2 0 3 7 26 282 3
cert_coverFacet 5 842
cert_cover_5 5 1 0 2 5 7 586 842 3
cert_coverFacet 6 364
cert_cover_5 6 3 1 2 4 5 44 364 3
cert_coverFacet 7 676
cert_cover_2 7 4 1 6 8 164 676 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0494

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e10q1_0496.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0496

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [307, 285, 541, 357, 709, 625, 654, 794, 394, 562, 738, 418, 204, 332, 488, 29, 69, 261, 517, 49, 273, 529, 97, 289, 577, 138, 266, 522, 50, 274, 530, 162, 290, 546, 386, 642, 76, 140, 268, 524, 196, 324, 644, 280, 536, 200, 328, 392, 560, 224, 352, 608, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_285, vertices_541, vertices_357, vertices_709, vertices_625, vertices_654, vertices_794, vertices_394, vertices_562, vertices_738, vertices_418, vertices_204, vertices_332, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_29, vertices_69, vertices_261, vertices_517, vertices_49, vertices_273, vertices_529, vertices_97, vertices_289, vertices_577, vertices_138, vertices_266, vertices_522, vertices_50, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_76, vertices_140, vertices_268, vertices_524, vertices_196, vertices_324, vertices_644, vertices_280, vertices_536, vertices_200, vertices_328, vertices_392, vertices_560, vertices_224, vertices_352, vertices_608, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_285), (false, vertices_541), (false, vertices_357), (false, vertices_709), (false, vertices_625), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_530), (true, vertices_162), (true, vertices_546), (true, vertices_386), (true, vertices_642), (true, vertices_76), (true, vertices_140), (true, vertices_200), (true, vertices_328), (true, vertices_392), (true, vertices_224), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 20 17 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 16 else
  if p.val = (false, vertices_285) then 18 else
  if p.val = (false, vertices_541) then 19 else
  if p.val = (false, vertices_357) then 21 else
  if p.val = (false, vertices_709) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_140) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
cert_nodeAtPriority_52 138 2 266 1 522 530 162 546 386 642 76 140 200 328 392 224 416 307 285 541 357 709 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 138 1
cert_row_4 1 0 2 3 7 8 794 266 2
cert_row_4 2 0 4 5 6 8 738 162 2
cert_row_4 3 2 4 5 6 7 488 200 1
cert_rows
cert_pivot_2 1 3 0 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 138 654 1
cert_coverFacet 1 794
cert_cover_5 1 1 0 2 3 7 266 794 2
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 562
cert_cover_2 3 3 0 4 8 50 562 3
cert_coverFacet 4 738
cert_cover_5 4 2 0 4 5 6 162 738 2
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 204
cert_cover_2 6 2 1 5 6 76 204 3
cert_coverFacet 7 332
cert_cover_2 7 2 1 5 7 76 332 3
cert_coverFacet 8 488
cert_cover_5 8 3 2 4 5 6 200 488 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0496

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e10q1_0497.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0497

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 589, 681, 457, 433, 833, 310, 534, 838, 666, 178, 674, 220, 540, 468, 73, 137, 521, 161, 289, 545, 321, 577, 385, 769, 22, 262, 518, 50, 146, 530, 162, 290, 546, 642, 770, 28, 76, 524, 212, 276, 532, 324, 580, 152, 536, 200, 648, 176, 304, 400, 672, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_589, vertices_681, vertices_457, vertices_433, vertices_833, vertices_310, vertices_534, vertices_838, vertices_666, vertices_178, vertices_674, vertices_220, vertices_540, vertices_468] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_521, vertices_161, vertices_289, vertices_545, vertices_321, vertices_577, vertices_385, vertices_769, vertices_22, vertices_262, vertices_518, vertices_50, vertices_146, vertices_530, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_28, vertices_76, vertices_524, vertices_212, vertices_276, vertices_532, vertices_324, vertices_580, vertices_152, vertices_536, vertices_200, vertices_648, vertices_176, vertices_304, vertices_400, vertices_672, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_589), (false, vertices_681), (false, vertices_457), (false, vertices_433), (false, vertices_833), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_50), (true, vertices_146), (true, vertices_530), (true, vertices_162), (true, vertices_642), (true, vertices_28), (true, vertices_212), (true, vertices_276), (true, vertices_532), (true, vertices_324), (true, vertices_152), (true, vertices_536)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_589) then 18 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (false, vertices_833) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_162) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_212) then 19 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_324) then 12 else
  if p.val = (true, vertices_152) then 13 else
  if p.val = (true, vertices_536) then 14 else
  0
cert_priority
cert_nodeAtPriority_65 833 2 22 1 262 3 518 50 146 530 162 642 28 276 532 324 152 536 803 589 212 681 457 433
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 7 310 22 3
cert_row_4 1 0 1 5 7 8 838 262 2
cert_row_2 2 1 3 5 6 212
cert_row_4 3 0 2 3 6 8 666 146 1
cert_rows
cert_pivot_2 4 7 1 0
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 0 0 1 3 4 22 310 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 838
cert_cover_5 2 1 0 1 5 7 262 838 2
cert_coverFacet 3 666
cert_cover_5 3 3 0 2 3 6 146 666 1
cert_coverFacet 4 178
cert_cover_2 4 3 0 4 6 50 178 3
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 220
cert_cover_5 6 2 1 2 3 5 28 220 3
cert_coverFacet 7 540
cert_cover_2 7 2 1 3 8 28 540 3
cert_coverFacet 8 468
cert_cover_5 8 2 1 3 5 7 212 468 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0497

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e10q1_0498.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0498

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 357, 793, 433, 737, 833, 542, 302, 230, 710, 154, 170, 844, 408, 424, 145, 273, 529, 97, 161, 289, 321, 577, 641, 769, 14, 38, 198, 518, 26, 42, 138, 146, 530, 162, 642, 268, 524, 100, 292, 324, 580, 152, 280, 536, 168, 296, 392, 776, 400, 224, 416, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_357, vertices_793, vertices_433, vertices_737, vertices_833, vertices_542, vertices_302, vertices_230, vertices_710, vertices_154, vertices_170, vertices_844, vertices_408, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_145, vertices_273, vertices_529, vertices_97, vertices_161, vertices_289, vertices_321, vertices_577, vertices_641, vertices_769, vertices_14, vertices_38, vertices_198, vertices_518, vertices_26, vertices_42, vertices_138, vertices_146, vertices_530, vertices_162, vertices_642, vertices_268, vertices_524, vertices_100, vertices_292, vertices_324, vertices_580, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_392, vertices_776, vertices_400, vertices_224, vertices_416, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_357), (false, vertices_793), (false, vertices_433), (false, vertices_737), (false, vertices_833), (true, vertices_14), (true, vertices_38), (true, vertices_198), (true, vertices_518), (true, vertices_26), (true, vertices_42), (true, vertices_138), (true, vertices_162), (true, vertices_268), (true, vertices_524), (true, vertices_580), (true, vertices_152), (true, vertices_168), (true, vertices_296), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 16 else
  if p.val = (false, vertices_357) then 19 else
  if p.val = (false, vertices_793) then 21 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (false, vertices_833) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_198) then 17 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_42) then 5 else
  if p.val = (true, vertices_138) then 6 else
  if p.val = (true, vertices_162) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_392) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 833 14 38 518 26 42 138 162 268 524 580 152 168 296 392 659 198 357 793 433 737
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 6 198
cert_row_4 1 0 1 2 3 8 542 14 3
cert_row_4 2 0 1 2 4 7 302 14 3
cert_row_4 3 1 2 5 7 8 844 268 2
cert_rows
cert_pivot_2 6 3 0 1
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 1 0 1 2 3 14 542 3
cert_coverFacet 1 302
cert_cover_5 1 2 0 1 2 4 14 302 3
cert_coverFacet 2 230
cert_cover_5 2 0 0 1 4 5 38 230 3
cert_coverFacet 3 710
cert_cover_5 3 0 0 1 5 8 198 710 3
cert_coverFacet 4 154
cert_cover_2 4 2 0 3 6 26 154 3
cert_coverFacet 5 170
cert_cover_2 5 2 0 4 6 42 170 3
cert_coverFacet 6 844
cert_cover_5 6 3 1 2 5 7 268 844 2
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0498

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e10q1_0499.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0499

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 789, 677, 185, 409, 625, 198, 582, 774, 458, 850, 716, 376, 616, 680, 133, 261, 517, 153, 49, 273, 529, 161, 545, 385, 70, 134, 262, 518, 194, 322, 578, 386, 770, 196, 580, 644, 772, 56, 280, 104, 168, 552, 200, 328, 584, 392, 648, 112, 336, 592, 784, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_789, vertices_677, vertices_185, vertices_409, vertices_625, vertices_198, vertices_582, vertices_774, vertices_458, vertices_850, vertices_716, vertices_376, vertices_616, vertices_680] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_153, vertices_49, vertices_273, vertices_529, vertices_161, vertices_545, vertices_385, vertices_70, vertices_134, vertices_262, vertices_518, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_196, vertices_580, vertices_644, vertices_772, vertices_56, vertices_280, vertices_104, vertices_168, vertices_552, vertices_200, vertices_328, vertices_584, vertices_392, vertices_648, vertices_112, vertices_336, vertices_592, vertices_784, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_789), (false, vertices_677), (false, vertices_185), (false, vertices_409), (false, vertices_625), (true, vertices_70), (true, vertices_518), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_196), (true, vertices_580), (true, vertices_104), (true, vertices_552), (true, vertices_200), (true, vertices_328), (true, vertices_584), (true, vertices_648), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 16 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_677) then 19 else
  if p.val = (false, vertices_185) then 21 else
  if p.val = (false, vertices_409) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_648) then 13 else
  if p.val = (true, vertices_336) then 14 else
  0
cert_priority
cert_nodeAtPriority_52 70 1 518 2 194 322 578 770 196 580 104 552 200 328 584 648 336 391 789 677 185 409 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 5 6 8 716 196 1
cert_row_4 1 0 2 5 6 7 458 194 1
cert_row_4 2 0 3 5 7 8 850 322 1
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 198
cert_cover_2 0 1 0 5 6 70 198 3
cert_coverFacet 1 582
cert_cover_2 1 1 0 5 8 70 582 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 458
cert_cover_5 3 1 0 2 5 6 194 458 1
cert_coverFacet 4 850
cert_cover_5 4 2 0 3 5 7 322 850 1
cert_coverFacet 5 716
cert_cover_5 5 0 1 2 5 6 196 716 1
cert_coverFacet 6 376
cert_cover_5 6 3 2 3 4 5 56 376 3
cert_coverFacet 7 616
cert_cover_2 7 4 2 5 8 104 616 3
cert_coverFacet 8 680
cert_cover_2 8 4 2 6 8 168 680 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0499

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e10q1_0500.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0500

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [355, 661, 809, 465, 785, 737, 542, 206, 614, 298, 554, 458, 412, 708, 792, 145, 273, 529, 97, 289, 545, 193, 321, 641, 769, 14, 70, 518, 42, 202, 266, 522, 98, 290, 546, 322, 28, 140, 148, 532, 196, 580, 644, 280, 536, 296, 552, 392, 776, 400, 784, 608, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_355, vertices_661, vertices_809, vertices_465, vertices_785, vertices_737, vertices_542, vertices_206, vertices_614, vertices_298, vertices_554, vertices_458, vertices_412, vertices_708, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_145, vertices_273, vertices_529, vertices_97, vertices_289, vertices_545, vertices_193, vertices_321, vertices_641, vertices_769, vertices_14, vertices_70, vertices_518, vertices_42, vertices_202, vertices_266, vertices_522, vertices_98, vertices_290, vertices_546, vertices_322, vertices_28, vertices_140, vertices_148, vertices_532, vertices_196, vertices_580, vertices_644, vertices_280, vertices_536, vertices_296, vertices_552, vertices_392, vertices_776, vertices_400, vertices_784, vertices_608, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_355), (false, vertices_661), (false, vertices_809), (false, vertices_465), (false, vertices_785), (false, vertices_737), (true, vertices_14), (true, vertices_70), (true, vertices_518), (true, vertices_42), (true, vertices_202), (true, vertices_266), (true, vertices_522), (true, vertices_546), (true, vertices_28), (true, vertices_140), (true, vertices_196), (true, vertices_580), (true, vertices_280), (true, vertices_536), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_355) then 16 else
  if p.val = (false, vertices_661) then 19 else
  if p.val = (false, vertices_809) then 21 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (false, vertices_785) then 0 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_202) then 17 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_140) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_536) then 13 else
  if p.val = (true, vertices_392) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 785 14 70 518 42 266 522 546 28 140 196 580 280 536 392 355 202 661 809 465 737
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 5 8 614 70 2
cert_row_2 1 0 2 5 6 202
cert_row_4 2 0 1 2 3 8 542 14 3
cert_row_4 3 1 2 3 6 7 412 28 3
cert_rows
cert_pivot_2 4 5 0 1
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 2 0 1 2 3 14 542 3
cert_coverFacet 1 206
cert_cover_5 1 1 0 1 2 5 14 206 3
cert_coverFacet 2 614
cert_cover_5 2 0 0 1 4 5 70 614 2
cert_coverFacet 3 298
cert_cover_2 3 2 0 4 7 42 298 3
cert_coverFacet 4 554
cert_cover_2 4 2 0 4 8 42 554 3
cert_coverFacet 5 458
cert_cover_5 5 1 0 2 5 7 202 458 3
cert_coverFacet 6 412
cert_cover_5 6 3 1 2 3 6 28 412 3
cert_coverFacet 7 708
cert_cover_2 7 5 1 6 8 196 708 3
cert_coverFacet 8 792
cert_cover_2 8 3 2 7 8 280 792 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0500

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e10q1_0501.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0501

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 589, 565, 165, 453, 569, 361, 182, 794, 306, 658, 898, 724, 312, 968, 37, 69, 133, 517, 41, 73, 521, 561, 161, 289, 321, 385, 50, 146, 274, 530, 162, 290, 386, 642, 770, 52, 148, 532, 164, 196, 580, 56, 280, 536, 296, 328, 584, 776, 304, 656, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_589, vertices_565, vertices_165, vertices_453, vertices_569, vertices_361, vertices_182, vertices_794, vertices_306, vertices_658, vertices_898, vertices_724, vertices_312, vertices_968] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_133, vertices_517, vertices_41, vertices_73, vertices_521, vertices_561, vertices_161, vertices_289, vertices_321, vertices_385, vertices_50, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_386, vertices_642, vertices_770, vertices_52, vertices_148, vertices_532, vertices_164, vertices_196, vertices_580, vertices_56, vertices_280, vertices_536, vertices_296, vertices_328, vertices_584, vertices_776, vertices_304, vertices_656, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_589), (false, vertices_565), (false, vertices_165), (false, vertices_453), (false, vertices_569), (false, vertices_361), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_642), (true, vertices_770), (true, vertices_148), (true, vertices_280), (true, vertices_776), (true, vertices_304), (true, vertices_656), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 19 21 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 15 else
  if p.val = (false, vertices_589) then 17 else
  if p.val = (false, vertices_565) then 22 else
  if p.val = (false, vertices_165) then 0 else
  if p.val = (false, vertices_453) then 18 else
  if p.val = (false, vertices_569) then 23 else
  if p.val = (false, vertices_361) then 20 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_776) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_656) then 11 else
  if p.val = (true, vertices_704) then 12 else
  if p.val = (true, vertices_896) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_165), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 6 182 50 1
cert_row_4 1 0 2 3 7 8 794 274 1
cert_row_4 2 1 3 5 6 8 724 148 2
cert_row_4 3 2 5 6 7 8 968 328 2
cert_rows
cert_pivot_2 4 0 1 2
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 0 0 1 3 4 50 182 1
cert_coverFacet 1 794
cert_cover_5 1 1 0 2 3 7 274 794 1
cert_coverFacet 2 306
cert_cover_2 2 3 0 4 7 50 306 3
cert_coverFacet 3 658
cert_cover_2 3 3 0 6 8 146 658 3
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 724
cert_cover_5 5 2 1 3 5 6 148 724 2
cert_coverFacet 6 312
cert_cover_2 6 3 2 4 7 56 312 3
cert_coverFacet 7 968
cert_cover_5 7 3 2 5 6 7 328 968 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0501

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m15e10q1_0502.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0502

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [59, 709, 281, 617, 777, 241, 913, 558, 358, 902, 282, 778, 370, 468, 612, 25, 41, 265, 521, 49, 145, 273, 97, 193, 577, 641, 769, 38, 262, 518, 26, 42, 266, 522, 50, 274, 354, 770, 100, 548, 196, 324, 580, 388, 644, 280, 552, 776, 112, 208, 336, 400, 608, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_59, vertices_709, vertices_281, vertices_617, vertices_777, vertices_241, vertices_913, vertices_558, vertices_358, vertices_902, vertices_282, vertices_778, vertices_370, vertices_468, vertices_612] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_265, vertices_521, vertices_49, vertices_145, vertices_273, vertices_97, vertices_193, vertices_577, vertices_641, vertices_769, vertices_38, vertices_262, vertices_518, vertices_26, vertices_42, vertices_266, vertices_522, vertices_50, vertices_274, vertices_354, vertices_770, vertices_100, vertices_548, vertices_196, vertices_324, vertices_580, vertices_388, vertices_644, vertices_280, vertices_552, vertices_776, vertices_112, vertices_208, vertices_336, vertices_400, vertices_608, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_59), (false, vertices_709), (false, vertices_281), (false, vertices_617), (false, vertices_777), (false, vertices_241), (false, vertices_913), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_354), (true, vertices_770), (true, vertices_100), (true, vertices_548), (true, vertices_324), (true, vertices_388), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 21 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_59) then 15 else
  if p.val = (false, vertices_709) then 18 else
  if p.val = (false, vertices_281) then 0 else
  if p.val = (false, vertices_617) then 20 else
  if p.val = (false, vertices_777) then 1 else
  if p.val = (false, vertices_241) then 22 else
  if p.val = (false, vertices_913) then 23 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_274) then 7 else
  if p.val = (true, vertices_354) then 16 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_324) then 11 else
  if p.val = (true, vertices_388) then 12 else
  if p.val = (true, vertices_336) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_59), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_354), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
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
cert_row_4 0 0 1 2 4 8 558 38 2
cert_row_2 1 0 4 5 7 354
cert_row_4 2 0 1 6 7 8 902 262 2
cert_row_4 3 1 3 5 6 7 468 196 1
cert_rows
cert_pivot_2 2 4 0 1
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 0 0 1 2 4 38 558 2
cert_coverFacet 1 358
cert_cover_5 1 1 0 1 4 5 38 358 3
cert_coverFacet 2 902
cert_cover_5 2 2 0 1 6 7 262 902 2
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 370
cert_cover_5 5 1 0 3 4 5 50 370 3
cert_coverFacet 6 468
cert_cover_5 6 3 1 3 5 6 196 468 1
cert_coverFacet 7 612
cert_cover_2 7 4 1 5 8 100 612 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0502

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m15e10q1_0504.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0504

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 781, 665, 457, 209, 865, 654, 310, 406, 614, 114, 658, 396, 804, 496, 137, 265, 521, 81, 145, 529, 193, 321, 577, 769, 278, 38, 134, 518, 50, 82, 146, 530, 98, 578, 642, 140, 268, 524, 292, 548, 388, 772, 392, 648, 112, 304, 208, 400, 656, 352, 608, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_781, vertices_665, vertices_457, vertices_209, vertices_865, vertices_654, vertices_310, vertices_406, vertices_614, vertices_114, vertices_658, vertices_396, vertices_804, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_81, vertices_145, vertices_529, vertices_193, vertices_321, vertices_577, vertices_769, vertices_278, vertices_38, vertices_134, vertices_518, vertices_50, vertices_82, vertices_146, vertices_530, vertices_98, vertices_578, vertices_642, vertices_140, vertices_268, vertices_524, vertices_292, vertices_548, vertices_388, vertices_772, vertices_392, vertices_648, vertices_112, vertices_304, vertices_208, vertices_400, vertices_656, vertices_352, vertices_608, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_781), (false, vertices_665), (false, vertices_457), (false, vertices_209), (false, vertices_865), (true, vertices_278), (true, vertices_38), (true, vertices_134), (true, vertices_518), (true, vertices_50), (true, vertices_146), (true, vertices_98), (true, vertices_642), (true, vertices_140), (true, vertices_292), (true, vertices_548), (true, vertices_388), (true, vertices_112), (true, vertices_304), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 16 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_665) then 21 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (false, vertices_209) then 0 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_278) then 17 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_98) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
cert_nodeAtPriority_32 209 38 134 518 50 146 98 642 140 292 548 388 112 304 400 595 278 781 665 457 865
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 134 2
cert_row_4 1 0 1 4 5 8 614 38 3
cert_row_2 2 0 1 3 7 278
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 2 8 0 3
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 134 654 2
cert_coverFacet 1 310
cert_cover_5 1 2 0 1 3 4 278 310 3
cert_coverFacet 2 406
cert_cover_5 2 2 0 1 3 6 278 406 3
cert_coverFacet 3 614
cert_cover_5 3 1 0 1 4 5 38 614 3
cert_coverFacet 4 114
cert_cover_2 4 3 0 4 5 50 114 3
cert_coverFacet 5 658
cert_cover_2 5 3 0 6 8 146 658 3
cert_coverFacet 6 396
cert_cover_2 6 2 1 6 7 140 396 3
cert_coverFacet 7 804
cert_cover_2 7 4 1 7 8 292 804 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 112 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0504

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m15e10q1_0505.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0505

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 779, 307, 163, 665, 281, 241, 422, 838, 724, 484, 120, 312, 600, 872, 35, 131, 259, 515, 25, 265, 521, 49, 145, 273, 161, 641, 134, 262, 518, 162, 290, 770, 420, 196, 324, 580, 644, 56, 88, 280, 536, 104, 296, 584, 776, 112, 304, 208, 592, 656, 224, 352, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_779, vertices_307, vertices_163, vertices_665, vertices_281, vertices_241, vertices_422, vertices_838, vertices_724, vertices_484, vertices_120, vertices_312, vertices_600, vertices_872] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_25, vertices_265, vertices_521, vertices_49, vertices_145, vertices_273, vertices_161, vertices_641, vertices_134, vertices_262, vertices_518, vertices_162, vertices_290, vertices_770, vertices_420, vertices_196, vertices_324, vertices_580, vertices_644, vertices_56, vertices_88, vertices_280, vertices_536, vertices_104, vertices_296, vertices_584, vertices_776, vertices_112, vertices_304, vertices_208, vertices_592, vertices_656, vertices_224, vertices_352, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_779), (false, vertices_307), (false, vertices_163), (false, vertices_665), (false, vertices_281), (false, vertices_241), (true, vertices_262), (true, vertices_420), (true, vertices_196), (true, vertices_324), (true, vertices_580), (true, vertices_56), (true, vertices_88), (true, vertices_104), (true, vertices_296), (true, vertices_584), (true, vertices_592), (true, vertices_352), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 15 else
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_307) then 17 else
  if p.val = (false, vertices_163) then 0 else
  if p.val = (false, vertices_665) then 21 else
  if p.val = (false, vertices_281) then 1 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_420) then 19 else
  if p.val = (true, vertices_196) then 3 else
  if p.val = (true, vertices_324) then 4 else
  if p.val = (true, vertices_580) then 5 else
  if p.val = (true, vertices_56) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_352) then 12 else
  if p.val = (true, vertices_832) then 13 else
  0
cert_priority
cert_nodeAtPriority_47 163 281 262 196 324 580 56 88 104 296 584 592 352 832 647 779 307 420 665 241
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 7 8 838 262 2
cert_row_4 1 1 3 5 6 8 724 196 1
cert_row_2 2 1 4 6 7 420
cert_row_4 3 2 4 5 7 8 872 104 3
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 2 0 1 4 6 134 422 2
cert_coverFacet 1 838
cert_cover_5 1 0 0 1 5 7 262 838 2
cert_coverFacet 2 724
cert_cover_5 2 1 1 3 5 6 196 724 1
cert_coverFacet 3 484
cert_cover_5 3 2 1 4 5 6 420 484 2
cert_coverFacet 4 120
cert_cover_2 4 3 2 4 5 56 120 3
cert_coverFacet 5 312
cert_cover_2 5 3 2 4 7 56 312 3
cert_coverFacet 6 600
cert_cover_2 6 3 2 5 8 88 600 3
cert_coverFacet 7 872
cert_cover_5 7 3 2 4 5 7 104 872 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0505

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m15e10q1_0506.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0506

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 611, 163, 387, 597, 357, 425, 682, 898, 668, 468, 900, 632, 472, 360, 35, 131, 259, 515, 69, 261, 517, 97, 161, 289, 577, 385, 162, 546, 386, 642, 770, 84, 148, 532, 324, 388, 644, 772, 88, 152, 536, 104, 168, 296, 552, 328, 392, 648, 464, 592, 352, 608, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_611, vertices_163, vertices_387, vertices_597, vertices_357, vertices_425, vertices_682, vertices_898, vertices_668, vertices_468, vertices_900, vertices_632, vertices_472, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_69, vertices_261, vertices_517, vertices_97, vertices_161, vertices_289, vertices_577, vertices_385, vertices_162, vertices_546, vertices_386, vertices_642, vertices_770, vertices_84, vertices_148, vertices_532, vertices_324, vertices_388, vertices_644, vertices_772, vertices_88, vertices_152, vertices_536, vertices_104, vertices_168, vertices_296, vertices_552, vertices_328, vertices_392, vertices_648, vertices_464, vertices_592, vertices_352, vertices_608, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_611), (false, vertices_163), (false, vertices_387), (false, vertices_597), (false, vertices_357), (false, vertices_425), (true, vertices_642), (true, vertices_148), (true, vertices_388), (true, vertices_644), (true, vertices_88), (true, vertices_152), (true, vertices_536), (true, vertices_104), (true, vertices_552), (true, vertices_328), (true, vertices_648), (true, vertices_464), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 15 else
  if p.val = (false, vertices_611) then 16 else
  if p.val = (false, vertices_163) then 0 else
  if p.val = (false, vertices_387) then 1 else
  if p.val = (false, vertices_597) then 18 else
  if p.val = (false, vertices_357) then 19 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (true, vertices_642) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_388) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_464) then 23 else
  if p.val = (true, vertices_896) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_163), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(true, vertices_464), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 5 6 7 464
cert_row_4 1 0 2 4 6 8 682 162 1
cert_row_4 2 1 2 3 6 8 668 148 1
cert_row_4 3 2 3 4 5 8 632 88 2
cert_rows
cert_pivot_2 7 0 1 2
cert_heightProof 4
cert_coverFacet 0 682
cert_cover_5 0 1 0 2 4 6 162 682 1
cert_coverFacet 1 898
cert_cover_2 1 6 0 7 8 386 898 3
cert_coverFacet 2 668
cert_cover_5 2 2 1 2 3 6 148 668 1
cert_coverFacet 3 468
cert_cover_5 3 0 1 3 5 6 84 468 3
cert_coverFacet 4 900
cert_cover_2 4 6 1 7 8 388 900 3
cert_coverFacet 5 632
cert_cover_5 5 3 2 3 4 5 88 632 2
cert_coverFacet 6 472
cert_cover_5 6 0 2 3 5 6 88 472 3
cert_coverFacet 7 360
cert_cover_2 7 4 2 5 7 104 360 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0506

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m15e10q1_0507.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0507

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 651, 771, 61, 157, 357, 809, 466, 866, 706, 628, 340, 404, 696, 720, 131, 259, 515, 29, 37, 133, 261, 41, 137, 521, 289, 769, 194, 322, 578, 386, 642, 770, 52, 84, 148, 276, 100, 324, 388, 56, 152, 552, 648, 560, 208, 336, 592, 400, 656, 352, 608, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_651, vertices_771, vertices_61, vertices_157, vertices_357, vertices_809, vertices_466, vertices_866, vertices_706, vertices_628, vertices_340, vertices_404, vertices_696, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_29, vertices_37, vertices_133, vertices_261, vertices_41, vertices_137, vertices_521, vertices_289, vertices_769, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_52, vertices_84, vertices_148, vertices_276, vertices_100, vertices_324, vertices_388, vertices_56, vertices_152, vertices_552, vertices_648, vertices_560, vertices_208, vertices_336, vertices_592, vertices_400, vertices_656, vertices_352, vertices_608, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_651), (false, vertices_771), (false, vertices_61), (false, vertices_157), (false, vertices_357), (false, vertices_809), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_84), (true, vertices_276), (true, vertices_560), (true, vertices_208), (true, vertices_336), (true, vertices_592), (true, vertices_400), (true, vertices_656), (true, vertices_608), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 15 else
  if p.val = (false, vertices_651) then 16 else
  if p.val = (false, vertices_771) then 0 else
  if p.val = (false, vertices_61) then 18 else
  if p.val = (false, vertices_157) then 19 else
  if p.val = (false, vertices_357) then 20 else
  if p.val = (false, vertices_809) then 22 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_560) then 6 else
  if p.val = (true, vertices_208) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_656) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_61), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 4 5 8 628 52 3
cert_row_4 1 2 3 4 6 8 696 56 3
cert_row_4 2 0 3 5 6 7 466 194 1
cert_row_4 3 0 4 5 7 8 866 322 1
cert_rows
cert_pivot_2 1 2 3 0
cert_heightProof 4
cert_coverFacet 0 466
cert_cover_5 0 2 0 3 5 6 194 466 1
cert_coverFacet 1 866
cert_cover_5 1 3 0 4 5 7 322 866 1
cert_coverFacet 2 706
cert_cover_2 2 5 0 6 8 194 706 3
cert_coverFacet 3 628
cert_cover_5 3 0 1 3 4 5 52 628 3
cert_coverFacet 4 340
cert_cover_2 4 3 1 5 7 84 340 3
cert_coverFacet 5 404
cert_cover_2 5 3 1 6 7 148 404 3
cert_coverFacet 6 696
cert_cover_5 6 1 2 3 4 6 56 696 3
cert_coverFacet 7 720
cert_cover_2 7 5 3 6 8 208 720 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0507

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m15e10q1_0508.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0508

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 563, 355, 665, 241, 961, 558, 358, 348, 108, 908, 120, 568, 408, 464, 35, 259, 515, 49, 145, 529, 97, 193, 321, 641, 769, 38, 262, 518, 354, 546, 44, 76, 268, 524, 100, 324, 772, 56, 88, 152, 280, 536, 104, 552, 392, 648, 112, 560, 208, 336, 400, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_563, vertices_355, vertices_665, vertices_241, vertices_961, vertices_558, vertices_358, vertices_348, vertices_108, vertices_908, vertices_120, vertices_568, vertices_408, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_259, vertices_515, vertices_49, vertices_145, vertices_529, vertices_97, vertices_193, vertices_321, vertices_641, vertices_769, vertices_38, vertices_262, vertices_518, vertices_354, vertices_546, vertices_44, vertices_76, vertices_268, vertices_524, vertices_100, vertices_324, vertices_772, vertices_56, vertices_88, vertices_152, vertices_280, vertices_536, vertices_104, vertices_552, vertices_392, vertices_648, vertices_112, vertices_560, vertices_208, vertices_336, vertices_400, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_563), (false, vertices_355), (false, vertices_665), (false, vertices_241), (false, vertices_961), (true, vertices_38), (true, vertices_44), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_100), (true, vertices_324), (true, vertices_56), (true, vertices_88), (true, vertices_280), (true, vertices_104), (true, vertices_552), (true, vertices_392), (true, vertices_336), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 20 22 24 25 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 16 else
  if p.val = (false, vertices_563) then 17 else
  if p.val = (false, vertices_355) then 18 else
  if p.val = (false, vertices_665) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (false, vertices_961) then 26 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_44) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_100) then 5 else
  if p.val = (true, vertices_324) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 5 7 348 76 2
cert_row_2 1 0 4 5 7 354
cert_row_4 2 0 1 2 4 8 558 38 2
cert_row_4 3 1 2 6 7 8 908 268 2
cert_rows
cert_pivot_2 3 5 0 1
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 2 0 1 2 4 38 558 2
cert_coverFacet 1 358
cert_cover_5 1 1 0 1 4 5 38 358 3
cert_coverFacet 2 348
cert_cover_5 2 0 1 2 3 5 76 348 2
cert_coverFacet 3 108
cert_cover_2 3 2 1 4 5 44 108 3
cert_coverFacet 4 908
cert_cover_5 4 3 1 2 6 7 268 908 2
cert_coverFacet 5 120
cert_cover_2 5 3 2 4 5 56 120 3
cert_coverFacet 6 568
cert_cover_2 6 3 2 4 8 56 568 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 464
cert_cover_2 8 5 3 6 7 208 464 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0508

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m15e10q1_0509.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0509

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [167, 555, 643, 301, 333, 213, 713, 818, 722, 402, 418, 852, 404, 420, 872, 35, 131, 515, 269, 37, 69, 133, 41, 73, 521, 193, 641, 146, 274, 530, 162, 290, 546, 386, 642, 84, 148, 276, 164, 292, 324, 388, 296, 552, 328, 584, 208, 592, 400, 784, 416, 800, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_167, vertices_555, vertices_643, vertices_301, vertices_333, vertices_213, vertices_713, vertices_818, vertices_722, vertices_402, vertices_418, vertices_852, vertices_404, vertices_420, vertices_872] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_515, vertices_269, vertices_37, vertices_69, vertices_133, vertices_41, vertices_73, vertices_521, vertices_193, vertices_641, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_84, vertices_148, vertices_276, vertices_164, vertices_292, vertices_324, vertices_388, vertices_296, vertices_552, vertices_328, vertices_584, vertices_208, vertices_592, vertices_400, vertices_784, vertices_416, vertices_800, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_167), (false, vertices_555), (false, vertices_643), (false, vertices_301), (false, vertices_333), (false, vertices_213), (false, vertices_713), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_386), (true, vertices_276), (true, vertices_388), (true, vertices_592), (true, vertices_400), (true, vertices_784), (true, vertices_416), (true, vertices_800), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_167) then 15 else
  if p.val = (false, vertices_555) then 16 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_301) then 18 else
  if p.val = (false, vertices_333) then 19 else
  if p.val = (false, vertices_213) then 20 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_592) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_416) then 11 else
  if p.val = (true, vertices_800) then 12 else
  if p.val = (true, vertices_832) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_167), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 6 8 722 146 2
cert_row_4 1 0 3 4 7 8 818 274 2
cert_row_4 2 1 3 5 7 8 852 84 3
cert_row_4 3 2 4 5 7 8 872 296 2
cert_rows
cert_pivot_2 6 0 1 2
cert_heightProof 4
cert_coverFacet 0 818
cert_cover_5 0 1 0 3 4 7 274 818 2
cert_coverFacet 1 722
cert_cover_5 1 0 0 3 5 6 146 722 2
cert_coverFacet 2 402
cert_cover_2 2 3 0 6 7 146 402 3
cert_coverFacet 3 418
cert_cover_2 3 4 0 6 7 162 418 3
cert_coverFacet 4 852
cert_cover_5 4 2 1 3 5 7 84 852 3
cert_coverFacet 5 404
cert_cover_2 5 3 1 6 7 148 404 3
cert_coverFacet 6 420
cert_cover_2 6 4 1 6 7 164 420 3
cert_coverFacet 7 872
cert_cover_5 7 3 2 4 5 7 296 872 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0509

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e10q1_0510.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0510

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 29, 589, 565, 409, 809, 177, 710, 842, 690, 802, 450, 348, 468, 660, 13, 21, 517, 25, 265, 521, 49, 145, 161, 289, 545, 385, 162, 290, 546, 194, 322, 578, 386, 642, 770, 28, 76, 340, 148, 532, 196, 580, 644, 280, 328, 584, 776, 176, 560, 400, 656, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_29, vertices_589, vertices_565, vertices_409, vertices_809, vertices_177, vertices_710, vertices_842, vertices_690, vertices_802, vertices_450, vertices_348, vertices_468, vertices_660] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_517, vertices_25, vertices_265, vertices_521, vertices_49, vertices_145, vertices_161, vertices_289, vertices_545, vertices_385, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_76, vertices_340, vertices_148, vertices_532, vertices_196, vertices_580, vertices_644, vertices_280, vertices_328, vertices_584, vertices_776, vertices_176, vertices_560, vertices_400, vertices_656, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_29), (false, vertices_589), (false, vertices_565), (false, vertices_409), (false, vertices_809), (false, vertices_177), (true, vertices_546), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_642), (true, vertices_770), (true, vertices_340), (true, vertices_148), (true, vertices_196), (true, vertices_644), (true, vertices_328), (true, vertices_656), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 15 else
  if p.val = (false, vertices_29) then 0 else
  if p.val = (false, vertices_589) then 17 else
  if p.val = (false, vertices_565) then 18 else
  if p.val = (false, vertices_409) then 21 else
  if p.val = (false, vertices_809) then 22 else
  if p.val = (false, vertices_177) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_340) then 19 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_448) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_29), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_177), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_340), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 7 8 842 322 1
cert_row_2 1 1 3 5 7 340
cert_row_4 2 0 1 5 6 8 710 194 1
cert_row_4 3 0 3 4 6 8 690 162 1
cert_rows
cert_pivot_2 2 7 1 0
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 2 0 1 5 6 194 710 1
cert_coverFacet 1 842
cert_cover_5 1 0 0 2 5 7 322 842 1
cert_coverFacet 2 690
cert_cover_5 2 3 0 3 4 6 162 690 1
cert_coverFacet 3 802
cert_cover_2 3 4 0 7 8 290 802 3
cert_coverFacet 4 450
cert_cover_2 4 5 0 6 7 194 450 3
cert_coverFacet 5 348
cert_cover_5 5 1 1 2 3 5 28 348 3
cert_coverFacet 6 468
cert_cover_5 6 1 1 3 5 6 340 468 3
cert_coverFacet 7 660
cert_cover_2 7 3 1 6 8 148 660 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0510

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e10q1_0511.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0511

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 285, 565, 421, 601, 905, 230, 842, 466, 610, 898, 628, 212, 404, 344, 21, 37, 261, 25, 265, 521, 529, 161, 545, 385, 641, 98, 162, 546, 194, 322, 578, 386, 642, 770, 564, 84, 148, 276, 100, 164, 196, 388, 88, 280, 328, 584, 776, 208, 336, 592, 400, 608, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_285, vertices_565, vertices_421, vertices_601, vertices_905, vertices_230, vertices_842, vertices_466, vertices_610, vertices_898, vertices_628, vertices_212, vertices_404, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_261, vertices_25, vertices_265, vertices_521, vertices_529, vertices_161, vertices_545, vertices_385, vertices_641, vertices_98, vertices_162, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_564, vertices_84, vertices_148, vertices_276, vertices_100, vertices_164, vertices_196, vertices_388, vertices_88, vertices_280, vertices_328, vertices_584, vertices_776, vertices_208, vertices_336, vertices_592, vertices_400, vertices_608, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_285), (false, vertices_565), (false, vertices_421), (false, vertices_601), (false, vertices_905), (true, vertices_98), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_386), (true, vertices_770), (true, vertices_84), (true, vertices_148), (true, vertices_100), (true, vertices_196), (true, vertices_328), (true, vertices_208), (true, vertices_336), (true, vertices_400), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_285) then 18 else
  if p.val = (false, vertices_565) then 19 else
  if p.val = (false, vertices_421) then 20 else
  if p.val = (false, vertices_601) then 22 else
  if p.val = (false, vertices_905) then 23 else
  if p.val = (true, vertices_98) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_608) then 14 else
  0
cert_priority
cert_nodeAtPriority_36 0 98 1 194 2 322 578 386 770 84 148 100 196 328 208 336 400 608 675 285 565 421 601 905
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 7 8 842 322 1
cert_row_2 1 1 3 4 8 564
cert_row_4 2 0 1 4 5 6 230 98 1
cert_row_4 3 0 3 5 6 7 466 194 1
cert_rows
cert_pivot_2 2 8 1 0
cert_heightProof 4
cert_coverFacet 0 230
cert_cover_5 0 2 0 1 4 5 98 230 1
cert_coverFacet 1 842
cert_cover_5 1 0 0 2 5 7 322 842 1
cert_coverFacet 2 466
cert_cover_5 2 3 0 3 5 6 194 466 1
cert_coverFacet 3 610
cert_cover_2 3 4 0 5 8 98 610 3
cert_coverFacet 4 898
cert_cover_2 4 6 0 7 8 386 898 3
cert_coverFacet 5 628
cert_cover_5 5 1 1 3 4 5 564 628 3
cert_coverFacet 6 212
cert_cover_2 6 3 1 5 6 84 212 3
cert_coverFacet 7 404
cert_cover_2 7 3 1 6 7 148 404 3
cert_coverFacet 8 344
cert_cover_2 8 3 2 5 7 88 344 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0511

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e10q1_0512.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0512

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 651, 179, 275, 309, 613, 673, 602, 154, 850, 484, 836, 472, 744, 432, 19, 131, 259, 515, 37, 261, 517, 49, 273, 161, 545, 641, 26, 138, 522, 594, 146, 274, 770, 100, 292, 324, 580, 772, 88, 152, 200, 584, 648, 176, 304, 336, 400, 224, 608, 416, 672, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_651, vertices_179, vertices_275, vertices_309, vertices_613, vertices_673, vertices_602, vertices_154, vertices_850, vertices_484, vertices_836, vertices_472, vertices_744, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_37, vertices_261, vertices_517, vertices_49, vertices_273, vertices_161, vertices_545, vertices_641, vertices_26, vertices_138, vertices_522, vertices_594, vertices_146, vertices_274, vertices_770, vertices_100, vertices_292, vertices_324, vertices_580, vertices_772, vertices_88, vertices_152, vertices_200, vertices_584, vertices_648, vertices_176, vertices_304, vertices_336, vertices_400, vertices_224, vertices_608, vertices_416, vertices_672, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_651), (false, vertices_179), (false, vertices_275), (false, vertices_309), (false, vertices_613), (false, vertices_673), (true, vertices_26), (true, vertices_594), (true, vertices_324), (true, vertices_88), (true, vertices_152), (true, vertices_200), (true, vertices_584), (true, vertices_336), (true, vertices_400), (true, vertices_224), (true, vertices_416), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 14 22 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 15 else
  if p.val = (false, vertices_651) then 19 else
  if p.val = (false, vertices_179) then 20 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_309) then 16 else
  if p.val = (false, vertices_613) then 17 else
  if p.val = (false, vertices_673) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_594) then 21 else
  if p.val = (true, vertices_324) then 3 else
  if p.val = (true, vertices_88) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_200) then 6 else
  if p.val = (true, vertices_584) then 7 else
  if p.val = (true, vertices_336) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_416) then 11 else
  if p.val = (true, vertices_448) then 12 else
  if p.val = (true, vertices_832) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_275), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_673), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_594), by decide +kernel⟩
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
cert_row_2 0 0 3 5 8 594
cert_row_4 1 1 4 5 6 7 484 100 3
cert_row_4 2 2 3 5 6 7 472 88 3
cert_row_4 3 2 4 5 6 8 744 200 1
cert_rows
cert_pivot_2 0 1 3 2
cert_heightProof 4
cert_coverFacet 0 602
cert_cover_5 0 0 0 2 3 5 26 602 3
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 850
cert_cover_5 2 0 0 3 5 7 594 850 3
cert_coverFacet 3 484
cert_cover_5 3 1 1 4 5 6 100 484 3
cert_coverFacet 4 836
cert_cover_2 4 5 1 7 8 324 836 3
cert_coverFacet 5 472
cert_cover_5 5 2 2 3 5 6 88 472 3
cert_coverFacet 6 744
cert_cover_5 6 3 2 4 5 6 200 744 1
cert_coverFacet 7 432
cert_cover_2 7 4 3 6 7 176 432 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0512

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e10q1_0513.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0513

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [355, 837, 665, 425, 777, 737, 94, 334, 154, 394, 114, 690, 418, 796, 628, 137, 265, 521, 97, 161, 289, 321, 577, 641, 769, 78, 26, 138, 266, 50, 82, 146, 98, 162, 290, 322, 386, 28, 268, 84, 532, 324, 580, 772, 152, 536, 392, 776, 112, 560, 656, 608, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_355, vertices_837, vertices_665, vertices_425, vertices_777, vertices_737, vertices_94, vertices_334, vertices_154, vertices_394, vertices_114, vertices_690, vertices_418, vertices_796, vertices_628] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_97, vertices_161, vertices_289, vertices_321, vertices_577, vertices_641, vertices_769, vertices_78, vertices_26, vertices_138, vertices_266, vertices_50, vertices_82, vertices_146, vertices_98, vertices_162, vertices_290, vertices_322, vertices_386, vertices_28, vertices_268, vertices_84, vertices_532, vertices_324, vertices_580, vertices_772, vertices_152, vertices_536, vertices_392, vertices_776, vertices_112, vertices_560, vertices_656, vertices_608, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_355), (false, vertices_837), (false, vertices_665), (false, vertices_425), (false, vertices_777), (false, vertices_737), (true, vertices_78), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_50), (true, vertices_82), (true, vertices_146), (true, vertices_162), (true, vertices_386), (true, vertices_28), (true, vertices_268), (true, vertices_84), (true, vertices_532), (true, vertices_112), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_355) then 16 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_665) then 21 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_162) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_268) then 10 else
  if p.val = (true, vertices_84) then 11 else
  if p.val = (true, vertices_532) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_560) then 14 else
  0
cert_priority
cert_nodeAtPriority_32 777 26 138 266 50 82 146 162 386 28 268 84 532 112 560 355 78 837 665 425 737
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 6 8 690 50 3
cert_row_2 1 0 1 2 5 78
cert_row_4 2 1 2 3 7 8 796 28 3
cert_row_4 3 1 3 4 5 8 628 84 2
cert_rows
cert_pivot_2 6 0 2 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 1 0 1 2 3 78 94 3
cert_coverFacet 1 334
cert_cover_5 1 1 0 1 2 7 78 334 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 114
cert_cover_2 4 3 0 4 5 50 114 3
cert_coverFacet 5 690
cert_cover_5 5 0 0 3 4 6 50 690 3
cert_coverFacet 6 418
cert_cover_2 6 4 0 6 7 162 418 3
cert_coverFacet 7 796
cert_cover_5 7 2 1 2 3 7 28 796 3
cert_coverFacet 8 628
cert_cover_5 8 3 1 3 4 5 84 628 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0513

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e10q1_0514.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0514

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [295, 555, 787, 173, 205, 325, 841, 722, 402, 418, 674, 436, 212, 852, 744, 35, 259, 515, 141, 37, 69, 261, 41, 73, 521, 321, 769, 146, 274, 530, 162, 290, 546, 386, 642, 84, 148, 276, 164, 292, 196, 324, 168, 552, 200, 584, 208, 592, 400, 784, 416, 672, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_555, vertices_787, vertices_173, vertices_205, vertices_325, vertices_841, vertices_722, vertices_402, vertices_418, vertices_674, vertices_436, vertices_212, vertices_852, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_259, vertices_515, vertices_141, vertices_37, vertices_69, vertices_261, vertices_41, vertices_73, vertices_521, vertices_321, vertices_769, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_84, vertices_148, vertices_276, vertices_164, vertices_292, vertices_196, vertices_324, vertices_168, vertices_552, vertices_200, vertices_584, vertices_208, vertices_592, vertices_400, vertices_784, vertices_416, vertices_672, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_555), (false, vertices_787), (false, vertices_173), (false, vertices_205), (false, vertices_325), (false, vertices_841), (true, vertices_146), (true, vertices_162), (true, vertices_386), (true, vertices_642), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_208), (true, vertices_592), (true, vertices_400), (true, vertices_416), (true, vertices_672), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 15 else
  if p.val = (false, vertices_555) then 16 else
  if p.val = (false, vertices_787) then 17 else
  if p.val = (false, vertices_173) then 19 else
  if p.val = (false, vertices_205) then 20 else
  if p.val = (false, vertices_325) then 0 else
  if p.val = (false, vertices_841) then 22 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_208) then 8 else
  if p.val = (true, vertices_592) then 9 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_416) then 11 else
  if p.val = (true, vertices_672) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_325), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 6 8 722 146 2
cert_row_4 1 2 4 5 6 8 744 168 2
cert_row_4 2 1 3 4 6 7 436 148 2
cert_row_4 3 1 3 5 7 8 852 84 3
cert_rows
cert_pivot_2 0 2 4 1
cert_heightProof 4
cert_coverFacet 0 722
cert_cover_5 0 0 0 3 5 6 146 722 2
cert_coverFacet 1 402
cert_cover_2 1 3 0 6 7 146 402 3
cert_coverFacet 2 418
cert_cover_2 2 4 0 6 7 162 418 3
cert_coverFacet 3 674
cert_cover_2 3 4 0 6 8 162 674 3
cert_coverFacet 4 436
cert_cover_5 4 2 1 3 4 6 148 436 2
cert_coverFacet 5 212
cert_cover_2 5 3 1 5 6 84 212 3
cert_coverFacet 6 852
cert_cover_5 6 3 1 3 5 7 84 852 3
cert_coverFacet 7 744
cert_cover_5 7 1 2 4 5 6 168 744 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0514

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m15e10q1_0515.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0515

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 53, 789, 421, 681, 625, 454, 618, 202, 650, 850, 188, 220, 340, 120, 21, 37, 261, 49, 529, 161, 545, 385, 641, 769, 74, 138, 522, 194, 322, 578, 386, 642, 770, 156, 52, 84, 276, 164, 196, 324, 388, 56, 88, 104, 168, 552, 200, 648, 112, 336, 592, 784, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_53, vertices_789, vertices_421, vertices_681, vertices_625, vertices_454, vertices_618, vertices_202, vertices_650, vertices_850, vertices_188, vertices_220, vertices_340, vertices_120] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_261, vertices_49, vertices_529, vertices_161, vertices_545, vertices_385, vertices_641, vertices_769, vertices_74, vertices_138, vertices_522, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_156, vertices_52, vertices_84, vertices_276, vertices_164, vertices_196, vertices_324, vertices_388, vertices_56, vertices_88, vertices_104, vertices_168, vertices_552, vertices_200, vertices_648, vertices_112, vertices_336, vertices_592, vertices_784, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_53), (false, vertices_789), (false, vertices_421), (false, vertices_681), (false, vertices_625), (true, vertices_74), (true, vertices_138), (true, vertices_522), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_156), (true, vertices_84), (true, vertices_196), (true, vertices_324), (true, vertices_56), (true, vertices_88), (true, vertices_104), (true, vertices_200), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 16 else
  if p.val = (false, vertices_53) then 0 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_421) then 19 else
  if p.val = (false, vertices_681) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_156) then 20 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_88) then 11 else
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_200) then 13 else
  if p.val = (true, vertices_336) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_53), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_156), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
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
cert_row_4 0 0 2 4 5 8 618 74 2
cert_row_2 1 1 2 3 6 156
cert_row_4 2 0 1 5 6 7 454 194 1
cert_row_4 3 0 3 5 7 8 850 322 1
cert_rows
cert_pivot_2 4 2 1 0
cert_heightProof 4
cert_coverFacet 0 454
cert_cover_5 0 2 0 1 5 6 194 454 1
cert_coverFacet 1 618
cert_cover_5 1 0 0 2 4 5 74 618 2
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 850
cert_cover_5 4 3 0 3 5 7 322 850 1
cert_coverFacet 5 188
cert_cover_5 5 1 1 2 3 4 156 188 3
cert_coverFacet 6 220
cert_cover_5 6 1 1 2 3 5 156 220 3
cert_coverFacet 7 340
cert_cover_2 7 3 1 5 7 84 340 3
cert_coverFacet 8 120
cert_cover_2 8 3 2 4 5 56 120 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0515

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m15e10q1_0516.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0516

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 93, 665, 361, 553, 241, 230, 358, 390, 810, 914, 796, 332, 212, 404, 25, 41, 73, 521, 81, 145, 97, 161, 545, 641, 102, 134, 262, 162, 290, 546, 386, 642, 770, 28, 76, 268, 84, 148, 276, 196, 324, 388, 536, 296, 552, 328, 776, 208, 400, 656, 784, 224, 352]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_93, vertices_665, vertices_361, vertices_553, vertices_241, vertices_230, vertices_358, vertices_390, vertices_810, vertices_914, vertices_796, vertices_332, vertices_212, vertices_404] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_73, vertices_521, vertices_81, vertices_145, vertices_97, vertices_161, vertices_545, vertices_641, vertices_102, vertices_134, vertices_262, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_28, vertices_76, vertices_268, vertices_84, vertices_148, vertices_276, vertices_196, vertices_324, vertices_388, vertices_536, vertices_296, vertices_552, vertices_328, vertices_776, vertices_208, vertices_400, vertices_656, vertices_784, vertices_224, vertices_352] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_93), (false, vertices_665), (false, vertices_361), (false, vertices_553), (false, vertices_241), (true, vertices_102), (true, vertices_134), (true, vertices_262), (true, vertices_290), (true, vertices_386), (true, vertices_770), (true, vertices_268), (true, vertices_148), (true, vertices_276), (true, vertices_196), (true, vertices_324), (true, vertices_388), (true, vertices_776), (true, vertices_400), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_93) then 19 else
  if p.val = (false, vertices_665) then 21 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_241) then 24 else
  if p.val = (true, vertices_102) then 17 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_784) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 553 134 262 290 386 770 268 148 276 196 324 388 776 400 784 675 102 93 665 361 241
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 4 5 102
cert_row_4 1 0 2 4 7 8 810 290 1
cert_row_4 2 0 3 6 7 8 914 386 1
cert_row_4 3 1 2 3 7 8 796 28 3
cert_rows
cert_pivot_2 5 4 0 1
cert_heightProof 4
cert_coverFacet 0 230
cert_cover_5 0 0 0 1 4 6 102 230 3
cert_coverFacet 1 358
cert_cover_5 1 0 0 1 4 7 102 358 3
cert_coverFacet 2 390
cert_cover_2 2 1 0 6 7 134 390 3
cert_coverFacet 3 810
cert_cover_5 3 1 0 2 4 7 290 810 1
cert_coverFacet 4 914
cert_cover_5 4 2 0 3 6 7 386 914 1
cert_coverFacet 5 796
cert_cover_5 5 3 1 2 3 7 28 796 3
cert_coverFacet 6 332
cert_cover_2 6 2 1 5 7 76 332 3
cert_coverFacet 7 212
cert_cover_2 7 3 1 5 6 84 212 3
cert_coverFacet 8 404
cert_cover_2 8 3 1 6 7 148 404 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0516

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m15e10q1_0517.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0517

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [203, 805, 425, 841, 625, 225, 286, 590, 598, 394, 242, 402, 780, 436, 564, 73, 137, 265, 97, 161, 289, 545, 193, 577, 769, 14, 22, 582, 74, 138, 266, 82, 146, 274, 194, 386, 268, 524, 52, 276, 532, 292, 548, 772, 584, 392, 776, 112, 176, 560, 592, 400, 224, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_203, vertices_805, vertices_425, vertices_841, vertices_625, vertices_225, vertices_286, vertices_590, vertices_598, vertices_394, vertices_242, vertices_402, vertices_780, vertices_436, vertices_564] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_265, vertices_97, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_769, vertices_14, vertices_22, vertices_582, vertices_74, vertices_138, vertices_266, vertices_82, vertices_146, vertices_274, vertices_194, vertices_386, vertices_268, vertices_524, vertices_52, vertices_276, vertices_532, vertices_292, vertices_548, vertices_772, vertices_584, vertices_392, vertices_776, vertices_112, vertices_176, vertices_560, vertices_592, vertices_400, vertices_224, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_203), (false, vertices_805), (false, vertices_425), (false, vertices_841), (false, vertices_625), (false, vertices_225), (true, vertices_14), (true, vertices_22), (true, vertices_582), (true, vertices_266), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_386), (true, vertices_268), (true, vertices_524), (true, vertices_52), (true, vertices_276), (true, vertices_532), (true, vertices_176), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_203) then 16 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_841) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (false, vertices_225) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_582) then 17 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_52) then 10 else
  if p.val = (true, vertices_276) then 11 else
  if p.val = (true, vertices_532) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 225 14 22 266 82 146 274 386 268 524 52 276 532 176 400 203 582 805 425 841 625
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 8 582
cert_row_4 1 0 1 2 3 7 286 14 3
cert_row_4 2 0 3 4 5 6 242 82 2
cert_row_4 3 1 3 4 6 7 436 52 3
cert_rows
cert_pivot_2 8 2 0 1
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 1 0 1 2 3 14 286 3
cert_coverFacet 1 590
cert_cover_5 1 0 0 1 2 5 14 590 3
cert_coverFacet 2 598
cert_cover_5 2 0 0 1 3 5 22 598 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 242
cert_cover_5 4 2 0 3 4 5 82 242 2
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 436
cert_cover_5 7 3 1 3 4 6 52 436 3
cert_coverFacet 8 564
cert_cover_2 8 3 1 4 8 52 564 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0517

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m15e10q1_0518.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0518

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [107, 267, 707, 771, 901, 425, 241, 542, 270, 774, 602, 284, 436, 724, 376, 11, 67, 259, 515, 41, 265, 97, 161, 193, 385, 641, 769, 14, 262, 518, 538, 74, 266, 578, 770, 28, 268, 148, 276, 532, 388, 644, 772, 88, 280, 104, 296, 112, 176, 304, 208, 592, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_107, vertices_267, vertices_707, vertices_771, vertices_901, vertices_425, vertices_241, vertices_542, vertices_270, vertices_774, vertices_602, vertices_284, vertices_436, vertices_724, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_67, vertices_259, vertices_515, vertices_41, vertices_265, vertices_97, vertices_161, vertices_193, vertices_385, vertices_641, vertices_769, vertices_14, vertices_262, vertices_518, vertices_538, vertices_74, vertices_266, vertices_578, vertices_770, vertices_28, vertices_268, vertices_148, vertices_276, vertices_532, vertices_388, vertices_644, vertices_772, vertices_88, vertices_280, vertices_104, vertices_296, vertices_112, vertices_176, vertices_304, vertices_208, vertices_592, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_107), (false, vertices_267), (false, vertices_707), (false, vertices_771), (false, vertices_901), (false, vertices_425), (false, vertices_241), (true, vertices_14), (true, vertices_262), (true, vertices_518), (true, vertices_538), (true, vertices_28), (true, vertices_268), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_88), (true, vertices_280), (true, vertices_304), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_107) then 15 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_771) then 1 else
  if p.val = (false, vertices_901) then 19 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_538) then 17 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_592) then 13 else
  0
cert_priority
cert_nodeAtPriority_23 267 771 14 262 518 28 268 148 276 532 88 280 304 592 107 707 538 901 425 241
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 8 538
cert_row_4 1 1 3 5 6 8 724 148 2
cert_row_4 2 1 3 4 6 7 436 148 2
cert_row_4 3 2 3 4 5 7 376 88 2
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 14 542 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 602
cert_cover_5 3 0 0 2 3 5 538 602 3
cert_coverFacet 4 284
cert_cover_2 4 2 1 3 7 28 284 3
cert_coverFacet 5 436
cert_cover_5 5 2 1 3 4 6 148 436 2
cert_coverFacet 6 724
cert_cover_5 6 1 1 3 5 6 148 724 2
cert_coverFacet 7 376
cert_cover_5 7 3 2 3 4 5 88 376 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0518

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m15e10q1_0519.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0519

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 205, 525, 357, 549, 665, 961, 30, 558, 118, 538, 370, 914, 92, 472, 13, 37, 69, 517, 137, 521, 289, 545, 193, 321, 641, 769, 14, 22, 38, 26, 522, 114, 274, 530, 290, 546, 770, 28, 76, 524, 84, 100, 548, 88, 152, 536, 200, 336, 400, 656, 352, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_205, vertices_525, vertices_357, vertices_549, vertices_665, vertices_961, vertices_30, vertices_558, vertices_118, vertices_538, vertices_370, vertices_914, vertices_92, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_69, vertices_517, vertices_137, vertices_521, vertices_289, vertices_545, vertices_193, vertices_321, vertices_641, vertices_769, vertices_14, vertices_22, vertices_38, vertices_26, vertices_522, vertices_114, vertices_274, vertices_530, vertices_290, vertices_546, vertices_770, vertices_28, vertices_76, vertices_524, vertices_84, vertices_100, vertices_548, vertices_88, vertices_152, vertices_536, vertices_200, vertices_336, vertices_400, vertices_656, vertices_352, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_205), (false, vertices_525), (false, vertices_357), (false, vertices_549), (false, vertices_665), (false, vertices_961), (true, vertices_14), (true, vertices_22), (true, vertices_38), (true, vertices_26), (true, vertices_522), (true, vertices_114), (true, vertices_274), (true, vertices_530), (true, vertices_28), (true, vertices_84), (true, vertices_88), (true, vertices_336), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 23 24 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 15 else
  if p.val = (false, vertices_205) then 18 else
  if p.val = (false, vertices_525) then 0 else
  if p.val = (false, vertices_357) then 19 else
  if p.val = (false, vertices_549) then 1 else
  if p.val = (false, vertices_665) then 21 else
  if p.val = (false, vertices_961) then 25 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_22) then 3 else
  if p.val = (true, vertices_38) then 4 else
  if p.val = (true, vertices_26) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_114) then 16 else
  if p.val = (true, vertices_274) then 7 else
  if p.val = (true, vertices_530) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_84) then 10 else
  if p.val = (true, vertices_88) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_400) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_549), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_114), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 8 558 14 3
cert_row_2 1 0 3 4 5 114
cert_row_4 2 0 3 6 7 8 914 274 2
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 1 4 0 2
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 558
cert_cover_5 1 0 0 1 2 4 14 558 3
cert_coverFacet 2 118
cert_cover_5 2 1 0 1 3 4 22 118 3
cert_coverFacet 3 538
cert_cover_2 3 2 0 3 8 26 538 3
cert_coverFacet 4 370
cert_cover_5 4 1 0 3 4 7 114 370 3
cert_coverFacet 5 914
cert_cover_5 5 2 0 3 6 7 274 914 2
cert_coverFacet 6 92
cert_cover_2 6 2 1 3 5 28 92 3
cert_coverFacet 7 472
cert_cover_5 7 3 2 3 5 6 88 472 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0519

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m15e10q1_0520.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0520

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 61, 269, 213, 389, 361, 625, 398, 654, 778, 722, 866, 540, 660, 824, 13, 21, 133, 261, 41, 265, 49, 81, 97, 193, 321, 385, 142, 266, 522, 194, 322, 578, 386, 642, 770, 28, 268, 524, 148, 532, 388, 644, 56, 536, 296, 776, 560, 208, 592, 656, 352, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_61, vertices_269, vertices_213, vertices_389, vertices_361, vertices_625, vertices_398, vertices_654, vertices_778, vertices_722, vertices_866, vertices_540, vertices_660, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_133, vertices_261, vertices_41, vertices_265, vertices_49, vertices_81, vertices_97, vertices_193, vertices_321, vertices_385, vertices_142, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_268, vertices_524, vertices_148, vertices_532, vertices_388, vertices_644, vertices_56, vertices_536, vertices_296, vertices_776, vertices_560, vertices_208, vertices_592, vertices_656, vertices_352, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_61), (false, vertices_269), (false, vertices_213), (false, vertices_389), (false, vertices_361), (false, vertices_625), (true, vertices_142), (true, vertices_266), (true, vertices_522), (true, vertices_578), (true, vertices_642), (true, vertices_770), (true, vertices_524), (true, vertices_532), (true, vertices_644), (true, vertices_536), (true, vertices_776), (true, vertices_656), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 15 else
  if p.val = (false, vertices_61) then 18 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_213) then 19 else
  if p.val = (false, vertices_389) then 1 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_625) then 23 else
  if p.val = (true, vertices_142) then 16 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_800) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 0 269 1 389 266 522 578 642 770 524 532 644 536 776 656 800 451 142 61 213 361 625
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 6 142
cert_row_4 1 0 3 5 6 8 722 194 1
cert_row_4 2 0 4 5 7 8 866 322 1
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 7 142 398 3
cert_coverFacet 1 654
cert_cover_5 1 0 0 1 2 8 142 654 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 722
cert_cover_5 3 1 0 3 5 6 194 722 1
cert_coverFacet 4 866
cert_cover_5 4 2 0 4 5 7 322 866 1
cert_coverFacet 5 540
cert_cover_2 5 2 1 3 8 28 540 3
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 824
cert_cover_5 7 3 2 3 4 7 56 824 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0520

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e10q1_0521.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0521

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [211, 301, 597, 789, 229, 433, 782, 394, 650, 850, 402, 738, 620, 424, 680, 533, 37, 69, 261, 81, 145, 273, 161, 289, 193, 138, 266, 522, 82, 146, 274, 194, 578, 386, 642, 770, 44, 268, 524, 100, 580, 772, 168, 296, 552, 392, 648, 592, 400, 784, 224, 608, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_211, vertices_301, vertices_597, vertices_789, vertices_229, vertices_433, vertices_782, vertices_394, vertices_650, vertices_850, vertices_402, vertices_738, vertices_620, vertices_424, vertices_680] (by decide +kernel)
  polygons := literalFinset [vertices_533, vertices_37, vertices_69, vertices_261, vertices_81, vertices_145, vertices_273, vertices_161, vertices_289, vertices_193, vertices_138, vertices_266, vertices_522, vertices_82, vertices_146, vertices_274, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_44, vertices_268, vertices_524, vertices_100, vertices_580, vertices_772, vertices_168, vertices_296, vertices_552, vertices_392, vertices_648, vertices_592, vertices_400, vertices_784, vertices_224, vertices_608, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_211), (false, vertices_301), (false, vertices_597), (false, vertices_789), (false, vertices_229), (false, vertices_433), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_578), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_524), (true, vertices_168), (true, vertices_552), (true, vertices_392), (true, vertices_648), (true, vertices_608), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 17 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_211) then 16 else
  if p.val = (false, vertices_301) then 18 else
  if p.val = (false, vertices_597) then 20 else
  if p.val = (false, vertices_789) then 21 else
  if p.val = (false, vertices_229) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_608) then 13 else
  if p.val = (true, vertices_672) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 7 8 850 82 3
cert_row_4 1 0 1 2 7 8 782 266 1
cert_row_4 2 0 4 5 6 8 738 194 1
cert_row_4 3 1 2 4 5 8 620 44 3
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 266 782 1
cert_coverFacet 1 394
cert_cover_2 1 2 0 6 7 138 394 3
cert_coverFacet 2 650
cert_cover_2 2 2 0 6 8 138 650 3
cert_coverFacet 3 850
cert_cover_5 3 0 0 3 5 7 82 850 3
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 738
cert_cover_5 5 2 0 4 5 6 194 738 1
cert_coverFacet 6 620
cert_cover_5 6 3 1 2 4 5 44 620 3
cert_coverFacet 7 424
cert_cover_2 7 4 2 6 7 168 424 3
cert_coverFacet 8 680
cert_cover_2 8 4 2 6 8 168 680 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0521

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e10q1_0522.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0522

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [295, 787, 227, 707, 665, 433, 110, 838, 412, 540, 300, 588, 788, 744, 424, 35, 195, 259, 515, 145, 273, 529, 161, 289, 641, 38, 70, 262, 98, 578, 770, 28, 44, 76, 268, 524, 276, 532, 292, 580, 772, 152, 536, 104, 168, 296, 584, 392, 648, 400, 784, 224, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_787, vertices_227, vertices_707, vertices_665, vertices_433, vertices_110, vertices_838, vertices_412, vertices_540, vertices_300, vertices_588, vertices_788, vertices_744, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_195, vertices_259, vertices_515, vertices_145, vertices_273, vertices_529, vertices_161, vertices_289, vertices_641, vertices_38, vertices_70, vertices_262, vertices_98, vertices_578, vertices_770, vertices_28, vertices_44, vertices_76, vertices_268, vertices_524, vertices_276, vertices_532, vertices_292, vertices_580, vertices_772, vertices_152, vertices_536, vertices_104, vertices_168, vertices_296, vertices_584, vertices_392, vertices_648, vertices_400, vertices_784, vertices_224, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_787), (false, vertices_227), (false, vertices_707), (false, vertices_665), (false, vertices_433), (true, vertices_70), (true, vertices_28), (true, vertices_44), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_276), (true, vertices_532), (true, vertices_580), (true, vertices_772), (true, vertices_104), (true, vertices_168), (true, vertices_296), (true, vertices_584), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 15 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 16 else
  if p.val = (false, vertices_787) then 18 else
  if p.val = (false, vertices_227) then 19 else
  if p.val = (false, vertices_707) then 20 else
  if p.val = (false, vertices_665) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_28) then 1 else
  if p.val = (true, vertices_44) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_392) then 14 else
  0
cert_priority
cert_nodeAtPriority_68 1 70 0 28 44 76 268 524 276 532 580 772 104 168 296 584 392 295 787 227 707 665 433
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 6 7 412 28 3
cert_row_4 1 0 1 5 7 8 838 70 3
cert_row_4 2 0 1 2 4 5 110 38 2
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 3 7 0 2
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 2 0 1 2 4 38 110 2
cert_coverFacet 1 838
cert_cover_5 1 1 0 1 5 7 70 838 3
cert_coverFacet 2 412
cert_cover_5 2 0 1 2 3 6 28 412 3
cert_coverFacet 3 540
cert_cover_2 3 2 1 3 8 28 540 3
cert_coverFacet 4 300
cert_cover_2 4 2 1 4 7 44 300 3
cert_coverFacet 5 588
cert_cover_2 5 2 1 5 8 76 588 3
cert_coverFacet 6 788
cert_cover_2 6 3 1 7 8 276 788 3
cert_coverFacet 7 744
cert_cover_5 7 3 2 4 5 6 104 744 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0522

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e10q1_0523.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0523

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [115, 595, 661, 277, 421, 313, 737, 790, 58, 282, 106, 714, 778, 908, 488, 83, 21, 133, 261, 49, 273, 529, 97, 161, 289, 577, 641, 26, 42, 74, 266, 522, 50, 274, 530, 98, 578, 770, 276, 532, 388, 644, 772, 56, 280, 104, 296, 200, 392, 648, 776, 224, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_115, vertices_595, vertices_661, vertices_277, vertices_421, vertices_313, vertices_737, vertices_790, vertices_58, vertices_282, vertices_106, vertices_714, vertices_778, vertices_908, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_83, vertices_21, vertices_133, vertices_261, vertices_49, vertices_273, vertices_529, vertices_97, vertices_161, vertices_289, vertices_577, vertices_641, vertices_26, vertices_42, vertices_74, vertices_266, vertices_522, vertices_50, vertices_274, vertices_530, vertices_98, vertices_578, vertices_770, vertices_276, vertices_532, vertices_388, vertices_644, vertices_772, vertices_56, vertices_280, vertices_104, vertices_296, vertices_200, vertices_392, vertices_648, vertices_776, vertices_224, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_115), (false, vertices_595), (false, vertices_661), (false, vertices_277), (false, vertices_421), (false, vertices_313), (false, vertices_737), (true, vertices_26), (true, vertices_42), (true, vertices_74), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_770), (true, vertices_772), (true, vertices_104), (true, vertices_200), (true, vertices_392), (true, vertices_648), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_115) then 15 else
  if p.val = (false, vertices_595) then 16 else
  if p.val = (false, vertices_661) then 18 else
  if p.val = (false, vertices_277) then 0 else
  if p.val = (false, vertices_421) then 19 else
  if p.val = (false, vertices_313) then 21 else
  if p.val = (false, vertices_737) then 24 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_776) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_115), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
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
cert_row_4 0 0 1 3 7 8 790 274 1
cert_row_4 1 0 2 5 6 8 714 74 3
cert_row_4 2 1 2 6 7 8 908 388 1
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 3 0 1 2
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 106
cert_cover_2 3 2 0 4 5 42 106 3
cert_coverFacet 4 714
cert_cover_5 4 1 0 2 5 6 74 714 3
cert_coverFacet 5 778
cert_cover_2 5 2 0 7 8 266 778 3
cert_coverFacet 6 908
cert_cover_5 6 2 1 2 6 7 388 908 1
cert_coverFacet 7 488
cert_cover_5 7 3 2 4 5 6 104 488 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0523

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_3093 : Certifies 3093 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0492.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3094 : Certifies 3094 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0493.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3095 : Certifies 3095 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0494.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3096 : Certifies 3096 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0496.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3097 : Certifies 3097 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0497.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3098 : Certifies 3098 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0498.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3099 : Certifies 3099 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0499.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3100 : Certifies 3100 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0500.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3101 : Certifies 3101 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0501.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3102 : Certifies 3102 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0502.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3103 : Certifies 3103 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0504.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3104 : Certifies 3104 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0505.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3105 : Certifies 3105 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0506.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3106 : Certifies 3106 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0507.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3107 : Certifies 3107 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0508.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3108 : Certifies 3108 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0509.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3109 : Certifies 3109 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0510.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3110 : Certifies 3110 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0511.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3111 : Certifies 3111 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0512.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3112 : Certifies 3112 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0513.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3113 : Certifies 3113 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0514.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3114 : Certifies 3114 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0515.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3115 : Certifies 3115 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0516.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3116 : Certifies 3116 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0517.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3117 : Certifies 3117 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0518.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3118 : Certifies 3118 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0519.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3119 : Certifies 3119 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0520.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3120 : Certifies 3120 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0521.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3121 : Certifies 3121 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0522.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3122 : Certifies 3122 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0523.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B102 (j : Fin 30) :
    Certifies (3093 + j.val) := by
  fin_cases j
  · exact projection_3093
  · exact projection_3094
  · exact projection_3095
  · exact projection_3096
  · exact projection_3097
  · exact projection_3098
  · exact projection_3099
  · exact projection_3100
  · exact projection_3101
  · exact projection_3102
  · exact projection_3103
  · exact projection_3104
  · exact projection_3105
  · exact projection_3106
  · exact projection_3107
  · exact projection_3108
  · exact projection_3109
  · exact projection_3110
  · exact projection_3111
  · exact projection_3112
  · exact projection_3113
  · exact projection_3114
  · exact projection_3115
  · exact projection_3116
  · exact projection_3117
  · exact projection_3118
  · exact projection_3119
  · exact projection_3120
  · exact projection_3121
  · exact projection_3122

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
