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
/- Source: ProjectionCertificates/R_m15e10q1_0618.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0618

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 397, 809, 713, 241, 417, 206, 590, 150, 534, 114, 818, 210, 796, 436, 137, 265, 521, 97, 161, 289, 545, 193, 577, 385, 78, 22, 134, 518, 50, 82, 146, 530, 98, 546, 194, 578, 140, 268, 524, 148, 276, 532, 388, 200, 584, 776, 112, 176, 304, 208, 784, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_397, vertices_809, vertices_713, vertices_241, vertices_417, vertices_206, vertices_590, vertices_150, vertices_534, vertices_114, vertices_818, vertices_210, vertices_796, vertices_436] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_97, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_78, vertices_22, vertices_134, vertices_518, vertices_50, vertices_82, vertices_146, vertices_530, vertices_98, vertices_546, vertices_194, vertices_578, vertices_140, vertices_268, vertices_524, vertices_148, vertices_276, vertices_532, vertices_388, vertices_200, vertices_584, vertices_776, vertices_112, vertices_176, vertices_304, vertices_208, vertices_784, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_397), (false, vertices_809), (false, vertices_713), (false, vertices_241), (false, vertices_417), (true, vertices_78), (true, vertices_22), (true, vertices_134), (true, vertices_518), (true, vertices_50), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_194), (true, vertices_524), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_304), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 16 else
  if p.val = (false, vertices_397) then 19 else
  if p.val = (false, vertices_809) then 21 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_241) then 24 else
  if p.val = (false, vertices_417) then 0 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_194) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_276) then 11 else
  if p.val = (true, vertices_532) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_784) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 417 22 134 518 50 82 146 530 194 524 148 276 532 304 784 611 78 397 809 713 241
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 3 4 7 8 818 50 3
cert_row_4 2 1 2 3 7 8 796 268 2
cert_row_4 3 1 3 4 6 7 436 148 2
cert_rows
cert_pivot_2 5 0 2 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 6 78 206 3
cert_coverFacet 1 590
cert_cover_5 1 0 0 1 2 8 78 590 3
cert_coverFacet 2 150
cert_cover_2 2 1 0 3 6 22 150 3
cert_coverFacet 3 534
cert_cover_2 3 1 0 3 8 22 534 3
cert_coverFacet 4 114
cert_cover_2 4 3 0 4 5 50 114 3
cert_coverFacet 5 818
cert_cover_5 5 1 0 3 4 7 50 818 3
cert_coverFacet 6 210
cert_cover_2 6 3 0 5 6 82 210 3
cert_coverFacet 7 796
cert_cover_5 7 2 1 2 3 7 268 796 2
cert_coverFacet 8 436
cert_cover_5 8 3 1 3 4 6 148 436 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0618

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e10q1_0619.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0619

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [227, 541, 217, 681, 113, 817, 398, 678, 806, 370, 450, 348, 652, 788, 456, 25, 137, 521, 49, 81, 529, 97, 161, 545, 193, 550, 134, 262, 98, 162, 290, 194, 322, 386, 28, 140, 268, 524, 276, 532, 644, 772, 88, 200, 328, 392, 648, 112, 304, 336, 784, 672, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_227, vertices_541, vertices_217, vertices_681, vertices_113, vertices_817, vertices_398, vertices_678, vertices_806, vertices_370, vertices_450, vertices_348, vertices_652, vertices_788, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_521, vertices_49, vertices_81, vertices_529, vertices_97, vertices_161, vertices_545, vertices_193, vertices_550, vertices_134, vertices_262, vertices_98, vertices_162, vertices_290, vertices_194, vertices_322, vertices_386, vertices_28, vertices_140, vertices_268, vertices_524, vertices_276, vertices_532, vertices_644, vertices_772, vertices_88, vertices_200, vertices_328, vertices_392, vertices_648, vertices_112, vertices_304, vertices_336, vertices_784, vertices_672, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_227), (false, vertices_541), (false, vertices_217), (false, vertices_681), (false, vertices_113), (false, vertices_817), (true, vertices_550), (true, vertices_134), (true, vertices_262), (true, vertices_290), (true, vertices_322), (true, vertices_386), (true, vertices_140), (true, vertices_268), (true, vertices_276), (true, vertices_644), (true, vertices_772), (true, vertices_328), (true, vertices_392), (true, vertices_336), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_227) then 16 else
  if p.val = (false, vertices_541) then 19 else
  if p.val = (false, vertices_217) then 21 else
  if p.val = (false, vertices_681) then 22 else
  if p.val = (false, vertices_113) then 0 else
  if p.val = (false, vertices_817) then 24 else
  if p.val = (true, vertices_550) then 17 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 113 134 262 290 322 386 140 268 276 644 772 328 392 336 448 227 550 541 217 681 817
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 4 8 550
cert_row_4 1 0 1 2 6 7 398 134 2
cert_row_4 2 0 3 4 5 7 370 98 1
cert_row_4 3 1 2 3 5 7 348 28 3
cert_rows
cert_pivot_2 8 6 0 1
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 1 0 1 2 6 134 398 2
cert_coverFacet 1 678
cert_cover_5 1 0 0 1 4 6 550 678 3
cert_coverFacet 2 806
cert_cover_5 2 0 0 1 4 7 550 806 3
cert_coverFacet 3 370
cert_cover_5 3 2 0 3 4 5 98 370 1
cert_coverFacet 4 450
cert_cover_2 4 5 0 6 7 194 450 3
cert_coverFacet 5 348
cert_cover_5 5 3 1 2 3 5 28 348 3
cert_coverFacet 6 652
cert_cover_2 6 2 1 6 8 140 652 3
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coverFacet 8 456
cert_cover_2 8 5 2 6 7 200 456 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0619

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e10q1_0620.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0620

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 597, 233, 817, 465, 609, 206, 270, 214, 278, 170, 810, 402, 796, 620, 81, 273, 529, 97, 161, 289, 545, 193, 577, 385, 14, 22, 198, 262, 42, 138, 266, 146, 274, 162, 290, 386, 76, 268, 524, 84, 276, 532, 580, 104, 168, 552, 200, 776, 208, 400, 784, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_597, vertices_233, vertices_817, vertices_465, vertices_609, vertices_206, vertices_270, vertices_214, vertices_278, vertices_170, vertices_810, vertices_402, vertices_796, vertices_620] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_273, vertices_529, vertices_97, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_14, vertices_22, vertices_198, vertices_262, vertices_42, vertices_138, vertices_266, vertices_146, vertices_274, vertices_162, vertices_290, vertices_386, vertices_76, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_580, vertices_104, vertices_168, vertices_552, vertices_200, vertices_776, vertices_208, vertices_400, vertices_784, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_597), (false, vertices_233), (false, vertices_817), (false, vertices_465), (false, vertices_609), (true, vertices_14), (true, vertices_22), (true, vertices_198), (true, vertices_262), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_146), (true, vertices_274), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_276), (true, vertices_552), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 16 else
  if p.val = (false, vertices_597) then 19 else
  if p.val = (false, vertices_233) then 21 else
  if p.val = (false, vertices_817) then 23 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (false, vertices_609) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_198) then 17 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_146) then 7 else
  if p.val = (true, vertices_274) then 8 else
  if p.val = (true, vertices_76) then 9 else
  if p.val = (true, vertices_268) then 10 else
  if p.val = (true, vertices_524) then 11 else
  if p.val = (true, vertices_276) then 12 else
  if p.val = (true, vertices_552) then 13 else
  if p.val = (true, vertices_776) then 14 else
  0
cert_priority
cert_nodeAtPriority_40 609 14 22 262 42 138 266 146 274 76 268 524 276 552 776 419 198 597 233 817 465
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 5 6 198
cert_row_4 1 0 2 4 7 8 810 42 3
cert_row_4 2 1 2 3 7 8 796 268 2
cert_row_4 3 1 2 4 5 8 620 76 2
cert_rows
cert_pivot_2 6 0 3 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 214
cert_cover_5 2 0 0 1 3 5 22 214 3
cert_coverFacet 3 278
cert_cover_2 3 1 0 3 7 22 278 3
cert_coverFacet 4 170
cert_cover_2 4 2 0 4 6 42 170 3
cert_coverFacet 5 810
cert_cover_5 5 1 0 2 4 7 42 810 3
cert_coverFacet 6 402
cert_cover_2 6 3 0 6 7 146 402 3
cert_coverFacet 7 796
cert_cover_5 7 2 1 2 3 7 268 796 2
cert_coverFacet 8 620
cert_cover_5 8 3 1 2 4 5 76 620 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0620

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e10q1_0621.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0621

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 421, 837, 361, 625, 673, 398, 342, 598, 154, 282, 690, 248, 344, 424, 133, 261, 517, 97, 161, 289, 545, 321, 577, 641, 86, 134, 262, 518, 26, 138, 266, 146, 274, 530, 642, 324, 580, 388, 88, 152, 280, 104, 168, 296, 328, 392, 112, 176, 560, 336, 592, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_421, vertices_837, vertices_361, vertices_625, vertices_673, vertices_398, vertices_342, vertices_598, vertices_154, vertices_282, vertices_690, vertices_248, vertices_344, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_97, vertices_161, vertices_289, vertices_545, vertices_321, vertices_577, vertices_641, vertices_86, vertices_134, vertices_262, vertices_518, vertices_26, vertices_138, vertices_266, vertices_146, vertices_274, vertices_530, vertices_642, vertices_324, vertices_580, vertices_388, vertices_88, vertices_152, vertices_280, vertices_104, vertices_168, vertices_296, vertices_328, vertices_392, vertices_112, vertices_176, vertices_560, vertices_336, vertices_592, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_421), (false, vertices_837), (false, vertices_361), (false, vertices_625), (false, vertices_673), (true, vertices_86), (true, vertices_262), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_168), (true, vertices_392), (true, vertices_176), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 16 else
  if p.val = (false, vertices_421) then 19 else
  if p.val = (false, vertices_837) then 20 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (false, vertices_673) then 0 else
  if p.val = (true, vertices_86) then 17 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_336) then 14 else
  0
cert_priority
cert_nodeAtPriority_22 673 262 26 138 266 146 274 530 88 152 280 168 392 176 336 647 86 421 837 361 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 134 2
cert_row_2 1 0 1 3 5 86
cert_row_4 2 0 3 4 6 8 690 146 2
cert_row_4 3 2 3 4 5 6 248 88 2
cert_rows
cert_pivot_2 7 1 0 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 134 398 2
cert_coverFacet 1 342
cert_cover_5 1 1 0 1 3 7 86 342 3
cert_coverFacet 2 598
cert_cover_5 2 1 0 1 3 8 86 598 3
cert_coverFacet 3 154
cert_cover_2 3 2 0 3 6 26 154 3
cert_coverFacet 4 282
cert_cover_2 4 2 0 3 7 26 282 3
cert_coverFacet 5 690
cert_cover_5 5 2 0 3 4 6 146 690 2
cert_coverFacet 6 248
cert_cover_5 6 3 2 3 4 5 88 248 2
cert_coverFacet 7 344
cert_cover_2 7 3 2 5 7 88 344 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0621

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e10q1_0622.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0622

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [355, 195, 899, 709, 809, 625, 158, 86, 198, 410, 338, 572, 908, 596, 376, 67, 131, 259, 97, 289, 545, 193, 577, 641, 769, 22, 70, 134, 154, 82, 274, 194, 322, 386, 28, 140, 524, 84, 532, 196, 580, 644, 56, 280, 296, 552, 392, 776, 112, 560, 336, 592, 352, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_355, vertices_195, vertices_899, vertices_709, vertices_809, vertices_625, vertices_158, vertices_86, vertices_198, vertices_410, vertices_338, vertices_572, vertices_908, vertices_596, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_97, vertices_289, vertices_545, vertices_193, vertices_577, vertices_641, vertices_769, vertices_22, vertices_70, vertices_134, vertices_154, vertices_82, vertices_274, vertices_194, vertices_322, vertices_386, vertices_28, vertices_140, vertices_524, vertices_84, vertices_532, vertices_196, vertices_580, vertices_644, vertices_56, vertices_280, vertices_296, vertices_552, vertices_392, vertices_776, vertices_112, vertices_560, vertices_336, vertices_592, vertices_352, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_355), (false, vertices_195), (false, vertices_899), (false, vertices_709), (false, vertices_809), (false, vertices_625), (true, vertices_22), (true, vertices_70), (true, vertices_134), (true, vertices_154), (true, vertices_82), (true, vertices_274), (true, vertices_28), (true, vertices_140), (true, vertices_524), (true, vertices_84), (true, vertices_532), (true, vertices_56), (true, vertices_280), (true, vertices_392), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_355) then 16 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_899) then 17 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_809) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_154) then 18 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_336) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_154), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
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
cert_row_2 0 0 2 3 6 154
cert_row_4 1 1 2 6 7 8 908 140 3
cert_row_4 2 1 2 3 4 8 572 28 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 0 0 1 2 3 22 158 2
cert_coverFacet 1 86
cert_cover_2 1 1 0 3 5 22 86 3
cert_coverFacet 2 198
cert_cover_2 2 1 0 5 6 70 198 3
cert_coverFacet 3 410
cert_cover_5 3 0 0 2 3 7 154 410 3
cert_coverFacet 4 338
cert_cover_2 4 3 0 5 7 82 338 3
cert_coverFacet 5 572
cert_cover_5 5 2 1 2 3 4 28 572 3
cert_coverFacet 6 908
cert_cover_5 6 1 1 2 6 7 140 908 3
cert_coverFacet 7 596
cert_cover_2 7 3 1 5 8 84 596 3
cert_coverFacet 8 376
cert_cover_5 8 3 2 3 4 5 56 376 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0622

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e10q1_0623.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0623

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 181, 677, 217, 841, 625, 782, 310, 150, 646, 394, 466, 868, 456, 368, 165, 73, 137, 521, 49, 81, 145, 545, 577, 641, 22, 134, 262, 518, 138, 266, 522, 146, 274, 386, 642, 52, 148, 292, 548, 644, 772, 200, 328, 392, 776, 112, 304, 208, 336, 352, 608, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_181, vertices_677, vertices_217, vertices_841, vertices_625, vertices_782, vertices_310, vertices_150, vertices_646, vertices_394, vertices_466, vertices_868, vertices_456, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_165, vertices_73, vertices_137, vertices_521, vertices_49, vertices_81, vertices_145, vertices_545, vertices_577, vertices_641, vertices_22, vertices_134, vertices_262, vertices_518, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_386, vertices_642, vertices_52, vertices_148, vertices_292, vertices_548, vertices_644, vertices_772, vertices_200, vertices_328, vertices_392, vertices_776, vertices_112, vertices_304, vertices_208, vertices_336, vertices_352, vertices_608, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_181), (false, vertices_677), (false, vertices_217), (false, vertices_841), (false, vertices_625), (true, vertices_22), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_266), (true, vertices_146), (true, vertices_274), (true, vertices_386), (true, vertices_292), (true, vertices_772), (true, vertices_392), (true, vertices_304), (true, vertices_336), (true, vertices_352), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 16 else
  if p.val = (false, vertices_181) then 18 else
  if p.val = (false, vertices_677) then 19 else
  if p.val = (false, vertices_217) then 21 else
  if p.val = (false, vertices_841) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_352) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
cert_nodeAtPriority_52 22 1 134 2 262 518 266 146 274 386 292 772 392 304 336 352 448 651 181 677 217 841 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 262 2
cert_row_4 1 0 3 5 6 7 466 146 2
cert_row_4 2 0 1 3 4 7 310 22 3
cert_row_4 3 1 4 5 7 8 868 292 2
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 262 782 2
cert_coverFacet 1 310
cert_cover_5 1 2 0 1 3 4 22 310 3
cert_coverFacet 2 150
cert_cover_2 2 1 0 3 6 22 150 3
cert_coverFacet 3 646
cert_cover_2 3 1 0 6 8 134 646 3
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 466
cert_cover_5 5 1 0 3 5 6 146 466 2
cert_coverFacet 6 868
cert_cover_5 6 3 1 4 5 7 292 868 2
cert_coverFacet 7 456
cert_cover_2 7 5 2 6 7 200 456 3
cert_coverFacet 8 368
cert_cover_2 8 4 3 5 7 112 368 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0623

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e10q1_0624.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0624

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [55, 563, 405, 805, 665, 961, 30, 110, 538, 714, 866, 284, 332, 356, 472, 51, 21, 37, 261, 145, 529, 545, 385, 641, 769, 14, 22, 38, 26, 74, 522, 530, 98, 546, 578, 28, 76, 268, 276, 100, 292, 324, 152, 280, 536, 200, 328, 648, 400, 352, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_55, vertices_563, vertices_405, vertices_805, vertices_665, vertices_961, vertices_30, vertices_110, vertices_538, vertices_714, vertices_866, vertices_284, vertices_332, vertices_356, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_51, vertices_21, vertices_37, vertices_261, vertices_145, vertices_529, vertices_545, vertices_385, vertices_641, vertices_769, vertices_14, vertices_22, vertices_38, vertices_26, vertices_74, vertices_522, vertices_530, vertices_98, vertices_546, vertices_578, vertices_28, vertices_76, vertices_268, vertices_276, vertices_100, vertices_292, vertices_324, vertices_152, vertices_280, vertices_536, vertices_200, vertices_328, vertices_648, vertices_400, vertices_352, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_55), (false, vertices_563), (false, vertices_405), (false, vertices_805), (false, vertices_665), (false, vertices_961), (true, vertices_14), (true, vertices_26), (true, vertices_74), (true, vertices_522), (true, vertices_98), (true, vertices_578), (true, vertices_28), (true, vertices_76), (true, vertices_268), (true, vertices_100), (true, vertices_324), (true, vertices_280), (true, vertices_200), (true, vertices_328), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 24 25 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_55) then 16 else
  if p.val = (false, vertices_563) then 17 else
  if p.val = (false, vertices_405) then 19 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (false, vertices_665) then 22 else
  if p.val = (false, vertices_961) then 26 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_328) then 13 else
  if p.val = (true, vertices_352) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_55), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 5 110 14 3
cert_row_4 1 0 4 5 7 8 866 98 3
cert_row_4 2 0 2 5 6 8 714 74 3
cert_row_4 3 2 3 5 6 7 472 152 2
cert_rows
cert_pivot_2 1 4 0 2
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 110
cert_cover_5 1 0 0 1 2 4 14 110 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 714
cert_cover_5 3 2 0 2 5 6 74 714 3
cert_coverFacet 4 866
cert_cover_5 4 1 0 4 5 7 98 866 3
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 332
cert_cover_2 6 2 1 5 7 76 332 3
cert_coverFacet 7 356
cert_cover_2 7 4 1 5 7 100 356 3
cert_coverFacet 8 472
cert_cover_5 8 3 2 3 5 6 152 472 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0624

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e10q1_0625.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0625

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 421, 233, 625, 465, 801, 206, 526, 214, 278, 806, 602, 684, 404, 616, 81, 273, 529, 97, 161, 289, 545, 193, 385, 769, 14, 22, 198, 262, 518, 74, 522, 82, 274, 530, 770, 140, 524, 148, 276, 164, 292, 548, 388, 104, 168, 552, 200, 584, 208, 592, 400, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_421, vertices_233, vertices_625, vertices_465, vertices_801, vertices_206, vertices_526, vertices_214, vertices_278, vertices_806, vertices_602, vertices_684, vertices_404, vertices_616] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_273, vertices_529, vertices_97, vertices_161, vertices_289, vertices_545, vertices_193, vertices_385, vertices_769, vertices_14, vertices_22, vertices_198, vertices_262, vertices_518, vertices_74, vertices_522, vertices_82, vertices_274, vertices_530, vertices_770, vertices_140, vertices_524, vertices_148, vertices_276, vertices_164, vertices_292, vertices_548, vertices_388, vertices_104, vertices_168, vertices_552, vertices_200, vertices_584, vertices_208, vertices_592, vertices_400, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_421), (false, vertices_233), (false, vertices_625), (false, vertices_465), (false, vertices_801), (true, vertices_14), (true, vertices_22), (true, vertices_198), (true, vertices_262), (true, vertices_518), (true, vertices_74), (true, vertices_522), (true, vertices_82), (true, vertices_140), (true, vertices_524), (true, vertices_148), (true, vertices_276), (true, vertices_548), (true, vertices_552), (true, vertices_584)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 16 else
  if p.val = (false, vertices_421) then 19 else
  if p.val = (false, vertices_233) then 21 else
  if p.val = (false, vertices_625) then 23 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (false, vertices_801) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_198) then 17 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_74) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_82) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_276) then 11 else
  if p.val = (true, vertices_548) then 12 else
  if p.val = (true, vertices_552) then 13 else
  if p.val = (true, vertices_584) then 14 else
  0
cert_priority
cert_nodeAtPriority_40 801 14 22 262 518 74 522 82 140 524 148 276 548 552 584 787 198 421 233 625 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 7 8 806 262 2
cert_row_4 1 0 2 3 5 8 602 74 2
cert_row_2 2 0 1 5 6 198
cert_row_4 3 1 2 4 6 8 684 140 2
cert_rows
cert_pivot_2 7 3 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 2 0 1 2 5 14 206 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 214
cert_cover_5 2 2 0 1 3 5 22 214 3
cert_coverFacet 3 278
cert_cover_2 3 1 0 3 7 22 278 3
cert_coverFacet 4 806
cert_cover_5 4 0 0 1 4 7 262 806 2
cert_coverFacet 5 602
cert_cover_5 5 1 0 2 3 5 74 602 2
cert_coverFacet 6 684
cert_cover_5 6 3 1 2 4 6 140 684 2
cert_coverFacet 7 404
cert_cover_2 7 3 1 6 7 148 404 3
cert_coverFacet 8 616
cert_cover_2 8 4 2 5 8 104 616 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0625

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e10q1_0626.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0626

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 563, 227, 387, 457, 369, 785, 398, 166, 550, 796, 716, 740, 632, 344, 35, 131, 259, 515, 49, 273, 529, 97, 193, 321, 385, 769, 38, 134, 262, 518, 162, 546, 386, 140, 268, 524, 164, 548, 708, 772, 88, 280, 536, 200, 328, 584, 392, 112, 560, 336, 784, 224, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_563, vertices_227, vertices_387, vertices_457, vertices_369, vertices_785, vertices_398, vertices_166, vertices_550, vertices_796, vertices_716, vertices_740, vertices_632, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_49, vertices_273, vertices_529, vertices_97, vertices_193, vertices_321, vertices_385, vertices_769, vertices_38, vertices_134, vertices_262, vertices_518, vertices_162, vertices_546, vertices_386, vertices_140, vertices_268, vertices_524, vertices_164, vertices_548, vertices_708, vertices_772, vertices_88, vertices_280, vertices_536, vertices_200, vertices_328, vertices_584, vertices_392, vertices_112, vertices_560, vertices_336, vertices_784, vertices_224, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_563), (false, vertices_227), (false, vertices_387), (false, vertices_457), (false, vertices_369), (false, vertices_785), (true, vertices_38), (true, vertices_134), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_164), (true, vertices_548), (true, vertices_708), (true, vertices_88), (true, vertices_280), (true, vertices_536), (true, vertices_584), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 15 else
  if p.val = (false, vertices_563) then 16 else
  if p.val = (false, vertices_227) then 17 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_369) then 23 else
  if p.val = (false, vertices_785) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_708) then 19 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_608) then 13 else
  0
cert_priority
cert_nodeAtPriority_47 387 785 38 134 140 268 524 164 548 88 280 536 584 608 775 563 227 708 457 369
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 134 2
cert_row_2 1 1 5 6 8 708
cert_row_4 2 1 2 3 7 8 796 268 2
cert_row_4 3 2 3 4 5 8 632 88 2
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 134 398 2
cert_coverFacet 1 166
cert_cover_2 1 1 0 4 6 38 166 3
cert_coverFacet 2 550
cert_cover_2 2 1 0 4 8 38 550 3
cert_coverFacet 3 796
cert_cover_5 3 2 1 2 3 7 268 796 2
cert_coverFacet 4 716
cert_cover_5 4 1 1 2 5 6 140 716 2
cert_coverFacet 5 740
cert_cover_5 5 1 1 4 5 6 164 740 2
cert_coverFacet 6 632
cert_cover_5 6 3 2 3 4 5 88 632 2
cert_coverFacet 7 344
cert_cover_2 7 3 2 5 7 88 344 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0626

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m15e10q1_0627.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0627

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 653, 901, 569, 425, 369, 206, 598, 390, 774, 338, 482, 620, 232, 624, 645, 41, 137, 521, 49, 273, 529, 289, 385, 769, 70, 134, 262, 518, 82, 274, 530, 194, 322, 386, 770, 76, 140, 524, 580, 388, 772, 104, 168, 552, 200, 112, 560, 336, 592, 224, 352, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_653, vertices_901, vertices_569, vertices_425, vertices_369, vertices_206, vertices_598, vertices_390, vertices_774, vertices_338, vertices_482, vertices_620, vertices_232, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_645, vertices_41, vertices_137, vertices_521, vertices_49, vertices_273, vertices_529, vertices_289, vertices_385, vertices_769, vertices_70, vertices_134, vertices_262, vertices_518, vertices_82, vertices_274, vertices_530, vertices_194, vertices_322, vertices_386, vertices_770, vertices_76, vertices_140, vertices_524, vertices_580, vertices_388, vertices_772, vertices_104, vertices_168, vertices_552, vertices_200, vertices_112, vertices_560, vertices_336, vertices_592, vertices_224, vertices_352, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_653), (false, vertices_901), (false, vertices_569), (false, vertices_425), (false, vertices_369), (true, vertices_70), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_82), (true, vertices_194), (true, vertices_322), (true, vertices_386), (true, vertices_76), (true, vertices_580), (true, vertices_104), (true, vertices_200), (true, vertices_592), (true, vertices_224), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 16 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_901) then 19 else
  if p.val = (false, vertices_569) then 21 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_608) then 14 else
  0
cert_priority
cert_nodeAtPriority_52 70 1 134 2 262 518 82 194 322 386 76 580 104 200 592 224 608 787 653 901 569 425 369
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 8 598 70 2
cert_row_4 1 0 4 5 6 7 482 194 1
cert_row_4 2 0 1 2 5 6 206 70 2
cert_row_4 3 1 2 4 5 8 620 76 2
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 2 0 1 2 5 70 206 2
cert_coverFacet 1 598
cert_cover_5 1 0 0 1 3 5 70 598 2
cert_coverFacet 2 390
cert_cover_2 2 1 0 6 7 134 390 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 338
cert_cover_2 4 3 0 5 7 82 338 3
cert_coverFacet 5 482
cert_cover_5 5 1 0 4 5 6 194 482 1
cert_coverFacet 6 620
cert_cover_5 6 3 1 2 4 5 76 620 2
cert_coverFacet 7 232
cert_cover_2 7 4 2 5 6 104 232 3
cert_coverFacet 8 624
cert_cover_2 8 4 3 5 8 112 624 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0627

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m15e10q1_0628.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0628

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 597, 805, 569, 433, 337, 590, 654, 390, 202, 466, 900, 248, 600, 936, 69, 261, 517, 49, 81, 273, 529, 289, 545, 321, 526, 70, 134, 262, 74, 138, 194, 322, 386, 580, 388, 644, 772, 56, 88, 536, 168, 552, 200, 584, 648, 176, 208, 336, 592, 400, 416, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_597, vertices_805, vertices_569, vertices_433, vertices_337, vertices_590, vertices_654, vertices_390, vertices_202, vertices_466, vertices_900, vertices_248, vertices_600, vertices_936] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_49, vertices_81, vertices_273, vertices_529, vertices_289, vertices_545, vertices_321, vertices_526, vertices_70, vertices_134, vertices_262, vertices_74, vertices_138, vertices_194, vertices_322, vertices_386, vertices_580, vertices_388, vertices_644, vertices_772, vertices_56, vertices_88, vertices_536, vertices_168, vertices_552, vertices_200, vertices_584, vertices_648, vertices_176, vertices_208, vertices_336, vertices_592, vertices_400, vertices_416, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_597), (false, vertices_805), (false, vertices_569), (false, vertices_433), (false, vertices_337), (true, vertices_526), (true, vertices_134), (true, vertices_74), (true, vertices_138), (true, vertices_194), (true, vertices_386), (true, vertices_388), (true, vertices_644), (true, vertices_88), (true, vertices_168), (true, vertices_200), (true, vertices_584), (true, vertices_648), (true, vertices_208), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 16 else
  if p.val = (false, vertices_597) then 19 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (false, vertices_569) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (true, vertices_526) then 17 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_896) then 14 else
  0
cert_priority
cert_nodeAtPriority_22 337 134 74 138 194 386 388 644 88 168 200 584 648 208 896 327 526 597 805 569 433
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 8 526
cert_row_4 1 0 3 5 6 7 466 194 1
cert_row_4 2 2 3 4 5 6 248 56 3
cert_row_4 3 2 4 6 7 8 936 168 3
cert_rows
cert_pivot_2 1 0 3 2
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 526 590 3
cert_coverFacet 1 654
cert_cover_5 1 0 0 1 2 6 526 654 3
cert_coverFacet 2 390
cert_cover_2 2 1 0 6 7 134 390 3
cert_coverFacet 3 202
cert_cover_2 3 2 0 5 6 74 202 3
cert_coverFacet 4 466
cert_cover_5 4 1 0 3 5 6 194 466 1
cert_coverFacet 5 900
cert_cover_2 5 6 1 7 8 388 900 3
cert_coverFacet 6 248
cert_cover_5 6 2 2 3 4 5 56 248 3
cert_coverFacet 7 600
cert_cover_2 7 3 2 5 8 88 600 3
cert_coverFacet 8 936
cert_cover_5 8 3 2 4 6 7 168 936 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0628

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m15e10q1_0629.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0629

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 405, 837, 345, 625, 657, 302, 142, 806, 170, 690, 396, 248, 408, 872, 133, 261, 517, 81, 145, 273, 529, 321, 577, 641, 14, 294, 134, 518, 42, 138, 162, 546, 642, 140, 268, 388, 772, 88, 152, 280, 104, 168, 296, 328, 392, 112, 176, 560, 400, 656, 608, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_405, vertices_837, vertices_345, vertices_625, vertices_657, vertices_302, vertices_142, vertices_806, vertices_170, vertices_690, vertices_396, vertices_248, vertices_408, vertices_872] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_81, vertices_145, vertices_273, vertices_529, vertices_321, vertices_577, vertices_641, vertices_14, vertices_294, vertices_134, vertices_518, vertices_42, vertices_138, vertices_162, vertices_546, vertices_642, vertices_140, vertices_268, vertices_388, vertices_772, vertices_88, vertices_152, vertices_280, vertices_104, vertices_168, vertices_296, vertices_328, vertices_392, vertices_112, vertices_176, vertices_560, vertices_400, vertices_656, vertices_608, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_405), (false, vertices_837), (false, vertices_345), (false, vertices_625), (false, vertices_657), (true, vertices_14), (true, vertices_294), (true, vertices_42), (true, vertices_138), (true, vertices_162), (true, vertices_546), (true, vertices_140), (true, vertices_268), (true, vertices_152), (true, vertices_104), (true, vertices_168), (true, vertices_296), (true, vertices_392), (true, vertices_176), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 16 else
  if p.val = (false, vertices_405) then 19 else
  if p.val = (false, vertices_837) then 20 else
  if p.val = (false, vertices_345) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (false, vertices_657) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_294) then 17 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_800) then 14 else
  0
cert_priority
cert_nodeAtPriority_22 657 14 42 138 162 546 140 268 152 104 168 296 392 176 800 647 294 405 837 345 625
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 4 7 294
cert_row_4 1 0 3 4 6 8 690 162 1
cert_row_4 2 2 3 4 5 6 248 88 2
cert_row_4 3 2 4 5 7 8 872 104 3
cert_rows
cert_pivot_2 1 0 3 2
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 0 0 1 2 4 14 302 3
cert_coverFacet 1 142
cert_cover_2 1 1 0 2 6 14 142 3
cert_coverFacet 2 806
cert_cover_5 2 0 0 1 4 8 294 806 3
cert_coverFacet 3 170
cert_cover_2 3 2 0 4 6 42 170 3
cert_coverFacet 4 690
cert_cover_5 4 1 0 3 4 6 162 690 1
cert_coverFacet 5 396
cert_cover_2 5 2 1 6 7 140 396 3
cert_coverFacet 6 248
cert_cover_5 6 2 2 3 4 5 88 248 2
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 872
cert_cover_5 8 3 2 4 5 7 104 872 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0629

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m15e10q1_0630.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0630

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [43, 779, 115, 595, 901, 425, 737, 542, 58, 284, 780, 724, 340, 484, 376, 11, 83, 35, 515, 41, 265, 97, 161, 577, 385, 641, 769, 26, 42, 522, 50, 530, 28, 268, 524, 84, 276, 532, 196, 324, 388, 644, 772, 56, 280, 296, 776, 112, 336, 592, 224, 352, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_43, vertices_779, vertices_115, vertices_595, vertices_901, vertices_425, vertices_737, vertices_542, vertices_58, vertices_284, vertices_780, vertices_724, vertices_340, vertices_484, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_83, vertices_35, vertices_515, vertices_41, vertices_265, vertices_97, vertices_161, vertices_577, vertices_385, vertices_641, vertices_769, vertices_26, vertices_42, vertices_522, vertices_50, vertices_530, vertices_28, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_196, vertices_324, vertices_388, vertices_644, vertices_772, vertices_56, vertices_280, vertices_296, vertices_776, vertices_112, vertices_336, vertices_592, vertices_224, vertices_352, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_43), (false, vertices_779), (false, vertices_115), (false, vertices_595), (false, vertices_901), (false, vertices_425), (false, vertices_737), (true, vertices_26), (true, vertices_28), (true, vertices_268), (true, vertices_524), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_196), (true, vertices_324), (true, vertices_56), (true, vertices_280), (true, vertices_336), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_43) then 0 else
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_115) then 16 else
  if p.val = (false, vertices_595) then 17 else
  if p.val = (false, vertices_901) then 19 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_737) then 24 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_352) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_43), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_115), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
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
cert_row_4 0 0 1 2 3 8 542 26 1
cert_row_4 1 1 3 5 6 8 724 84 3
cert_row_4 2 1 4 5 6 7 484 196 1
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 26 542 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 284
cert_cover_2 2 2 1 3 7 28 284 3
cert_coverFacet 3 780
cert_cover_2 3 2 1 7 8 268 780 3
cert_coverFacet 4 724
cert_cover_5 4 1 1 3 5 6 84 724 3
cert_coverFacet 5 340
cert_cover_2 5 3 1 5 7 84 340 3
cert_coverFacet 6 484
cert_cover_5 6 2 1 4 5 6 196 484 1
cert_coverFacet 7 376
cert_cover_5 7 3 2 3 4 5 56 376 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0630

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m15e10q1_0631.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0631

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [295, 403, 611, 643, 229, 389, 713, 666, 306, 562, 412, 204, 844, 868, 824, 35, 131, 259, 515, 37, 133, 261, 97, 193, 577, 385, 641, 50, 146, 274, 530, 290, 546, 642, 76, 140, 268, 100, 292, 196, 836, 388, 152, 280, 536, 200, 584, 648, 776, 304, 560, 400, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_403, vertices_611, vertices_643, vertices_229, vertices_389, vertices_713, vertices_666, vertices_306, vertices_562, vertices_412, vertices_204, vertices_844, vertices_868, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_37, vertices_133, vertices_261, vertices_97, vertices_193, vertices_577, vertices_385, vertices_641, vertices_50, vertices_146, vertices_274, vertices_530, vertices_290, vertices_546, vertices_642, vertices_76, vertices_140, vertices_268, vertices_100, vertices_292, vertices_196, vertices_836, vertices_388, vertices_152, vertices_280, vertices_536, vertices_200, vertices_584, vertices_648, vertices_776, vertices_304, vertices_560, vertices_400, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_403), (false, vertices_611), (false, vertices_643), (false, vertices_229), (false, vertices_389), (false, vertices_713), (true, vertices_50), (true, vertices_530), (true, vertices_76), (true, vertices_140), (true, vertices_268), (true, vertices_836), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_776), (true, vertices_304), (true, vertices_560), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 15 else
  if p.val = (false, vertices_403) then 16 else
  if p.val = (false, vertices_611) then 17 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_229) then 19 else
  if p.val = (false, vertices_389) then 1 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_836) then 20 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_800) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_295), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_836), by decide +kernel⟩
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
cert_row_2 0 1 5 7 8 836
cert_row_4 1 0 2 3 6 8 666 146 1
cert_row_4 2 1 2 3 6 7 412 140 2
cert_row_4 3 2 3 4 7 8 824 280 2
cert_rows
cert_pivot_2 5 0 1 2
cert_heightProof 4
cert_coverFacet 0 666
cert_cover_5 0 1 0 2 3 6 146 666 1
cert_coverFacet 1 306
cert_cover_2 1 3 0 4 7 50 306 3
cert_coverFacet 2 562
cert_cover_2 2 3 0 4 8 50 562 3
cert_coverFacet 3 412
cert_cover_5 3 2 1 2 3 6 140 412 2
cert_coverFacet 4 204
cert_cover_2 4 2 1 5 6 76 204 3
cert_coverFacet 5 844
cert_cover_5 5 0 1 2 5 7 76 844 3
cert_coverFacet 6 868
cert_cover_5 6 0 1 4 5 7 100 868 3
cert_coverFacet 7 824
cert_cover_5 7 3 2 3 4 7 280 824 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0631

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m15e10q1_0632.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0632

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [107, 555, 541, 345, 913, 865, 206, 526, 662, 226, 930, 284, 332, 404, 484, 43, 25, 73, 521, 273, 529, 97, 545, 321, 769, 14, 134, 518, 74, 522, 98, 162, 546, 194, 642, 28, 76, 268, 524, 148, 276, 532, 196, 324, 388, 280, 328, 400, 656, 224, 352, 416, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_107, vertices_555, vertices_541, vertices_345, vertices_913, vertices_865, vertices_206, vertices_526, vertices_662, vertices_226, vertices_930, vertices_284, vertices_332, vertices_404, vertices_484] (by decide +kernel)
  polygons := literalFinset [vertices_43, vertices_25, vertices_73, vertices_521, vertices_273, vertices_529, vertices_97, vertices_545, vertices_321, vertices_769, vertices_14, vertices_134, vertices_518, vertices_74, vertices_522, vertices_98, vertices_162, vertices_546, vertices_194, vertices_642, vertices_28, vertices_76, vertices_268, vertices_524, vertices_148, vertices_276, vertices_532, vertices_196, vertices_324, vertices_388, vertices_280, vertices_328, vertices_400, vertices_656, vertices_224, vertices_352, vertices_416, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_107), (false, vertices_555), (false, vertices_541), (false, vertices_345), (false, vertices_913), (false, vertices_865), (true, vertices_14), (true, vertices_134), (true, vertices_518), (true, vertices_162), (true, vertices_194), (true, vertices_642), (true, vertices_76), (true, vertices_268), (true, vertices_148), (true, vertices_276), (true, vertices_196), (true, vertices_324), (true, vertices_388), (true, vertices_224), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_107) then 16 else
  if p.val = (false, vertices_555) then 17 else
  if p.val = (false, vertices_541) then 19 else
  if p.val = (false, vertices_345) then 21 else
  if p.val = (false, vertices_913) then 23 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_324) then 11 else
  if p.val = (true, vertices_388) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_107), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 6 206 14 3
cert_row_4 1 0 1 3 6 8 662 134 2
cert_row_4 2 0 4 6 7 8 930 162 3
cert_row_4 3 1 4 5 6 7 484 196 1
cert_rows
cert_pivot_2 2 3 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 662
cert_cover_5 2 1 0 1 3 6 134 662 2
cert_coverFacet 3 226
cert_cover_2 3 4 0 5 6 98 226 3
cert_coverFacet 4 930
cert_cover_5 4 2 0 4 6 7 162 930 3
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 332
cert_cover_2 6 2 1 5 7 76 332 3
cert_coverFacet 7 404
cert_cover_2 7 3 1 6 7 148 404 3
cert_coverFacet 8 484
cert_cover_5 8 3 1 4 5 6 196 484 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0632

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m15e10q1_0633.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0633

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 523, 675, 653, 457, 369, 225, 286, 542, 626, 306, 396, 852, 740, 452, 11, 35, 515, 137, 265, 521, 97, 161, 289, 193, 321, 641, 30, 266, 522, 50, 274, 530, 290, 546, 140, 268, 524, 276, 532, 196, 324, 580, 388, 644, 392, 112, 304, 336, 592, 224, 608, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_523, vertices_675, vertices_653, vertices_457, vertices_369, vertices_225, vertices_286, vertices_542, vertices_626, vertices_306, vertices_396, vertices_852, vertices_740, vertices_452] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_515, vertices_137, vertices_265, vertices_521, vertices_97, vertices_161, vertices_289, vertices_193, vertices_321, vertices_641, vertices_30, vertices_266, vertices_522, vertices_50, vertices_274, vertices_530, vertices_290, vertices_546, vertices_140, vertices_268, vertices_524, vertices_276, vertices_532, vertices_196, vertices_324, vertices_580, vertices_388, vertices_644, vertices_392, vertices_112, vertices_304, vertices_336, vertices_592, vertices_224, vertices_608, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_523), (false, vertices_675), (false, vertices_653), (false, vertices_457), (false, vertices_369), (false, vertices_225), (true, vertices_30), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_268), (true, vertices_276), (true, vertices_532), (true, vertices_196), (true, vertices_324), (true, vertices_580), (true, vertices_388), (true, vertices_592), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 15 else
  if p.val = (false, vertices_523) then 0 else
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_653) then 19 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_369) then 23 else
  if p.val = (false, vertices_225) then 1 else
  if p.val = (true, vertices_30) then 17 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_608) then 13 else
  0
cert_priority
cert_nodeAtPriority_23 523 225 50 274 530 268 276 532 196 324 580 388 592 608 299 675 30 653 457 369
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 3 30
cert_row_4 1 0 3 4 5 8 626 50 3
cert_row_4 2 1 3 5 7 8 852 276 2
cert_row_4 3 1 4 5 6 8 740 196 1
cert_rows
cert_pivot_2 2 0 3 1
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 7 30 286 3
cert_coverFacet 1 542
cert_cover_5 1 0 0 1 2 8 30 542 3
cert_coverFacet 2 626
cert_cover_5 2 1 0 3 4 5 50 626 3
cert_coverFacet 3 306
cert_cover_2 3 3 0 4 7 50 306 3
cert_coverFacet 4 396
cert_cover_2 4 2 1 6 7 140 396 3
cert_coverFacet 5 852
cert_cover_5 5 2 1 3 5 7 276 852 2
cert_coverFacet 6 740
cert_cover_5 6 3 1 4 5 6 196 740 1
cert_coverFacet 7 452
cert_cover_2 7 5 1 6 7 196 452 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0633

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e10q1_0634.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0634

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 677, 809, 713, 433, 449, 94, 182, 198, 794, 402, 450, 604, 820, 708, 73, 265, 521, 161, 289, 545, 193, 321, 385, 641, 22, 70, 134, 26, 74, 266, 146, 274, 194, 322, 386, 92, 52, 532, 164, 548, 196, 580, 644, 536, 584, 776, 176, 304, 400, 784, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_677, vertices_809, vertices_713, vertices_433, vertices_449, vertices_94, vertices_182, vertices_198, vertices_794, vertices_402, vertices_450, vertices_604, vertices_820, vertices_708] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_265, vertices_521, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_385, vertices_641, vertices_22, vertices_70, vertices_134, vertices_26, vertices_74, vertices_266, vertices_146, vertices_274, vertices_194, vertices_322, vertices_386, vertices_92, vertices_52, vertices_532, vertices_164, vertices_548, vertices_196, vertices_580, vertices_644, vertices_536, vertices_584, vertices_776, vertices_176, vertices_304, vertices_400, vertices_784, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_677), (false, vertices_809), (false, vertices_713), (false, vertices_433), (false, vertices_449), (true, vertices_22), (true, vertices_70), (true, vertices_134), (true, vertices_26), (true, vertices_146), (true, vertices_274), (true, vertices_194), (true, vertices_386), (true, vertices_92), (true, vertices_52), (true, vertices_532), (true, vertices_196), (true, vertices_580), (true, vertices_536), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 16 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_809) then 21 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_92) then 19 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_196) then 11 else
  if p.val = (true, vertices_580) then 12 else
  if p.val = (true, vertices_536) then 13 else
  if p.val = (true, vertices_784) then 14 else
  0
cert_priority
cert_nodeAtPriority_65 449 2 22 1 70 3 134 26 146 274 194 386 52 532 196 580 536 784 331 677 92 809 713 433
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 5 92
cert_row_4 1 0 1 3 4 6 182 22 3
cert_row_4 2 0 2 3 7 8 794 26 3
cert_row_4 3 1 3 4 7 8 820 52 3
cert_rows
cert_pivot_2 5 6 0 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 3 22 94 2
cert_coverFacet 1 182
cert_cover_5 1 1 0 1 3 4 22 182 3
cert_coverFacet 2 198
cert_cover_2 2 1 0 5 6 70 198 3
cert_coverFacet 3 794
cert_cover_5 3 2 0 2 3 7 26 794 3
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 450
cert_cover_2 5 5 0 6 7 194 450 3
cert_coverFacet 6 604
cert_cover_5 6 0 1 2 3 8 92 604 3
cert_coverFacet 7 820
cert_cover_5 7 3 1 3 4 7 52 820 3
cert_coverFacet 8 708
cert_cover_2 8 5 1 6 8 196 708 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0634

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e10q1_0635.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0635

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [27, 779, 51, 675, 901, 313, 481, 94, 590, 626, 284, 780, 468, 740, 368, 11, 19, 35, 515, 25, 265, 49, 161, 289, 385, 641, 769, 78, 26, 522, 50, 82, 546, 578, 28, 268, 524, 84, 276, 196, 580, 388, 644, 772, 280, 776, 112, 304, 336, 224, 352, 608, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_27, vertices_779, vertices_51, vertices_675, vertices_901, vertices_313, vertices_481, vertices_94, vertices_590, vertices_626, vertices_284, vertices_780, vertices_468, vertices_740, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_35, vertices_515, vertices_25, vertices_265, vertices_49, vertices_161, vertices_289, vertices_385, vertices_641, vertices_769, vertices_78, vertices_26, vertices_522, vertices_50, vertices_82, vertices_546, vertices_578, vertices_28, vertices_268, vertices_524, vertices_84, vertices_276, vertices_196, vertices_580, vertices_388, vertices_644, vertices_772, vertices_280, vertices_776, vertices_112, vertices_304, vertices_336, vertices_224, vertices_352, vertices_608, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_27), (false, vertices_779), (false, vertices_51), (false, vertices_675), (false, vertices_901), (false, vertices_313), (false, vertices_481), (true, vertices_78), (true, vertices_82), (true, vertices_578), (true, vertices_28), (true, vertices_268), (true, vertices_524), (true, vertices_84), (true, vertices_276), (true, vertices_196), (true, vertices_580), (true, vertices_112), (true, vertices_336), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_27) then 0 else
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_51) then 1 else
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_901) then 19 else
  if p.val = (false, vertices_313) then 21 else
  if p.val = (false, vertices_481) then 24 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_608) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_27), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_51), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_78), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
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
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 3 4 5 8 626 50 3
cert_row_4 2 1 3 5 6 7 468 84 3
cert_row_4 3 1 4 5 6 8 740 196 1
cert_rows
cert_pivot_2 2 0 3 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 3 78 94 3
cert_coverFacet 1 590
cert_cover_5 1 0 0 1 2 8 78 590 3
cert_coverFacet 2 626
cert_cover_5 2 1 0 3 4 5 50 626 3
cert_coverFacet 3 284
cert_cover_2 3 2 1 3 7 28 284 3
cert_coverFacet 4 780
cert_cover_2 4 2 1 7 8 268 780 3
cert_coverFacet 5 468
cert_cover_5 5 2 1 3 5 6 84 468 3
cert_coverFacet 6 740
cert_cover_5 6 3 1 4 5 6 196 740 1
cert_coverFacet 7 368
cert_cover_2 7 4 3 5 7 112 368 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0635

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e10q1_0636.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0636

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [55, 307, 661, 805, 409, 961, 30, 78, 102, 282, 458, 866, 540, 620, 728, 51, 21, 37, 517, 145, 273, 289, 385, 641, 769, 14, 22, 38, 70, 26, 74, 266, 274, 98, 290, 322, 28, 76, 524, 532, 100, 548, 152, 280, 536, 200, 584, 392, 656, 608, 800, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_55, vertices_307, vertices_661, vertices_805, vertices_409, vertices_961, vertices_30, vertices_78, vertices_102, vertices_282, vertices_458, vertices_866, vertices_540, vertices_620, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_51, vertices_21, vertices_37, vertices_517, vertices_145, vertices_273, vertices_289, vertices_385, vertices_641, vertices_769, vertices_14, vertices_22, vertices_38, vertices_70, vertices_26, vertices_74, vertices_266, vertices_274, vertices_98, vertices_290, vertices_322, vertices_28, vertices_76, vertices_524, vertices_532, vertices_100, vertices_548, vertices_152, vertices_280, vertices_536, vertices_200, vertices_584, vertices_392, vertices_656, vertices_608, vertices_800, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_55), (false, vertices_307), (false, vertices_661), (false, vertices_805), (false, vertices_409), (false, vertices_961), (true, vertices_14), (true, vertices_70), (true, vertices_26), (true, vertices_74), (true, vertices_266), (true, vertices_98), (true, vertices_322), (true, vertices_28), (true, vertices_76), (true, vertices_524), (true, vertices_100), (true, vertices_536), (true, vertices_200), (true, vertices_584), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 24 25 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_55) then 16 else
  if p.val = (false, vertices_307) then 17 else
  if p.val = (false, vertices_661) then 19 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (false, vertices_409) then 22 else
  if p.val = (false, vertices_961) then 26 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_100) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_608) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_55), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 4 5 8 620 76 2
cert_row_4 1 0 4 5 7 8 866 98 3
cert_row_4 2 0 2 5 6 7 458 74 3
cert_row_4 3 2 3 5 6 8 728 152 2
cert_rows
cert_pivot_2 1 4 0 2
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 78
cert_cover_2 1 1 0 2 5 14 78 3
cert_coverFacet 2 102
cert_cover_2 2 1 0 4 5 38 102 3
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 458
cert_cover_5 4 2 0 2 5 6 74 458 3
cert_coverFacet 5 866
cert_cover_5 5 1 0 4 5 7 98 866 3
cert_coverFacet 6 540
cert_cover_2 6 2 1 3 8 28 540 3
cert_coverFacet 7 620
cert_cover_5 7 0 1 2 4 5 76 620 2
cert_coverFacet 8 728
cert_cover_5 8 3 2 3 5 6 152 728 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0636

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e10q1_0637.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0637

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [199, 613, 901, 809, 369, 449, 158, 86, 314, 906, 338, 450, 668, 596, 632, 69, 133, 517, 97, 289, 545, 193, 321, 385, 769, 22, 70, 134, 26, 138, 266, 82, 274, 194, 322, 386, 156, 84, 532, 580, 644, 56, 536, 296, 552, 648, 776, 112, 304, 336, 592, 608, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_199, vertices_613, vertices_901, vertices_809, vertices_369, vertices_449, vertices_158, vertices_86, vertices_314, vertices_906, vertices_338, vertices_450, vertices_668, vertices_596, vertices_632] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_517, vertices_97, vertices_289, vertices_545, vertices_193, vertices_321, vertices_385, vertices_769, vertices_22, vertices_70, vertices_134, vertices_26, vertices_138, vertices_266, vertices_82, vertices_274, vertices_194, vertices_322, vertices_386, vertices_156, vertices_84, vertices_532, vertices_580, vertices_644, vertices_56, vertices_536, vertices_296, vertices_552, vertices_648, vertices_776, vertices_112, vertices_304, vertices_336, vertices_592, vertices_608, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_199), (false, vertices_613), (false, vertices_901), (false, vertices_809), (false, vertices_369), (false, vertices_449), (true, vertices_22), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_82), (true, vertices_274), (true, vertices_322), (true, vertices_386), (true, vertices_156), (true, vertices_84), (true, vertices_532), (true, vertices_56), (true, vertices_536), (true, vertices_648), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_199) then 16 else
  if p.val = (false, vertices_613) then 18 else
  if p.val = (false, vertices_901) then 19 else
  if p.val = (false, vertices_809) then 22 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_156) then 20 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_648) then 13 else
  if p.val = (true, vertices_592) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_449), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_156), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
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
cert_row_2 0 1 2 3 6 156
cert_row_4 1 0 2 6 7 8 906 138 3
cert_row_4 2 0 2 3 4 7 314 26 3
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 0 0 1 2 3 22 158 2
cert_coverFacet 1 86
cert_cover_2 1 1 0 3 5 22 86 3
cert_coverFacet 2 314
cert_cover_5 2 2 0 2 3 4 26 314 3
cert_coverFacet 3 906
cert_cover_5 3 1 0 2 6 7 138 906 3
cert_coverFacet 4 338
cert_cover_2 4 3 0 5 7 82 338 3
cert_coverFacet 5 450
cert_cover_2 5 5 0 6 7 194 450 3
cert_coverFacet 6 668
cert_cover_5 6 0 1 2 3 8 156 668 3
cert_coverFacet 7 596
cert_cover_2 7 3 1 5 8 84 596 3
cert_coverFacet 8 632
cert_cover_5 8 3 2 3 4 5 56 632 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0637

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e10q1_0638.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0638

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 589, 213, 421, 773, 345, 401, 806, 122, 282, 618, 434, 676, 708, 752, 69, 133, 261, 517, 73, 265, 521, 81, 145, 273, 385, 769, 26, 106, 266, 522, 50, 274, 290, 546, 770, 164, 292, 548, 196, 580, 644, 772, 88, 280, 584, 112, 176, 208, 400, 608, 416, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_589, vertices_213, vertices_421, vertices_773, vertices_345, vertices_401, vertices_806, vertices_122, vertices_282, vertices_618, vertices_434, vertices_676, vertices_708, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_517, vertices_73, vertices_265, vertices_521, vertices_81, vertices_145, vertices_273, vertices_385, vertices_769, vertices_26, vertices_106, vertices_266, vertices_522, vertices_50, vertices_274, vertices_290, vertices_546, vertices_770, vertices_164, vertices_292, vertices_548, vertices_196, vertices_580, vertices_644, vertices_772, vertices_88, vertices_280, vertices_584, vertices_112, vertices_176, vertices_208, vertices_400, vertices_608, vertices_416, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_589), (false, vertices_213), (false, vertices_421), (false, vertices_773), (false, vertices_345), (false, vertices_401), (true, vertices_26), (true, vertices_106), (true, vertices_50), (true, vertices_274), (true, vertices_290), (true, vertices_546), (true, vertices_548), (true, vertices_644), (true, vertices_112), (true, vertices_176), (true, vertices_608), (true, vertices_672), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_589) then 18 else
  if p.val = (false, vertices_213) then 19 else
  if p.val = (false, vertices_421) then 20 else
  if p.val = (false, vertices_773) then 0 else
  if p.val = (false, vertices_345) then 22 else
  if p.val = (false, vertices_401) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_106) then 16 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_608) then 11 else
  if p.val = (true, vertices_672) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
cert_nodeAtPriority_4 0 773 1 401 26 50 274 290 546 548 644 112 176 608 672 704 779 106 589 213 421 345
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 4 5 106
cert_row_4 1 0 1 4 7 8 806 290 1
cert_row_4 2 0 3 4 6 7 434 50 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 2 1 0 3
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 1 0 1 4 7 290 806 1
cert_coverFacet 1 122
cert_cover_5 1 0 0 2 3 4 26 122 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 618
cert_cover_5 3 0 0 2 4 8 106 618 3
cert_coverFacet 4 434
cert_cover_5 4 2 0 3 4 6 50 434 3
cert_coverFacet 5 676
cert_cover_2 5 4 1 6 8 164 676 3
cert_coverFacet 6 708
cert_cover_2 6 5 1 6 8 196 708 3
cert_coverFacet 7 752
cert_cover_5 7 3 3 4 5 6 112 752 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0638

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m15e10q1_0639.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0639

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 419, 707, 361, 241, 833, 542, 150, 390, 658, 316, 844, 436, 120, 728, 131, 259, 515, 97, 161, 289, 193, 321, 577, 769, 22, 134, 262, 518, 146, 530, 386, 642, 28, 268, 524, 308, 148, 388, 772, 56, 88, 536, 104, 296, 328, 584, 112, 176, 208, 656, 416, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_419, vertices_707, vertices_361, vertices_241, vertices_833, vertices_542, vertices_150, vertices_390, vertices_658, vertices_316, vertices_844, vertices_436, vertices_120, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_97, vertices_161, vertices_289, vertices_193, vertices_321, vertices_577, vertices_769, vertices_22, vertices_134, vertices_262, vertices_518, vertices_146, vertices_530, vertices_386, vertices_642, vertices_28, vertices_268, vertices_524, vertices_308, vertices_148, vertices_388, vertices_772, vertices_56, vertices_88, vertices_536, vertices_104, vertices_296, vertices_328, vertices_584, vertices_112, vertices_176, vertices_208, vertices_656, vertices_416, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_419), (false, vertices_707), (false, vertices_361), (false, vertices_241), (false, vertices_833), (true, vertices_22), (true, vertices_134), (true, vertices_146), (true, vertices_530), (true, vertices_28), (true, vertices_268), (true, vertices_524), (true, vertices_308), (true, vertices_148), (true, vertices_388), (true, vertices_56), (true, vertices_88), (true, vertices_536), (true, vertices_584), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 16 else
  if p.val = (false, vertices_419) then 17 else
  if p.val = (false, vertices_707) then 18 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_241) then 24 else
  if p.val = (false, vertices_833) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_308) then 20 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_88) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_656) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_833), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(true, vertices_308), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 4 7 308
cert_row_4 1 0 1 2 3 8 542 22 2
cert_row_4 2 1 2 5 7 8 844 268 2
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 4 0 1 2
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 1 0 1 2 3 22 542 2
cert_coverFacet 1 150
cert_cover_2 1 1 0 3 6 22 150 3
cert_coverFacet 2 390
cert_cover_2 2 1 0 6 7 134 390 3
cert_coverFacet 3 658
cert_cover_2 3 3 0 6 8 146 658 3
cert_coverFacet 4 316
cert_cover_5 4 0 1 2 3 4 28 316 3
cert_coverFacet 5 844
cert_cover_5 5 2 1 2 5 7 268 844 2
cert_coverFacet 6 436
cert_cover_5 6 0 1 3 4 6 308 436 3
cert_coverFacet 7 120
cert_cover_2 7 3 2 4 5 56 120 3
cert_coverFacet 8 728
cert_cover_5 8 3 2 3 5 6 88 728 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0639

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m15e10q1_0640.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0640

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 229, 681, 369, 721, 801, 30, 270, 342, 538, 810, 604, 428, 716, 356, 81, 273, 529, 97, 161, 289, 545, 193, 641, 769, 14, 22, 262, 26, 266, 522, 274, 530, 770, 28, 588, 140, 268, 84, 100, 164, 292, 196, 324, 536, 168, 296, 552, 648, 336, 592, 352, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_229, vertices_681, vertices_369, vertices_721, vertices_801, vertices_30, vertices_270, vertices_342, vertices_538, vertices_810, vertices_604, vertices_428, vertices_716, vertices_356] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_273, vertices_529, vertices_97, vertices_161, vertices_289, vertices_545, vertices_193, vertices_641, vertices_769, vertices_14, vertices_22, vertices_262, vertices_26, vertices_266, vertices_522, vertices_274, vertices_530, vertices_770, vertices_28, vertices_588, vertices_140, vertices_268, vertices_84, vertices_100, vertices_164, vertices_292, vertices_196, vertices_324, vertices_536, vertices_168, vertices_296, vertices_552, vertices_648, vertices_336, vertices_592, vertices_352, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_229), (false, vertices_681), (false, vertices_369), (false, vertices_721), (false, vertices_801), (true, vertices_14), (true, vertices_22), (true, vertices_262), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_28), (true, vertices_588), (true, vertices_140), (true, vertices_268), (true, vertices_84), (true, vertices_292), (true, vertices_324), (true, vertices_536), (true, vertices_296)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 16 else
  if p.val = (false, vertices_229) then 18 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (false, vertices_369) then 23 else
  if p.val = (false, vertices_721) then 24 else
  if p.val = (false, vertices_801) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_588) then 19 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_84) then 10 else
  if p.val = (true, vertices_292) then 11 else
  if p.val = (true, vertices_324) then 12 else
  if p.val = (true, vertices_536) then 13 else
  if p.val = (true, vertices_296) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_801), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_588), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 7 342 22 3
cert_row_2 1 1 2 5 8 588
cert_row_4 2 0 2 4 7 8 810 266 2
cert_row_4 3 1 2 4 6 7 428 140 2
cert_rows
cert_pivot_2 3 5 0 1
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 342
cert_cover_5 2 0 0 1 3 5 22 342 3
cert_coverFacet 3 538
cert_cover_2 3 2 0 3 8 26 538 3
cert_coverFacet 4 810
cert_cover_5 4 2 0 2 4 7 266 810 2
cert_coverFacet 5 604
cert_cover_5 5 1 1 2 3 5 28 604 3
cert_coverFacet 6 428
cert_cover_5 6 3 1 2 4 6 140 428 2
cert_coverFacet 7 716
cert_cover_5 7 1 1 2 5 6 588 716 3
cert_coverFacet 8 356
cert_cover_2 8 4 1 5 7 100 356 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0640

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m15e10q1_0641.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0641

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 227, 835, 781, 681, 625, 310, 422, 114, 338, 668, 396, 180, 852, 688, 67, 131, 259, 137, 265, 521, 97, 161, 545, 577, 769, 294, 50, 82, 274, 98, 162, 322, 386, 140, 268, 524, 52, 148, 276, 532, 164, 388, 772, 392, 648, 112, 176, 560, 336, 592, 656, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_227, vertices_835, vertices_781, vertices_681, vertices_625, vertices_310, vertices_422, vertices_114, vertices_338, vertices_668, vertices_396, vertices_180, vertices_852, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_137, vertices_265, vertices_521, vertices_97, vertices_161, vertices_545, vertices_577, vertices_769, vertices_294, vertices_50, vertices_82, vertices_274, vertices_98, vertices_162, vertices_322, vertices_386, vertices_140, vertices_268, vertices_524, vertices_52, vertices_148, vertices_276, vertices_532, vertices_164, vertices_388, vertices_772, vertices_392, vertices_648, vertices_112, vertices_176, vertices_560, vertices_336, vertices_592, vertices_656, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_227), (false, vertices_835), (false, vertices_781), (false, vertices_681), (false, vertices_625), (true, vertices_294), (true, vertices_50), (true, vertices_82), (true, vertices_274), (true, vertices_140), (true, vertices_52), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_164), (true, vertices_388), (true, vertices_176), (true, vertices_336), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 13 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 17 else
  if p.val = (false, vertices_227) then 18 else
  if p.val = (false, vertices_835) then 19 else
  if p.val = (false, vertices_781) then 14 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (false, vertices_625) then 23 else
  if p.val = (true, vertices_294) then 15 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_656) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_294), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 4 7 294
cert_row_4 1 1 2 3 6 8 668 140 2
cert_row_4 2 1 3 5 7 8 852 276 2
cert_rows_3
cert_pivot_3 2 0 1
cert_heightProof 3
cert_coverFacet 0 310
cert_cover_5 0 0 0 1 3 4 294 310 2
cert_coverFacet 1 422
cert_cover_5 1 0 0 1 4 6 294 422 3
cert_coverFacet 2 114
cert_cover_2 2 3 0 4 5 50 114 3
cert_coverFacet 3 338
cert_cover_2 3 3 0 5 7 82 338 3
cert_coverFacet 4 668
cert_cover_5 4 1 1 2 3 6 140 668 2
cert_coverFacet 5 396
cert_cover_2 5 2 1 6 7 140 396 3
cert_coverFacet 6 180
cert_cover_2 6 3 1 4 6 52 180 3
cert_coverFacet 7 852
cert_cover_5 7 2 1 3 5 7 276 852 2
cert_coverFacet 8 688
cert_cover_2 8 4 3 6 8 176 688 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 3 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0641

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m15e10q1_0642.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0642

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 53, 213, 293, 837, 809, 689, 454, 570, 154, 842, 394, 658, 316, 412, 21, 37, 69, 261, 49, 145, 289, 545, 193, 577, 641, 769, 26, 138, 266, 522, 146, 530, 194, 322, 578, 386, 642, 284, 52, 148, 292, 196, 324, 388, 56, 152, 296, 552, 392, 776, 560, 656, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_53, vertices_213, vertices_293, vertices_837, vertices_809, vertices_689, vertices_454, vertices_570, vertices_154, vertices_842, vertices_394, vertices_658, vertices_316, vertices_412] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_69, vertices_261, vertices_49, vertices_145, vertices_289, vertices_545, vertices_193, vertices_577, vertices_641, vertices_769, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_530, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_284, vertices_52, vertices_148, vertices_292, vertices_196, vertices_324, vertices_388, vertices_56, vertices_152, vertices_296, vertices_552, vertices_392, vertices_776, vertices_560, vertices_656, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_53), (false, vertices_213), (false, vertices_293), (false, vertices_837), (false, vertices_809), (false, vertices_689), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_530), (true, vertices_322), (true, vertices_386), (true, vertices_284), (true, vertices_388), (true, vertices_56), (true, vertices_152), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 15 else
  if p.val = (false, vertices_53) then 0 else
  if p.val = (false, vertices_213) then 17 else
  if p.val = (false, vertices_293) then 1 else
  if p.val = (false, vertices_837) then 18 else
  if p.val = (false, vertices_809) then 21 else
  if p.val = (false, vertices_689) then 23 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_322) then 8 else
  if p.val = (true, vertices_386) then 9 else
  if p.val = (true, vertices_284) then 19 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_392) then 13 else
  0
cert_priority
cert_nodeAtPriority_54 53 293 26 138 266 522 146 530 322 386 388 56 152 392 707 213 837 284 809 689
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 194 1
cert_row_2 1 1 2 3 7 284
cert_row_4 2 0 2 3 4 8 570 26 3
cert_row_4 3 0 2 5 7 8 842 266 2
cert_rows
cert_pivot_2 6 1 3 0
cert_heightProof 4
cert_coverFacet 0 454
cert_cover_5 0 0 0 1 5 6 194 454 1
cert_coverFacet 1 570
cert_cover_5 1 2 0 2 3 4 26 570 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 842
cert_cover_5 3 3 0 2 5 7 266 842 2
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 658
cert_cover_2 5 3 0 6 8 146 658 3
cert_coverFacet 6 316
cert_cover_5 6 1 1 2 3 4 284 316 3
cert_coverFacet 7 412
cert_cover_5 7 1 1 2 3 6 284 412 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0642

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m15e10q1_0644.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0644

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [59, 331, 659, 771, 901, 297, 433, 838, 538, 586, 364, 740, 420, 248, 728, 11, 19, 259, 515, 41, 265, 49, 145, 289, 385, 641, 769, 26, 74, 522, 530, 322, 578, 770, 100, 164, 292, 324, 580, 388, 644, 772, 56, 216, 536, 104, 296, 328, 584, 176, 656, 224, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_59, vertices_331, vertices_659, vertices_771, vertices_901, vertices_297, vertices_433, vertices_838, vertices_538, vertices_586, vertices_364, vertices_740, vertices_420, vertices_248, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_259, vertices_515, vertices_41, vertices_265, vertices_49, vertices_145, vertices_289, vertices_385, vertices_641, vertices_769, vertices_26, vertices_74, vertices_522, vertices_530, vertices_322, vertices_578, vertices_770, vertices_100, vertices_164, vertices_292, vertices_324, vertices_580, vertices_388, vertices_644, vertices_772, vertices_56, vertices_216, vertices_536, vertices_104, vertices_296, vertices_328, vertices_584, vertices_176, vertices_656, vertices_224, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_59), (false, vertices_331), (false, vertices_659), (false, vertices_771), (false, vertices_901), (false, vertices_297), (false, vertices_433), (true, vertices_522), (true, vertices_578), (true, vertices_100), (true, vertices_164), (true, vertices_292), (true, vertices_324), (true, vertices_580), (true, vertices_216), (true, vertices_536), (true, vertices_104), (true, vertices_584), (true, vertices_224), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_59) then 15 else
  if p.val = (false, vertices_331) then 16 else
  if p.val = (false, vertices_659) then 17 else
  if p.val = (false, vertices_771) then 0 else
  if p.val = (false, vertices_901) then 19 else
  if p.val = (false, vertices_297) then 1 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_100) then 4 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_216) then 21 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_771), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_297), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_59), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
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
cert_row_2 0 2 3 5 6 216
cert_row_4 1 0 1 5 7 8 838 322 1
cert_row_4 2 1 2 4 5 7 364 100 1
cert_row_4 3 1 4 5 6 8 740 100 3
cert_rows
cert_pivot_2 3 0 2 1
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 1 0 1 5 7 322 838 1
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 586
cert_cover_2 2 2 0 5 8 74 586 3
cert_coverFacet 3 364
cert_cover_5 3 2 1 2 4 5 100 364 1
cert_coverFacet 4 740
cert_cover_5 4 3 1 4 5 6 100 740 3
cert_coverFacet 5 420
cert_cover_2 5 4 1 6 7 164 420 3
cert_coverFacet 6 248
cert_cover_5 6 0 2 3 4 5 56 248 3
cert_coverFacet 7 728
cert_cover_5 7 0 2 3 5 8 216 728 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0644

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m15e10q1_0645.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0645

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 205, 397, 357, 617, 817, 710, 410, 202, 586, 690, 786, 436, 612, 676, 141, 69, 261, 73, 265, 521, 97, 289, 545, 769, 74, 138, 266, 522, 146, 274, 530, 194, 578, 642, 770, 100, 164, 292, 548, 196, 580, 388, 644, 200, 584, 392, 176, 304, 560, 400, 784, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_205, vertices_397, vertices_357, vertices_617, vertices_817, vertices_710, vertices_410, vertices_202, vertices_586, vertices_690, vertices_786, vertices_436, vertices_612, vertices_676] (by decide +kernel)
  polygons := literalFinset [vertices_141, vertices_69, vertices_261, vertices_73, vertices_265, vertices_521, vertices_97, vertices_289, vertices_545, vertices_769, vertices_74, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_194, vertices_578, vertices_642, vertices_770, vertices_100, vertices_164, vertices_292, vertices_548, vertices_196, vertices_580, vertices_388, vertices_644, vertices_200, vertices_584, vertices_392, vertices_176, vertices_304, vertices_560, vertices_400, vertices_784, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_205), (false, vertices_397), (false, vertices_357), (false, vertices_617), (false, vertices_817), (true, vertices_74), (true, vertices_138), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_194), (true, vertices_578), (true, vertices_642), (true, vertices_164), (true, vertices_548), (true, vertices_580), (true, vertices_644), (true, vertices_176), (true, vertices_400), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_205) then 18 else
  if p.val = (false, vertices_397) then 19 else
  if p.val = (false, vertices_357) then 20 else
  if p.val = (false, vertices_617) then 22 else
  if p.val = (false, vertices_817) then 24 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_672) then 14 else
  0
cert_priority
cert_nodeAtPriority_68 0 74 1 138 146 274 530 194 578 642 164 548 580 644 176 400 672 779 205 397 357 617 817
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 8 710 194 1
cert_row_4 1 0 2 3 6 7 410 138 2
cert_row_4 2 0 3 4 6 8 690 146 2
cert_row_4 3 1 3 4 6 7 436 164 1
cert_rows
cert_pivot_2 5 2 0 1
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 0 0 1 5 6 194 710 1
cert_coverFacet 1 410
cert_cover_5 1 1 0 2 3 6 138 410 2
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 586
cert_cover_2 3 2 0 5 8 74 586 3
cert_coverFacet 4 690
cert_cover_5 4 2 0 3 4 6 146 690 2
cert_coverFacet 5 786
cert_cover_2 5 3 0 7 8 274 786 3
cert_coverFacet 6 436
cert_cover_5 6 3 1 3 4 6 164 436 1
cert_coverFacet 7 612
cert_cover_2 7 4 1 5 8 100 612 3
cert_coverFacet 8 676
cert_cover_2 8 4 1 6 8 164 676 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0645

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e10q1_0646.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0646

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 789, 809, 369, 721, 214, 342, 390, 682, 354, 418, 706, 668, 428, 780, 81, 273, 529, 97, 289, 545, 577, 769, 86, 134, 262, 98, 162, 290, 546, 194, 322, 578, 386, 642, 140, 268, 524, 148, 276, 532, 388, 772, 168, 296, 552, 648, 776, 208, 336, 656, 352, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_789, vertices_809, vertices_369, vertices_721, vertices_214, vertices_342, vertices_390, vertices_682, vertices_354, vertices_418, vertices_706, vertices_668, vertices_428, vertices_780] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_273, vertices_529, vertices_97, vertices_289, vertices_545, vertices_577, vertices_769, vertices_86, vertices_134, vertices_262, vertices_98, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_140, vertices_268, vertices_524, vertices_148, vertices_276, vertices_532, vertices_388, vertices_772, vertices_168, vertices_296, vertices_552, vertices_648, vertices_776, vertices_208, vertices_336, vertices_656, vertices_352, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_789), (false, vertices_809), (false, vertices_369), (false, vertices_721), (true, vertices_86), (true, vertices_134), (true, vertices_262), (true, vertices_162), (true, vertices_290), (true, vertices_194), (true, vertices_322), (true, vertices_386), (true, vertices_642), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_148), (true, vertices_388), (true, vertices_168), (true, vertices_648), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 23 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 17 else
  if p.val = (false, vertices_789) then 20 else
  if p.val = (false, vertices_809) then 22 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (false, vertices_721) then 25 else
  if p.val = (true, vertices_86) then 18 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_148) then 11 else
  if p.val = (true, vertices_388) then 12 else
  if p.val = (true, vertices_168) then 13 else
  if p.val = (true, vertices_648) then 14 else
  if p.val = (true, vertices_416) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_86), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 5 86
cert_row_4 1 0 2 4 6 8 682 162 1
cert_row_4 2 1 2 3 6 8 668 140 2
cert_row_4 3 1 2 4 6 7 428 140 2
cert_rows
cert_pivot_2 5 0 3 1
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 6 86 214 3
cert_coverFacet 1 342
cert_cover_5 1 0 0 1 3 7 86 342 3
cert_coverFacet 2 390
cert_cover_2 2 1 0 6 7 134 390 3
cert_coverFacet 3 682
cert_cover_5 3 1 0 2 4 6 162 682 1
cert_coverFacet 4 354
cert_cover_2 4 4 0 5 7 98 354 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 706
cert_cover_2 6 5 0 6 8 194 706 3
cert_coverFacet 7 668
cert_cover_5 7 2 1 2 3 6 140 668 2
cert_coverFacet 8 428
cert_cover_5 8 3 1 2 4 6 140 428 2
cert_coverFacet 9 780
cert_cover_2 9 2 1 7 8 268 780 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0646

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e10q1_0647.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0647

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 837, 665, 809, 457, 614, 570, 114, 210, 658, 316, 412, 244, 804, 452, 137, 265, 521, 193, 321, 577, 641, 769, 50, 82, 146, 530, 98, 546, 194, 578, 642, 284, 52, 148, 100, 292, 548, 196, 324, 580, 388, 772, 56, 152, 536, 296, 552, 392, 112, 208, 656, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_837, vertices_665, vertices_809, vertices_457, vertices_614, vertices_570, vertices_114, vertices_210, vertices_658, vertices_316, vertices_412, vertices_244, vertices_804, vertices_452] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_50, vertices_82, vertices_146, vertices_530, vertices_98, vertices_546, vertices_194, vertices_578, vertices_642, vertices_284, vertices_52, vertices_148, vertices_100, vertices_292, vertices_548, vertices_196, vertices_324, vertices_580, vertices_388, vertices_772, vertices_56, vertices_152, vertices_536, vertices_296, vertices_552, vertices_392, vertices_112, vertices_208, vertices_656, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_837), (false, vertices_665), (false, vertices_809), (false, vertices_457), (true, vertices_50), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_98), (true, vertices_546), (true, vertices_284), (true, vertices_52), (true, vertices_148), (true, vertices_100), (true, vertices_292), (true, vertices_548), (true, vertices_196), (true, vertices_388), (true, vertices_56), (true, vertices_112), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 21 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 17 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_665) then 22 else
  if p.val = (false, vertices_809) then 23 else
  if p.val = (false, vertices_457) then 24 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_284) then 20 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_196) then 11 else
  if p.val = (true, vertices_388) then 12 else
  if p.val = (true, vertices_56) then 13 else
  if p.val = (true, vertices_112) then 14 else
  if p.val = (true, vertices_208) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_284), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 7 284
cert_row_4 1 0 2 3 4 8 570 50 1
cert_row_4 2 0 1 4 5 8 614 98 1
cert_row_4 3 1 3 4 5 6 244 52 3
cert_rows
cert_pivot_2 7 2 0 1
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_5 0 2 0 1 4 5 98 614 1
cert_coverFacet 1 570
cert_cover_5 1 1 0 2 3 4 50 570 1
cert_coverFacet 2 114
cert_cover_2 2 3 0 4 5 50 114 3
cert_coverFacet 3 210
cert_cover_2 3 3 0 5 6 82 210 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 316
cert_cover_5 5 0 1 2 3 4 284 316 3
cert_coverFacet 6 412
cert_cover_5 6 0 1 2 3 6 284 412 3
cert_coverFacet 7 244
cert_cover_5 7 3 1 3 4 5 52 244 3
cert_coverFacet 8 804
cert_cover_2 8 4 1 7 8 292 804 3
cert_coverFacet 9 452
cert_cover_2 9 5 1 6 7 196 452 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0647

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e10q1_0648.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0648

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 395, 659, 109, 653, 293, 361, 818, 466, 588, 628, 804, 728, 456, 368, 131, 259, 515, 13, 37, 261, 517, 105, 137, 265, 289, 641, 146, 274, 530, 386, 770, 76, 524, 100, 292, 548, 580, 772, 200, 328, 584, 392, 648, 112, 304, 560, 208, 336, 592, 656, 352, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_395, vertices_659, vertices_109, vertices_653, vertices_293, vertices_361, vertices_818, vertices_466, vertices_588, vertices_628, vertices_804, vertices_728, vertices_456, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_13, vertices_37, vertices_261, vertices_517, vertices_105, vertices_137, vertices_265, vertices_289, vertices_641, vertices_146, vertices_274, vertices_530, vertices_386, vertices_770, vertices_76, vertices_524, vertices_100, vertices_292, vertices_548, vertices_580, vertices_772, vertices_200, vertices_328, vertices_584, vertices_392, vertices_648, vertices_112, vertices_304, vertices_560, vertices_208, vertices_336, vertices_592, vertices_656, vertices_352, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_395), (false, vertices_659), (false, vertices_109), (false, vertices_653), (false, vertices_293), (false, vertices_361), (true, vertices_274), (true, vertices_548), (true, vertices_580), (true, vertices_200), (true, vertices_584), (true, vertices_112), (true, vertices_304), (true, vertices_560), (true, vertices_208), (true, vertices_336), (true, vertices_592), (true, vertices_800), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 15 else
  if p.val = (false, vertices_395) then 16 else
  if p.val = (false, vertices_659) then 17 else
  if p.val = (false, vertices_109) then 21 else
  if p.val = (false, vertices_653) then 19 else
  if p.val = (false, vertices_293) then 0 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_548) then 2 else
  if p.val = (true, vertices_580) then 3 else
  if p.val = (true, vertices_200) then 4 else
  if p.val = (true, vertices_584) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_800) then 12 else
  if p.val = (true, vertices_448) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_293), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 4 5 8 628 100 1
cert_row_4 1 0 3 4 7 8 818 274 2
cert_row_4 2 0 3 5 6 7 466 146 2
cert_row_4 3 2 3 5 6 8 728 200 1
cert_rows
cert_pivot_2 1 4 0 2
cert_heightProof 4
cert_coverFacet 0 818
cert_cover_5 0 1 0 3 4 7 274 818 2
cert_coverFacet 1 466
cert_cover_5 1 2 0 3 5 6 146 466 2
cert_coverFacet 2 588
cert_cover_2 2 2 1 5 8 76 588 3
cert_coverFacet 3 628
cert_cover_5 3 0 1 3 4 5 100 628 1
cert_coverFacet 4 804
cert_cover_2 4 4 1 7 8 292 804 3
cert_coverFacet 5 728
cert_cover_5 5 3 2 3 5 6 200 728 1
cert_coverFacet 6 456
cert_cover_2 6 5 2 6 7 200 456 3
cert_coverFacet 7 368
cert_cover_2 7 4 3 5 7 112 368 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0648

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_3213 : Certifies 3213 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0618.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3214 : Certifies 3214 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0619.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3215 : Certifies 3215 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0620.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3216 : Certifies 3216 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0621.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3217 : Certifies 3217 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0622.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3218 : Certifies 3218 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0623.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3219 : Certifies 3219 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0624.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3220 : Certifies 3220 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0625.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3221 : Certifies 3221 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0626.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3222 : Certifies 3222 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0627.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3223 : Certifies 3223 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0628.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3224 : Certifies 3224 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0629.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3225 : Certifies 3225 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0630.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3226 : Certifies 3226 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0631.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3227 : Certifies 3227 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0632.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3228 : Certifies 3228 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0633.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3229 : Certifies 3229 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0634.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3230 : Certifies 3230 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0635.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3231 : Certifies 3231 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0636.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3232 : Certifies 3232 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0637.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3233 : Certifies 3233 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0638.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3234 : Certifies 3234 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0639.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3235 : Certifies 3235 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0640.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3236 : Certifies 3236 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0641.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3237 : Certifies 3237 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0642.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3238 : Certifies 3238 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0644.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3239 : Certifies 3239 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0645.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3240 : Certifies 3240 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0646.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3241 : Certifies 3241 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0647.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3242 : Certifies 3242 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0648.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B106 (j : Fin 30) :
    Certifies (3213 + j.val) := by
  fin_cases j
  · exact projection_3213
  · exact projection_3214
  · exact projection_3215
  · exact projection_3216
  · exact projection_3217
  · exact projection_3218
  · exact projection_3219
  · exact projection_3220
  · exact projection_3221
  · exact projection_3222
  · exact projection_3223
  · exact projection_3224
  · exact projection_3225
  · exact projection_3226
  · exact projection_3227
  · exact projection_3228
  · exact projection_3229
  · exact projection_3230
  · exact projection_3231
  · exact projection_3232
  · exact projection_3233
  · exact projection_3234
  · exact projection_3235
  · exact projection_3236
  · exact projection_3237
  · exact projection_3238
  · exact projection_3239
  · exact projection_3240
  · exact projection_3241
  · exact projection_3242

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
