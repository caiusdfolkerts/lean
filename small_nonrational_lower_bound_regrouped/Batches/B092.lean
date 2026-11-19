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
/- Source: ProjectionCertificates/R_m15e10q1_0181.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0181

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 205, 269, 661, 361, 465, 785, 558, 270, 298, 370, 690, 786, 684, 248, 13, 133, 261, 517, 73, 265, 145, 273, 529, 193, 321, 769, 14, 262, 518, 42, 266, 50, 274, 530, 290, 546, 770, 556, 140, 268, 644, 104, 168, 296, 200, 112, 176, 208, 336, 656, 784, 352, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_205, vertices_269, vertices_661, vertices_361, vertices_465, vertices_785, vertices_558, vertices_270, vertices_298, vertices_370, vertices_690, vertices_786, vertices_684, vertices_248] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_261, vertices_517, vertices_73, vertices_265, vertices_145, vertices_273, vertices_529, vertices_193, vertices_321, vertices_769, vertices_14, vertices_262, vertices_518, vertices_42, vertices_266, vertices_50, vertices_274, vertices_530, vertices_290, vertices_546, vertices_770, vertices_556, vertices_140, vertices_268, vertices_644, vertices_104, vertices_168, vertices_296, vertices_200, vertices_112, vertices_176, vertices_208, vertices_336, vertices_656, vertices_784, vertices_352, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_205), (false, vertices_269), (false, vertices_661), (false, vertices_361), (false, vertices_465), (false, vertices_785), (true, vertices_14), (true, vertices_42), (true, vertices_266), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_546), (true, vertices_556), (true, vertices_168), (true, vertices_112), (true, vertices_176), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 15 else
  if p.val = (false, vertices_205) then 17 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_661) then 18 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (false, vertices_785) then 1 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_290) then 8 else
  if p.val = (true, vertices_546) then 9 else
  if p.val = (true, vertices_556) then 19 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
cert_nodeAtPriority_54 269 785 14 42 266 50 274 530 290 546 168 112 176 672 775 205 661 556 361 465
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 4 8 556
cert_row_4 1 0 3 4 5 7 370 50 3
cert_row_4 2 0 3 4 6 8 690 50 3
cert_row_4 3 2 3 4 5 6 248 104 1
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 0 0 1 2 4 14 558 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 298
cert_cover_2 2 2 0 4 7 42 298 3
cert_coverFacet 3 370
cert_cover_5 3 1 0 3 4 5 50 370 3
cert_coverFacet 4 690
cert_cover_5 4 2 0 3 4 6 50 690 3
cert_coverFacet 5 786
cert_cover_2 5 3 0 7 8 274 786 3
cert_coverFacet 6 684
cert_cover_5 6 0 1 2 4 6 556 684 3
cert_coverFacet 7 248
cert_cover_5 7 3 2 3 4 5 104 248 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0181

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e10q1_0182.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0182

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 109, 269, 709, 773, 425, 241, 542, 314, 778, 434, 722, 60, 780, 628, 13, 69, 261, 517, 41, 265, 97, 161, 193, 385, 641, 769, 26, 266, 522, 306, 146, 530, 386, 642, 770, 28, 44, 268, 524, 52, 532, 100, 580, 772, 56, 296, 776, 112, 176, 208, 592, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_109, vertices_269, vertices_709, vertices_773, vertices_425, vertices_241, vertices_542, vertices_314, vertices_778, vertices_434, vertices_722, vertices_60, vertices_780, vertices_628] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_261, vertices_517, vertices_41, vertices_265, vertices_97, vertices_161, vertices_193, vertices_385, vertices_641, vertices_769, vertices_26, vertices_266, vertices_522, vertices_306, vertices_146, vertices_530, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_268, vertices_524, vertices_52, vertices_532, vertices_100, vertices_580, vertices_772, vertices_56, vertices_296, vertices_776, vertices_112, vertices_176, vertices_208, vertices_592, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_109), (false, vertices_269), (false, vertices_709), (false, vertices_773), (false, vertices_425), (false, vertices_241), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_306), (true, vertices_146), (true, vertices_530), (true, vertices_28), (true, vertices_524), (true, vertices_52), (true, vertices_532), (true, vertices_56), (true, vertices_776), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 15 else
  if p.val = (false, vertices_109) then 18 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_773) then 1 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_306) then 16 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_592) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 0 269 1 773 26 266 522 146 530 28 524 52 532 56 776 592 899 306 109 709 425 241
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 4 7 306
cert_row_4 1 0 1 2 3 8 542 26 1
cert_row_4 2 0 3 5 6 8 722 146 2
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 7 2 0 1
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 1 0 1 2 3 26 542 1
cert_coverFacet 1 314
cert_cover_5 1 0 0 2 3 4 26 314 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 434
cert_cover_5 3 0 0 3 4 6 306 434 3
cert_coverFacet 4 722
cert_cover_5 4 2 0 3 5 6 146 722 2
cert_coverFacet 5 60
cert_cover_2 5 2 1 3 4 28 60 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 628
cert_cover_5 7 3 1 3 4 5 52 628 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0182

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e10q1_0183.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0183

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 285, 653, 149, 841, 817, 182, 230, 714, 562, 866, 396, 372, 452, 456, 13, 21, 133, 265, 521, 145, 273, 529, 641, 769, 166, 50, 146, 530, 98, 546, 194, 578, 642, 140, 268, 52, 148, 276, 100, 196, 324, 388, 200, 328, 584, 392, 648, 304, 560, 352, 800, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_285, vertices_653, vertices_149, vertices_841, vertices_817, vertices_182, vertices_230, vertices_714, vertices_562, vertices_866, vertices_396, vertices_372, vertices_452, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_133, vertices_265, vertices_521, vertices_145, vertices_273, vertices_529, vertices_641, vertices_769, vertices_166, vertices_50, vertices_146, vertices_530, vertices_98, vertices_546, vertices_194, vertices_578, vertices_642, vertices_140, vertices_268, vertices_52, vertices_148, vertices_276, vertices_100, vertices_196, vertices_324, vertices_388, vertices_200, vertices_328, vertices_584, vertices_392, vertices_648, vertices_304, vertices_560, vertices_352, vertices_800, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_285), (false, vertices_653), (false, vertices_149), (false, vertices_841), (false, vertices_817), (true, vertices_166), (true, vertices_50), (true, vertices_98), (true, vertices_546), (true, vertices_194), (true, vertices_578), (true, vertices_52), (true, vertices_100), (true, vertices_196), (true, vertices_324), (true, vertices_388), (true, vertices_200), (true, vertices_392), (true, vertices_352), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 16 else
  if p.val = (false, vertices_285) then 19 else
  if p.val = (false, vertices_653) then 20 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_841) then 22 else
  if p.val = (false, vertices_817) then 24 else
  if p.val = (true, vertices_166) then 17 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_100) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_352) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
cert_nodeAtPriority_22 149 50 98 546 194 578 52 100 196 324 388 200 392 352 448 659 166 285 653 841 817
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 8 714 194 1
cert_row_2 1 0 1 4 6 166
cert_row_4 2 0 4 5 7 8 866 98 3
cert_row_4 3 1 3 4 5 7 372 52 3
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 1 0 1 3 4 166 182 2
cert_coverFacet 1 230
cert_cover_5 1 1 0 1 4 5 166 230 3
cert_coverFacet 2 714
cert_cover_5 2 0 0 2 5 6 194 714 1
cert_coverFacet 3 562
cert_cover_2 3 3 0 4 8 50 562 3
cert_coverFacet 4 866
cert_cover_5 4 2 0 4 5 7 98 866 3
cert_coverFacet 5 396
cert_cover_2 5 2 1 6 7 140 396 3
cert_coverFacet 6 372
cert_cover_5 6 3 1 3 4 5 52 372 3
cert_coverFacet 7 452
cert_cover_2 7 5 1 6 7 196 452 3
cert_coverFacet 8 456
cert_cover_2 8 5 2 6 7 200 456 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0183

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e10q1_0184.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0184

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 653, 213, 837, 393, 369, 401, 678, 186, 314, 650, 866, 628, 180, 408, 69, 133, 517, 137, 265, 521, 81, 145, 273, 321, 385, 769, 58, 138, 266, 522, 162, 290, 546, 642, 770, 52, 84, 148, 164, 548, 580, 644, 152, 280, 392, 648, 112, 176, 304, 400, 352, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_653, vertices_213, vertices_837, vertices_393, vertices_369, vertices_401, vertices_678, vertices_186, vertices_314, vertices_650, vertices_866, vertices_628, vertices_180, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_517, vertices_137, vertices_265, vertices_521, vertices_81, vertices_145, vertices_273, vertices_321, vertices_385, vertices_769, vertices_58, vertices_138, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_52, vertices_84, vertices_148, vertices_164, vertices_548, vertices_580, vertices_644, vertices_152, vertices_280, vertices_392, vertices_648, vertices_112, vertices_176, vertices_304, vertices_400, vertices_352, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_653), (false, vertices_213), (false, vertices_837), (false, vertices_393), (false, vertices_369), (false, vertices_401), (true, vertices_58), (true, vertices_138), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_642), (true, vertices_52), (true, vertices_164), (true, vertices_548), (true, vertices_152), (true, vertices_280), (true, vertices_176), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_213) then 19 else
  if p.val = (false, vertices_837) then 20 else
  if p.val = (false, vertices_393) then 0 else
  if p.val = (false, vertices_369) then 23 else
  if p.val = (false, vertices_401) then 1 else
  if p.val = (true, vertices_58) then 16 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_608) then 13 else
  0
cert_priority
cert_nodeAtPriority_15 0 393 1 401 138 162 290 546 642 52 164 548 152 280 176 608 779 58 653 213 837 369
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 4 58
cert_row_4 1 0 1 4 6 8 678 162 1
cert_row_4 2 0 4 5 7 8 866 290 2
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 1 0 1 4 6 162 678 1
cert_coverFacet 1 186
cert_cover_5 1 0 0 2 3 6 58 186 3
cert_coverFacet 2 314
cert_cover_5 2 0 0 2 3 7 58 314 3
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 866
cert_cover_5 4 2 0 4 5 7 290 866 2
cert_coverFacet 5 628
cert_cover_5 5 3 1 3 4 5 52 628 3
cert_coverFacet 6 180
cert_cover_2 6 3 1 4 6 52 180 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0184

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e10q1_0185.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0185

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 157, 525, 309, 773, 713, 689, 342, 842, 242, 306, 738, 460, 780, 212, 13, 21, 261, 517, 137, 521, 49, 145, 289, 545, 641, 769, 50, 82, 274, 226, 290, 546, 322, 578, 770, 140, 268, 524, 84, 148, 276, 196, 324, 772, 200, 328, 584, 776, 176, 304, 208, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_157, vertices_525, vertices_309, vertices_773, vertices_713, vertices_689, vertices_342, vertices_842, vertices_242, vertices_306, vertices_738, vertices_460, vertices_780, vertices_212] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_261, vertices_517, vertices_137, vertices_521, vertices_49, vertices_145, vertices_289, vertices_545, vertices_641, vertices_769, vertices_50, vertices_82, vertices_274, vertices_226, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_140, vertices_268, vertices_524, vertices_84, vertices_148, vertices_276, vertices_196, vertices_324, vertices_772, vertices_200, vertices_328, vertices_584, vertices_776, vertices_176, vertices_304, vertices_208, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_157), (false, vertices_525), (false, vertices_309), (false, vertices_773), (false, vertices_713), (false, vertices_689), (true, vertices_50), (true, vertices_82), (true, vertices_274), (true, vertices_226), (true, vertices_322), (true, vertices_578), (true, vertices_268), (true, vertices_84), (true, vertices_196), (true, vertices_324), (true, vertices_328), (true, vertices_776), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 15 else
  if p.val = (false, vertices_157) then 18 else
  if p.val = (false, vertices_525) then 0 else
  if p.val = (false, vertices_309) then 19 else
  if p.val = (false, vertices_773) then 1 else
  if p.val = (false, vertices_713) then 21 else
  if p.val = (false, vertices_689) then 23 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_226) then 16 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_208) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 0 525 1 773 50 82 274 322 578 268 84 196 324 328 776 208 803 226 157 309 713 689
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 4 5 6 226
cert_row_4 1 0 1 3 5 7 342 82 1
cert_row_4 2 0 2 5 7 8 842 322 1
cert_row_4 3 1 2 5 6 7 460 140 2
cert_rows
cert_pivot_2 4 3 0 1
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 1 0 1 3 5 82 342 1
cert_coverFacet 1 842
cert_cover_5 1 2 0 2 5 7 322 842 1
cert_coverFacet 2 242
cert_cover_5 2 0 0 3 4 5 50 242 3
cert_coverFacet 3 306
cert_cover_2 3 3 0 4 7 50 306 3
cert_coverFacet 4 738
cert_cover_5 4 0 0 4 5 8 226 738 3
cert_coverFacet 5 460
cert_cover_5 5 3 1 2 5 6 140 460 2
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 212
cert_cover_2 7 3 1 5 6 84 212 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0185

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e10q1_0186.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0186

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 781, 105, 713, 913, 481, 110, 270, 118, 534, 774, 434, 786, 604, 752, 41, 73, 265, 521, 97, 289, 193, 385, 641, 769, 14, 22, 102, 262, 518, 42, 266, 50, 274, 530, 290, 770, 76, 268, 524, 84, 532, 772, 104, 584, 112, 176, 592, 400, 656, 784, 224, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_781, vertices_105, vertices_713, vertices_913, vertices_481, vertices_110, vertices_270, vertices_118, vertices_534, vertices_774, vertices_434, vertices_786, vertices_604, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_265, vertices_521, vertices_97, vertices_289, vertices_193, vertices_385, vertices_641, vertices_769, vertices_14, vertices_22, vertices_102, vertices_262, vertices_518, vertices_42, vertices_266, vertices_50, vertices_274, vertices_530, vertices_290, vertices_770, vertices_76, vertices_268, vertices_524, vertices_84, vertices_532, vertices_772, vertices_104, vertices_584, vertices_112, vertices_176, vertices_592, vertices_400, vertices_656, vertices_784, vertices_224, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_781), (false, vertices_105), (false, vertices_713), (false, vertices_913), (false, vertices_481), (true, vertices_14), (true, vertices_22), (true, vertices_102), (true, vertices_262), (true, vertices_518), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_770), (true, vertices_76), (true, vertices_84), (true, vertices_532), (true, vertices_112), (true, vertices_176), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 16 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_105) then 0 else
  if p.val = (false, vertices_713) then 21 else
  if p.val = (false, vertices_913) then 23 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_102) then 17 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_76) then 9 else
  if p.val = (true, vertices_84) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_592) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 105 14 22 262 518 50 274 530 770 76 84 532 112 176 592 299 102 781 713 913 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 6 7 434 50 3
cert_row_2 1 0 1 4 5 102
cert_row_4 2 1 2 3 5 8 604 76 2
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 7 0 1 3
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 1 0 1 2 4 14 110 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 118
cert_cover_5 2 1 0 1 3 4 22 118 3
cert_coverFacet 3 534
cert_cover_2 3 1 0 3 8 22 534 3
cert_coverFacet 4 774
cert_cover_2 4 1 0 7 8 262 774 3
cert_coverFacet 5 434
cert_cover_5 5 0 0 3 4 6 50 434 3
cert_coverFacet 6 786
cert_cover_2 6 3 0 7 8 274 786 3
cert_coverFacet 7 604
cert_cover_5 7 2 1 2 3 5 76 604 2
cert_coverFacet 8 752
cert_cover_5 8 3 3 4 5 6 112 752 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0186

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e10q1_0187.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0187

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 613, 325, 681, 913, 481, 94, 110, 278, 550, 666, 554, 786, 468, 248, 69, 261, 517, 97, 161, 545, 321, 385, 641, 769, 78, 22, 38, 262, 518, 26, 42, 522, 274, 530, 546, 770, 84, 276, 100, 548, 324, 88, 152, 104, 168, 552, 648, 208, 400, 656, 784, 224, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_613, vertices_325, vertices_681, vertices_913, vertices_481, vertices_94, vertices_110, vertices_278, vertices_550, vertices_666, vertices_554, vertices_786, vertices_468, vertices_248] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_97, vertices_161, vertices_545, vertices_321, vertices_385, vertices_641, vertices_769, vertices_78, vertices_22, vertices_38, vertices_262, vertices_518, vertices_26, vertices_42, vertices_522, vertices_274, vertices_530, vertices_546, vertices_770, vertices_84, vertices_276, vertices_100, vertices_548, vertices_324, vertices_88, vertices_152, vertices_104, vertices_168, vertices_552, vertices_648, vertices_208, vertices_400, vertices_656, vertices_784, vertices_224, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_613), (false, vertices_325), (false, vertices_681), (false, vertices_913), (false, vertices_481), (true, vertices_78), (true, vertices_22), (true, vertices_38), (true, vertices_26), (true, vertices_42), (true, vertices_522), (true, vertices_274), (true, vertices_530), (true, vertices_546), (true, vertices_84), (true, vertices_276), (true, vertices_88), (true, vertices_152), (true, vertices_104), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 16 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_325) then 0 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (false, vertices_913) then 23 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_88) then 11 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_104) then 13 else
  if p.val = (true, vertices_208) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 325 22 38 26 42 522 274 530 546 84 276 88 152 104 208 775 78 613 681 913 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 8 666 26 3
cert_row_2 1 0 1 2 5 78
cert_row_4 2 1 3 5 6 7 468 84 3
cert_row_4 3 2 3 4 5 6 248 88 2
cert_rows
cert_pivot_2 8 0 1 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 1 0 1 2 3 78 94 3
cert_coverFacet 1 110
cert_cover_5 1 1 0 1 2 4 78 110 3
cert_coverFacet 2 278
cert_cover_2 2 1 0 3 7 22 278 3
cert_coverFacet 3 550
cert_cover_2 3 1 0 4 8 38 550 3
cert_coverFacet 4 666
cert_cover_5 4 0 0 2 3 6 26 666 3
cert_coverFacet 5 554
cert_cover_2 5 2 0 4 8 42 554 3
cert_coverFacet 6 786
cert_cover_2 6 3 0 7 8 274 786 3
cert_coverFacet 7 468
cert_cover_5 7 2 1 3 5 6 84 468 3
cert_coverFacet 8 248
cert_cover_5 8 3 2 3 4 5 88 248 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0187

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e10q1_0188.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0188

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 789, 613, 453, 713, 401, 310, 566, 154, 282, 618, 298, 650, 364, 472, 69, 261, 517, 145, 273, 529, 193, 577, 385, 641, 54, 26, 42, 138, 266, 522, 146, 274, 530, 290, 546, 642, 276, 532, 100, 292, 548, 324, 152, 280, 104, 296, 200, 328, 584, 648, 400, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_789, vertices_613, vertices_453, vertices_713, vertices_401, vertices_310, vertices_566, vertices_154, vertices_282, vertices_618, vertices_298, vertices_650, vertices_364, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_145, vertices_273, vertices_529, vertices_193, vertices_577, vertices_385, vertices_641, vertices_54, vertices_26, vertices_42, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_290, vertices_546, vertices_642, vertices_276, vertices_532, vertices_100, vertices_292, vertices_548, vertices_324, vertices_152, vertices_280, vertices_104, vertices_296, vertices_200, vertices_328, vertices_584, vertices_648, vertices_400, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_789), (false, vertices_613), (false, vertices_453), (false, vertices_713), (false, vertices_401), (true, vertices_54), (true, vertices_26), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_290), (true, vertices_546), (true, vertices_292), (true, vertices_152), (true, vertices_280), (true, vertices_104), (true, vertices_296), (true, vertices_328)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 16 else
  if p.val = (false, vertices_789) then 19 else
  if p.val = (false, vertices_613) then 20 else
  if p.val = (false, vertices_453) then 21 else
  if p.val = (false, vertices_713) then 23 else
  if p.val = (false, vertices_401) then 0 else
  if p.val = (true, vertices_54) then 17 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_328) then 14 else
  0
cert_priority
cert_nodeAtPriority_51 401 26 42 138 266 522 274 290 546 292 152 280 104 296 328 659 54 789 613 453 713
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 5 8 618 42 3
cert_row_2 1 0 1 3 4 54
cert_row_4 2 1 2 4 5 7 364 100 1
cert_row_4 3 2 3 5 6 7 472 152 2
cert_rows
cert_pivot_2 8 0 1 2
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 1 0 1 3 7 54 310 3
cert_coverFacet 1 566
cert_cover_5 1 1 0 1 3 8 54 566 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 618
cert_cover_5 4 0 0 2 4 5 42 618 3
cert_coverFacet 5 298
cert_cover_2 5 2 0 4 7 42 298 3
cert_coverFacet 6 650
cert_cover_2 6 2 0 6 8 138 650 3
cert_coverFacet 7 364
cert_cover_5 7 2 1 2 4 5 100 364 1
cert_coverFacet 8 472
cert_cover_5 8 3 2 3 5 6 152 472 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0188

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e10q1_0189.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0189

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [339, 653, 269, 789, 217, 329, 689, 558, 358, 774, 242, 562, 786, 364, 744, 13, 261, 517, 73, 137, 265, 81, 145, 273, 529, 321, 641, 38, 262, 518, 50, 82, 274, 530, 98, 546, 322, 770, 44, 268, 524, 356, 772, 104, 552, 200, 328, 648, 176, 560, 208, 784, 224, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_653, vertices_269, vertices_789, vertices_217, vertices_329, vertices_689, vertices_558, vertices_358, vertices_774, vertices_242, vertices_562, vertices_786, vertices_364, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_261, vertices_517, vertices_73, vertices_137, vertices_265, vertices_81, vertices_145, vertices_273, vertices_529, vertices_321, vertices_641, vertices_38, vertices_262, vertices_518, vertices_50, vertices_82, vertices_274, vertices_530, vertices_98, vertices_546, vertices_322, vertices_770, vertices_44, vertices_268, vertices_524, vertices_356, vertices_772, vertices_104, vertices_552, vertices_200, vertices_328, vertices_648, vertices_176, vertices_560, vertices_208, vertices_784, vertices_224, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_653), (false, vertices_269), (false, vertices_789), (false, vertices_217), (false, vertices_329), (false, vertices_689), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_50), (true, vertices_530), (true, vertices_98), (true, vertices_546), (true, vertices_770), (true, vertices_44), (true, vertices_356), (true, vertices_104), (true, vertices_552), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 15 else
  if p.val = (false, vertices_653) then 17 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_789) then 18 else
  if p.val = (false, vertices_217) then 21 else
  if p.val = (false, vertices_329) then 1 else
  if p.val = (false, vertices_689) then 23 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_98) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_770) then 9 else
  if p.val = (true, vertices_44) then 10 else
  if p.val = (true, vertices_356) then 19 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_224) then 13 else
  0
cert_priority
cert_nodeAtPriority_54 269 329 38 262 518 50 530 98 546 770 44 104 552 224 339 653 789 356 217 689
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 5 7 356
cert_row_4 1 0 1 2 4 8 558 38 2
cert_row_4 2 0 3 4 5 6 242 50 3
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 7 1 0 2
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 1 0 1 2 4 38 558 2
cert_coverFacet 1 358
cert_cover_5 1 0 0 1 4 5 38 358 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 242
cert_cover_5 3 2 0 3 4 5 50 242 3
cert_coverFacet 4 562
cert_cover_2 4 3 0 4 8 50 562 3
cert_coverFacet 5 786
cert_cover_2 5 3 0 7 8 274 786 3
cert_coverFacet 6 364
cert_cover_5 6 0 1 2 4 5 44 364 3
cert_coverFacet 7 744
cert_cover_5 7 3 2 4 5 6 104 744 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0189

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m15e10q1_0190.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0190

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [539, 179, 643, 309, 533, 901, 481, 590, 218, 962, 60, 540, 108, 868, 248, 19, 131, 515, 21, 261, 517, 49, 529, 161, 289, 385, 641, 26, 74, 522, 146, 194, 578, 642, 28, 44, 76, 524, 52, 532, 100, 292, 580, 772, 56, 216, 536, 104, 176, 224, 352, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_539, vertices_179, vertices_643, vertices_309, vertices_533, vertices_901, vertices_481, vertices_590, vertices_218, vertices_962, vertices_60, vertices_540, vertices_108, vertices_868, vertices_248] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_515, vertices_21, vertices_261, vertices_517, vertices_49, vertices_529, vertices_161, vertices_289, vertices_385, vertices_641, vertices_26, vertices_74, vertices_522, vertices_146, vertices_194, vertices_578, vertices_642, vertices_28, vertices_44, vertices_76, vertices_524, vertices_52, vertices_532, vertices_100, vertices_292, vertices_580, vertices_772, vertices_56, vertices_216, vertices_536, vertices_104, vertices_176, vertices_224, vertices_352, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_539), (false, vertices_179), (false, vertices_643), (false, vertices_309), (false, vertices_533), (false, vertices_901), (false, vertices_481), (true, vertices_74), (true, vertices_194), (true, vertices_578), (true, vertices_28), (true, vertices_44), (true, vertices_76), (true, vertices_524), (true, vertices_100), (true, vertices_580), (true, vertices_56), (true, vertices_216), (true, vertices_104), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_539) then 15 else
  if p.val = (false, vertices_179) then 16 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_309) then 18 else
  if p.val = (false, vertices_533) then 1 else
  if p.val = (false, vertices_901) then 19 else
  if p.val = (false, vertices_481) then 24 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_216) then 21 else
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_832) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
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
cert_row_2 0 2 3 5 6 216
cert_row_4 1 0 1 2 5 8 590 74 1
cert_row_4 2 0 5 6 7 8 962 194 3
cert_row_4 3 1 4 5 7 8 868 100 3
cert_rows
cert_pivot_2 3 2 0 1
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 1 0 1 2 5 74 590 1
cert_coverFacet 1 218
cert_cover_5 1 0 0 2 3 5 26 218 3
cert_coverFacet 2 962
cert_cover_5 2 2 0 5 6 7 194 962 3
cert_coverFacet 3 60
cert_cover_2 3 2 1 3 4 28 60 3
cert_coverFacet 4 540
cert_cover_2 4 2 1 3 8 28 540 3
cert_coverFacet 5 108
cert_cover_2 5 2 1 4 5 44 108 3
cert_coverFacet 6 868
cert_cover_5 6 3 1 4 5 7 100 868 3
cert_coverFacet 7 248
cert_cover_5 7 0 2 3 4 5 56 248 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0190

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m15e10q1_0191.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0191

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [583, 391, 339, 661, 601, 433, 806, 362, 610, 932, 184, 312, 344, 664, 744, 7, 67, 259, 133, 517, 81, 145, 273, 529, 577, 385, 262, 518, 98, 290, 546, 322, 578, 804, 388, 644, 56, 88, 152, 280, 536, 104, 168, 296, 328, 584, 648, 176, 304, 336, 656, 608, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_583, vertices_391, vertices_339, vertices_661, vertices_601, vertices_433, vertices_806, vertices_362, vertices_610, vertices_932, vertices_184, vertices_312, vertices_344, vertices_664, vertices_744] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_67, vertices_259, vertices_133, vertices_517, vertices_81, vertices_145, vertices_273, vertices_529, vertices_577, vertices_385, vertices_262, vertices_518, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_804, vertices_388, vertices_644, vertices_56, vertices_88, vertices_152, vertices_280, vertices_536, vertices_104, vertices_168, vertices_296, vertices_328, vertices_584, vertices_648, vertices_176, vertices_304, vertices_336, vertices_656, vertices_608, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_583), (false, vertices_391), (false, vertices_339), (false, vertices_661), (false, vertices_601), (false, vertices_433), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_804), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_104), (true, vertices_168), (true, vertices_296), (true, vertices_328), (true, vertices_648), (true, vertices_608), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_583) then 14 else
  if p.val = (false, vertices_391) then 15 else
  if p.val = (false, vertices_339) then 16 else
  if p.val = (false, vertices_661) then 18 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (true, vertices_98) then 0 else
  if p.val = (true, vertices_290) then 1 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_804) then 19 else
  if p.val = (true, vertices_56) then 3 else
  if p.val = (true, vertices_152) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_608) then 11 else
  if p.val = (true, vertices_672) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_804), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
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
cert_row_2 0 1 4 7 8 804
cert_row_4 1 0 2 4 5 7 362 98 1
cert_row_4 2 2 4 5 6 8 744 104 3
cert_rows_3
cert_pivot_3 0 1 2
cert_heightProof 3
cert_coverFacet 0 806
cert_cover_5 0 0 0 1 4 7 262 806 2
cert_coverFacet 1 362
cert_cover_5 1 1 0 2 4 5 98 362 1
cert_coverFacet 2 610
cert_cover_2 2 4 0 5 8 98 610 3
cert_coverFacet 3 932
cert_cover_5 3 0 1 4 6 7 804 932 2
cert_coverFacet 4 184
cert_cover_2 4 3 2 4 6 56 184 3
cert_coverFacet 5 312
cert_cover_2 5 3 2 4 7 56 312 3
cert_coverFacet 6 344
cert_cover_2 6 3 2 5 7 88 344 3
cert_coverFacet 7 664
cert_cover_2 7 3 2 6 8 152 664 3
cert_coverFacet 8 744
cert_cover_5 8 2 2 4 5 6 104 744 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 3 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0191

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m15e10q1_0192.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0192

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 77, 525, 613, 217, 905, 849, 806, 426, 242, 626, 786, 236, 300, 780, 13, 69, 517, 73, 137, 521, 81, 145, 273, 577, 385, 769, 114, 146, 274, 530, 162, 290, 546, 386, 770, 44, 76, 268, 524, 100, 292, 548, 772, 168, 296, 200, 392, 776, 208, 592, 784, 224, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_77, vertices_525, vertices_613, vertices_217, vertices_905, vertices_849, vertices_806, vertices_426, vertices_242, vertices_626, vertices_786, vertices_236, vertices_300, vertices_780] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_517, vertices_73, vertices_137, vertices_521, vertices_81, vertices_145, vertices_273, vertices_577, vertices_385, vertices_769, vertices_114, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_770, vertices_44, vertices_76, vertices_268, vertices_524, vertices_100, vertices_292, vertices_548, vertices_772, vertices_168, vertices_296, vertices_200, vertices_392, vertices_776, vertices_208, vertices_592, vertices_784, vertices_224, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_77), (false, vertices_525), (false, vertices_613), (false, vertices_217), (false, vertices_905), (false, vertices_849), (true, vertices_114), (true, vertices_530), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_44), (true, vertices_268), (true, vertices_292), (true, vertices_772), (true, vertices_168), (true, vertices_296), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 15 else
  if p.val = (false, vertices_77) then 0 else
  if p.val = (false, vertices_525) then 1 else
  if p.val = (false, vertices_613) then 18 else
  if p.val = (false, vertices_217) then 20 else
  if p.val = (false, vertices_905) then 21 else
  if p.val = (false, vertices_849) then 23 else
  if p.val = (true, vertices_114) then 16 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_44) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_224) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_77), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_114), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
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
cert_row_2 0 0 3 4 5 114
cert_row_4 1 0 1 4 7 8 806 290 1
cert_row_4 2 0 2 4 6 7 426 162 1
cert_row_4 3 1 2 4 5 6 236 44 3
cert_rows
cert_pivot_2 3 8 0 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 1 0 1 4 7 290 806 1
cert_coverFacet 1 426
cert_cover_5 1 2 0 2 4 6 162 426 1
cert_coverFacet 2 242
cert_cover_5 2 0 0 3 4 6 114 242 3
cert_coverFacet 3 626
cert_cover_5 3 0 0 3 4 8 114 626 3
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 236
cert_cover_5 5 3 1 2 4 5 44 236 3
cert_coverFacet 6 300
cert_cover_2 6 2 1 4 7 44 300 3
cert_coverFacet 7 780
cert_cover_2 7 2 1 7 8 268 780 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0192

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m15e10q1_0193.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0193

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 805, 569, 89, 361, 721, 422, 710, 774, 346, 410, 210, 692, 184, 424, 25, 41, 73, 81, 529, 289, 545, 321, 577, 769, 134, 262, 518, 282, 82, 146, 194, 322, 578, 386, 770, 164, 292, 548, 644, 772, 56, 88, 152, 168, 296, 328, 392, 176, 560, 208, 656, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_805, vertices_569, vertices_89, vertices_361, vertices_721, vertices_422, vertices_710, vertices_774, vertices_346, vertices_410, vertices_210, vertices_692, vertices_184, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_73, vertices_81, vertices_529, vertices_289, vertices_545, vertices_321, vertices_577, vertices_769, vertices_134, vertices_262, vertices_518, vertices_282, vertices_82, vertices_146, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_164, vertices_292, vertices_548, vertices_644, vertices_772, vertices_56, vertices_88, vertices_152, vertices_168, vertices_296, vertices_328, vertices_392, vertices_176, vertices_560, vertices_208, vertices_656, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_805), (false, vertices_569), (false, vertices_89), (false, vertices_361), (false, vertices_721), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_282), (true, vertices_82), (true, vertices_146), (true, vertices_194), (true, vertices_386), (true, vertices_164), (true, vertices_644), (true, vertices_152), (true, vertices_168), (true, vertices_392), (true, vertices_176), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_569) then 21 else
  if p.val = (false, vertices_89) then 0 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_721) then 24 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_282) then 17 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 89 134 262 518 82 146 194 386 164 644 152 168 392 176 416 835 282 805 569 361 721
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 7 282
cert_row_4 1 0 1 4 6 7 422 134 2
cert_row_4 2 0 1 5 6 8 710 134 2
cert_row_4 3 1 3 4 6 8 692 164 1
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 1 0 1 4 6 134 422 2
cert_coverFacet 1 710
cert_cover_5 1 2 0 1 5 6 134 710 2
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 346
cert_cover_5 3 0 0 2 3 5 282 346 3
cert_coverFacet 4 410
cert_cover_5 4 0 0 2 3 6 282 410 3
cert_coverFacet 5 210
cert_cover_2 5 3 0 5 6 82 210 3
cert_coverFacet 6 692
cert_cover_5 6 3 1 3 4 6 164 692 1
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0193

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m15e10q1_0194.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0194

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 109, 205, 805, 569, 905, 198, 326, 666, 818, 210, 338, 898, 372, 248, 77, 37, 133, 261, 41, 137, 521, 545, 385, 769, 70, 134, 262, 82, 146, 274, 530, 194, 322, 386, 642, 770, 100, 292, 196, 324, 56, 152, 536, 104, 200, 648, 112, 304, 560, 208, 336, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_109, vertices_205, vertices_805, vertices_569, vertices_905, vertices_198, vertices_326, vertices_666, vertices_818, vertices_210, vertices_338, vertices_898, vertices_372, vertices_248] (by decide +kernel)
  polygons := literalFinset [vertices_77, vertices_37, vertices_133, vertices_261, vertices_41, vertices_137, vertices_521, vertices_545, vertices_385, vertices_769, vertices_70, vertices_134, vertices_262, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_386, vertices_642, vertices_770, vertices_100, vertices_292, vertices_196, vertices_324, vertices_56, vertices_152, vertices_536, vertices_104, vertices_200, vertices_648, vertices_112, vertices_304, vertices_560, vertices_208, vertices_336, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_109), (false, vertices_205), (false, vertices_805), (false, vertices_569), (false, vertices_905), (true, vertices_70), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_194), (true, vertices_322), (true, vertices_642), (true, vertices_770), (true, vertices_324), (true, vertices_152), (true, vertices_112), (true, vertices_304), (true, vertices_208), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 16 else
  if p.val = (false, vertices_109) then 18 else
  if p.val = (false, vertices_205) then 19 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (false, vertices_569) then 22 else
  if p.val = (false, vertices_905) then 23 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_336) then 14 else
  0
cert_priority
cert_nodeAtPriority_36 0 70 1 82 2 146 274 530 194 322 642 770 324 152 112 304 208 336 391 109 205 805 569 905
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 4 5 7 372 100 1
cert_row_4 1 0 3 4 7 8 818 274 2
cert_row_4 2 0 2 3 6 8 666 146 1
cert_row_4 3 2 3 4 5 6 248 56 3
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 198
cert_cover_2 0 1 0 5 6 70 198 3
cert_coverFacet 1 326
cert_cover_2 1 1 0 5 7 70 326 3
cert_coverFacet 2 666
cert_cover_5 2 2 0 2 3 6 146 666 1
cert_coverFacet 3 818
cert_cover_5 3 1 0 3 4 7 274 818 2
cert_coverFacet 4 210
cert_cover_2 4 3 0 5 6 82 210 3
cert_coverFacet 5 338
cert_cover_2 5 3 0 5 7 82 338 3
cert_coverFacet 6 898
cert_cover_2 6 6 0 7 8 386 898 3
cert_coverFacet 7 372
cert_cover_5 7 0 1 3 4 5 100 372 1
cert_coverFacet 8 248
cert_cover_5 8 3 2 3 4 5 56 248 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0194

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m15e10q1_0195.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0195

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [179, 93, 157, 677, 837, 625, 902, 314, 154, 394, 866, 674, 460, 344, 368, 29, 69, 133, 517, 49, 81, 145, 161, 545, 577, 26, 138, 266, 50, 146, 162, 290, 546, 386, 642, 770, 76, 140, 324, 388, 644, 772, 88, 152, 280, 328, 392, 112, 304, 336, 352, 608, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_179, vertices_93, vertices_157, vertices_677, vertices_837, vertices_625, vertices_902, vertices_314, vertices_154, vertices_394, vertices_866, vertices_674, vertices_460, vertices_344, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_29, vertices_69, vertices_133, vertices_517, vertices_49, vertices_81, vertices_145, vertices_161, vertices_545, vertices_577, vertices_26, vertices_138, vertices_266, vertices_50, vertices_146, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_76, vertices_140, vertices_324, vertices_388, vertices_644, vertices_772, vertices_88, vertices_152, vertices_280, vertices_328, vertices_392, vertices_112, vertices_304, vertices_336, vertices_352, vertices_608, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_179), (false, vertices_93), (false, vertices_157), (false, vertices_677), (false, vertices_837), (false, vertices_625), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_290), (true, vertices_546), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_388), (true, vertices_280), (true, vertices_328), (true, vertices_392), (true, vertices_304), (true, vertices_336), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 20 17 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_179) then 16 else
  if p.val = (false, vertices_93) then 18 else
  if p.val = (false, vertices_157) then 19 else
  if p.val = (false, vertices_677) then 21 else
  if p.val = (false, vertices_837) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_352) then 14 else
  0
cert_priority
cert_nodeAtPriority_52 26 2 138 1 266 290 546 386 642 770 388 280 328 392 304 336 352 179 93 157 677 837 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 7 314 26 3
cert_row_4 1 0 4 5 7 8 866 290 2
cert_row_4 2 0 1 6 7 8 902 386 1
cert_row_4 3 1 2 5 6 7 460 76 3
cert_rows
cert_pivot_2 3 4 0 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 2 0 1 6 7 386 902 1
cert_coverFacet 1 314
cert_cover_5 1 0 0 2 3 4 26 314 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 866
cert_cover_5 4 1 0 4 5 7 290 866 2
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 460
cert_cover_5 6 3 1 2 5 6 76 460 3
cert_coverFacet 7 344
cert_cover_2 7 3 2 5 7 88 344 3
cert_coverFacet 8 368
cert_cover_2 8 4 3 5 7 112 368 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0195

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m15e10q1_0196.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0196

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 213, 405, 613, 121, 817, 390, 646, 314, 218, 650, 778, 402, 716, 872, 149, 69, 261, 517, 49, 81, 273, 97, 545, 769, 134, 262, 518, 26, 138, 266, 522, 146, 274, 386, 642, 770, 196, 580, 388, 644, 56, 88, 104, 296, 200, 584, 648, 776, 304, 208, 400, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_213, vertices_405, vertices_613, vertices_121, vertices_817, vertices_390, vertices_646, vertices_314, vertices_218, vertices_650, vertices_778, vertices_402, vertices_716, vertices_872] (by decide +kernel)
  polygons := literalFinset [vertices_149, vertices_69, vertices_261, vertices_517, vertices_49, vertices_81, vertices_273, vertices_97, vertices_545, vertices_769, vertices_134, vertices_262, vertices_518, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_386, vertices_642, vertices_770, vertices_196, vertices_580, vertices_388, vertices_644, vertices_56, vertices_88, vertices_104, vertices_296, vertices_200, vertices_584, vertices_648, vertices_776, vertices_304, vertices_208, vertices_400, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_213), (false, vertices_405), (false, vertices_613), (false, vertices_121), (false, vertices_817), (true, vertices_134), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_274), (true, vertices_386), (true, vertices_642), (true, vertices_644), (true, vertices_296), (true, vertices_200), (true, vertices_584), (true, vertices_648), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 16 else
  if p.val = (false, vertices_213) then 18 else
  if p.val = (false, vertices_405) then 19 else
  if p.val = (false, vertices_613) then 20 else
  if p.val = (false, vertices_121) then 22 else
  if p.val = (false, vertices_817) then 24 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_642) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_648) then 13 else
  if p.val = (true, vertices_776) then 14 else
  0
cert_priority
cert_nodeAtPriority_68 0 134 1 26 138 266 522 146 274 386 642 644 296 200 584 648 776 775 213 405 613 121 817
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 5 6 8 716 196 1
cert_row_4 1 0 2 3 5 6 218 26 3
cert_row_4 2 0 2 3 4 7 314 26 3
cert_row_4 3 2 4 5 7 8 872 104 3
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 390
cert_cover_2 0 1 0 6 7 134 390 3
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 314
cert_cover_5 2 2 0 2 3 4 26 314 3
cert_coverFacet 3 218
cert_cover_5 3 1 0 2 3 5 26 218 3
cert_coverFacet 4 650
cert_cover_2 4 2 0 6 8 138 650 3
cert_coverFacet 5 778
cert_cover_2 5 2 0 7 8 266 778 3
cert_coverFacet 6 402
cert_cover_2 6 3 0 6 7 146 402 3
cert_coverFacet 7 716
cert_cover_5 7 0 1 2 5 6 196 716 1
cert_coverFacet 8 872
cert_cover_5 8 3 2 4 5 7 104 872 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0196

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e10q1_0197.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0197

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 109, 333, 185, 465, 737, 542, 270, 614, 326, 786, 962, 556, 568, 944, 77, 25, 41, 265, 145, 273, 97, 161, 193, 321, 14, 70, 262, 518, 26, 266, 274, 530, 322, 578, 770, 44, 268, 524, 100, 548, 324, 56, 536, 552, 176, 560, 400, 784, 608, 672, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_109, vertices_333, vertices_185, vertices_465, vertices_737, vertices_542, vertices_270, vertices_614, vertices_326, vertices_786, vertices_962, vertices_556, vertices_568, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_77, vertices_25, vertices_41, vertices_265, vertices_145, vertices_273, vertices_97, vertices_161, vertices_193, vertices_321, vertices_14, vertices_70, vertices_262, vertices_518, vertices_26, vertices_266, vertices_274, vertices_530, vertices_322, vertices_578, vertices_770, vertices_44, vertices_268, vertices_524, vertices_100, vertices_548, vertices_324, vertices_56, vertices_536, vertices_552, vertices_176, vertices_560, vertices_400, vertices_784, vertices_608, vertices_672, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_109), (false, vertices_333), (false, vertices_185), (false, vertices_465), (false, vertices_737), (true, vertices_14), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_530), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_524), (true, vertices_548), (true, vertices_536), (true, vertices_552), (true, vertices_560), (true, vertices_784), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 16 else
  if p.val = (false, vertices_109) then 18 else
  if p.val = (false, vertices_333) then 19 else
  if p.val = (false, vertices_185) then 21 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_784) then 13 else
  if p.val = (true, vertices_896) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 8 542 14 3
cert_row_4 1 0 1 4 5 8 614 70 2
cert_row_4 2 0 5 6 7 8 962 322 2
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 2 1 0 3
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 14 542 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 614
cert_cover_5 2 1 0 1 4 5 70 614 2
cert_coverFacet 3 326
cert_cover_2 3 1 0 5 7 70 326 3
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 962
cert_cover_5 5 2 0 5 6 7 322 962 2
cert_coverFacet 6 556
cert_cover_2 6 2 1 4 8 44 556 3
cert_coverFacet 7 568
cert_cover_2 7 3 2 4 8 56 568 3
cert_coverFacet 8 944
cert_cover_5 8 3 3 4 6 7 176 944 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0197

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e10q1_0198.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0198

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 275, 803, 613, 425, 241, 401, 782, 410, 666, 236, 300, 652, 724, 804, 19, 259, 515, 81, 145, 273, 97, 161, 289, 545, 577, 385, 154, 266, 522, 274, 530, 770, 44, 140, 268, 524, 100, 292, 548, 196, 580, 644, 772, 168, 296, 392, 648, 208, 592, 400, 656, 224, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_275, vertices_803, vertices_613, vertices_425, vertices_241, vertices_401, vertices_782, vertices_410, vertices_666, vertices_236, vertices_300, vertices_652, vertices_724, vertices_804] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_259, vertices_515, vertices_81, vertices_145, vertices_273, vertices_97, vertices_161, vertices_289, vertices_545, vertices_577, vertices_385, vertices_154, vertices_266, vertices_522, vertices_274, vertices_530, vertices_770, vertices_44, vertices_140, vertices_268, vertices_524, vertices_100, vertices_292, vertices_548, vertices_196, vertices_580, vertices_644, vertices_772, vertices_168, vertices_296, vertices_392, vertices_648, vertices_208, vertices_592, vertices_400, vertices_656, vertices_224, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_275), (false, vertices_803), (false, vertices_613), (false, vertices_425), (false, vertices_241), (false, vertices_401), (true, vertices_154), (true, vertices_266), (true, vertices_522), (true, vertices_44), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_292), (true, vertices_196), (true, vertices_644), (true, vertices_772), (true, vertices_648), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 15 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (false, vertices_401) then 1 else
  if p.val = (true, vertices_154) then 17 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_656) then 13 else
  0
cert_priority
cert_nodeAtPriority_23 275 401 266 522 44 140 268 524 292 196 644 772 648 656 595 803 154 613 425 241
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 266 1
cert_row_2 1 0 2 3 6 154
cert_row_4 2 1 2 4 5 6 236 44 3
cert_row_4 3 1 3 5 6 8 724 196 1
cert_rows
cert_pivot_2 7 0 2 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 266 782 1
cert_coverFacet 1 410
cert_cover_5 1 1 0 2 3 7 154 410 3
cert_coverFacet 2 666
cert_cover_5 2 1 0 2 3 8 154 666 3
cert_coverFacet 3 236
cert_cover_5 3 2 1 2 4 5 44 236 3
cert_coverFacet 4 300
cert_cover_2 4 2 1 4 7 44 300 3
cert_coverFacet 5 652
cert_cover_2 5 2 1 6 8 140 652 3
cert_coverFacet 6 724
cert_cover_5 6 3 1 3 5 6 196 724 1
cert_coverFacet 7 804
cert_cover_2 7 4 1 7 8 292 804 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0198

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e10q1_0199.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0199

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 147, 707, 613, 457, 369, 401, 782, 790, 410, 650, 364, 716, 308, 564, 19, 131, 515, 49, 145, 273, 97, 545, 193, 321, 577, 385, 774, 138, 266, 522, 146, 274, 530, 642, 76, 268, 524, 52, 276, 532, 100, 292, 548, 580, 200, 328, 392, 648, 304, 560, 400, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_147, vertices_707, vertices_613, vertices_457, vertices_369, vertices_401, vertices_782, vertices_790, vertices_410, vertices_650, vertices_364, vertices_716, vertices_308, vertices_564] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_515, vertices_49, vertices_145, vertices_273, vertices_97, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_774, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_642, vertices_76, vertices_268, vertices_524, vertices_52, vertices_276, vertices_532, vertices_100, vertices_292, vertices_548, vertices_580, vertices_200, vertices_328, vertices_392, vertices_648, vertices_304, vertices_560, vertices_400, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_147), (false, vertices_707), (false, vertices_613), (false, vertices_457), (false, vertices_369), (false, vertices_401), (true, vertices_774), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_52), (true, vertices_276), (true, vertices_532), (true, vertices_292), (true, vertices_648)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 14 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 18 else
  if p.val = (false, vertices_147) then 0 else
  if p.val = (false, vertices_707) then 19 else
  if p.val = (false, vertices_613) then 15 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_369) then 23 else
  if p.val = (false, vertices_401) then 1 else
  if p.val = (true, vertices_774) then 16 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_292) then 12 else
  if p.val = (true, vertices_648) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 1 147 0 401 138 266 522 274 76 268 524 52 276 532 292 648 613 774 563 707 457 369
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 7 410 138 2
cert_row_2 1 0 1 7 8 774
cert_row_4 2 1 2 4 5 7 364 76 2
cert_row_4 3 1 2 5 6 8 716 76 3
cert_rows
cert_pivot_2 3 0 4 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 1 0 1 2 7 774 782 2
cert_coverFacet 1 790
cert_cover_5 1 1 0 1 3 7 774 790 2
cert_coverFacet 2 410
cert_cover_5 2 0 0 2 3 6 138 410 2
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 364
cert_cover_5 4 2 1 2 4 5 76 364 2
cert_coverFacet 5 716
cert_cover_5 5 3 1 2 5 6 76 716 3
cert_coverFacet 6 308
cert_cover_2 6 3 1 4 7 52 308 3
cert_coverFacet 7 564
cert_cover_2 7 3 1 4 8 52 564 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0199

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e10q1_0200.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0200

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 565, 149, 357, 389, 617, 721, 406, 282, 538, 362, 714, 658, 796, 812, 21, 37, 133, 261, 145, 529, 97, 545, 193, 321, 577, 385, 26, 74, 266, 522, 146, 274, 530, 194, 322, 386, 642, 780, 148, 276, 532, 292, 548, 388, 280, 536, 104, 296, 552, 584, 656, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_565, vertices_149, vertices_357, vertices_389, vertices_617, vertices_721, vertices_406, vertices_282, vertices_538, vertices_362, vertices_714, vertices_658, vertices_796, vertices_812] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_133, vertices_261, vertices_145, vertices_529, vertices_97, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_26, vertices_74, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_386, vertices_642, vertices_780, vertices_148, vertices_276, vertices_532, vertices_292, vertices_548, vertices_388, vertices_280, vertices_536, vertices_104, vertices_296, vertices_552, vertices_584, vertices_656, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_565), (false, vertices_149), (false, vertices_357), (false, vertices_389), (false, vertices_617), (false, vertices_721), (true, vertices_26), (true, vertices_74), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_642), (true, vertices_780), (true, vertices_276), (true, vertices_280), (true, vertices_536), (true, vertices_296)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 15 else
  if p.val = (false, vertices_565) then 17 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_357) then 18 else
  if p.val = (false, vertices_389) then 1 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_274) then 7 else
  if p.val = (true, vertices_530) then 8 else
  if p.val = (true, vertices_642) then 9 else
  if p.val = (true, vertices_780) then 19 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_296) then 13 else
  0
cert_priority
cert_nodeAtPriority_54 149 389 26 74 266 522 146 274 530 642 276 280 536 296 451 565 357 780 617 721
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 7 406 146 1
cert_row_2 1 1 2 7 8 780
cert_row_4 2 0 2 4 5 7 362 74 2
cert_row_4 3 0 2 5 6 8 714 74 3
cert_rows
cert_pivot_2 3 1 4 0
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 0 0 1 3 6 146 406 1
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 362
cert_cover_5 3 2 0 2 4 5 74 362 2
cert_coverFacet 4 714
cert_cover_5 4 3 0 2 5 6 74 714 3
cert_coverFacet 5 658
cert_cover_2 5 3 0 6 8 146 658 3
cert_coverFacet 6 796
cert_cover_5 6 1 1 2 3 7 780 796 2
cert_coverFacet 7 812
cert_cover_5 7 1 1 2 4 7 780 812 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0200

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e10q1_0201.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0201

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [539, 285, 397, 213, 233, 553, 625, 790, 282, 426, 554, 866, 596, 484, 836, 269, 21, 133, 25, 41, 137, 521, 81, 529, 97, 545, 193, 26, 42, 266, 522, 274, 530, 290, 546, 770, 84, 276, 532, 196, 324, 580, 388, 772, 280, 168, 552, 392, 592, 224, 352, 608, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_539, vertices_285, vertices_397, vertices_213, vertices_233, vertices_553, vertices_625, vertices_790, vertices_282, vertices_426, vertices_554, vertices_866, vertices_596, vertices_484, vertices_836] (by decide +kernel)
  polygons := literalFinset [vertices_269, vertices_21, vertices_133, vertices_25, vertices_41, vertices_137, vertices_521, vertices_81, vertices_529, vertices_97, vertices_545, vertices_193, vertices_26, vertices_42, vertices_266, vertices_522, vertices_274, vertices_530, vertices_290, vertices_546, vertices_770, vertices_84, vertices_276, vertices_532, vertices_196, vertices_324, vertices_580, vertices_388, vertices_772, vertices_280, vertices_168, vertices_552, vertices_392, vertices_592, vertices_224, vertices_352, vertices_608, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_539), (false, vertices_285), (false, vertices_397), (false, vertices_213), (false, vertices_233), (false, vertices_553), (false, vertices_625), (true, vertices_42), (true, vertices_266), (true, vertices_274), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_532), (true, vertices_324), (true, vertices_580), (true, vertices_772), (true, vertices_352), (true, vertices_416), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_539) then 15 else
  if p.val = (false, vertices_285) then 17 else
  if p.val = (false, vertices_397) then 18 else
  if p.val = (false, vertices_213) then 19 else
  if p.val = (false, vertices_233) then 21 else
  if p.val = (false, vertices_553) then 0 else
  if p.val = (false, vertices_625) then 23 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_416) then 12 else
  if p.val = (true, vertices_832) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_553), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
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
cert_row_4 0 0 1 3 7 8 790 274 1
cert_row_4 1 0 2 4 6 7 426 42 3
cert_row_4 2 0 4 5 7 8 866 290 2
cert_row_4 3 1 4 5 6 7 484 196 1
cert_rows
cert_pivot_2 3 2 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 426
cert_cover_5 2 1 0 2 4 6 42 426 3
cert_coverFacet 3 554
cert_cover_2 3 2 0 4 8 42 554 3
cert_coverFacet 4 866
cert_cover_5 4 2 0 4 5 7 290 866 2
cert_coverFacet 5 596
cert_cover_2 5 3 1 5 8 84 596 3
cert_coverFacet 6 484
cert_cover_5 6 3 1 4 5 6 196 484 1
cert_coverFacet 7 836
cert_cover_2 7 5 1 7 8 324 836 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0201

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m15e10q1_0202.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0202

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 267, 899, 421, 233, 297, 721, 62, 302, 534, 774, 538, 244, 916, 632, 11, 259, 515, 41, 73, 265, 161, 289, 193, 577, 385, 641, 46, 22, 262, 518, 26, 266, 522, 530, 770, 52, 148, 532, 164, 292, 388, 772, 56, 536, 104, 296, 584, 112, 208, 592, 656, 224, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_267, vertices_899, vertices_421, vertices_233, vertices_297, vertices_721, vertices_62, vertices_302, vertices_534, vertices_774, vertices_538, vertices_244, vertices_916, vertices_632] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_259, vertices_515, vertices_41, vertices_73, vertices_265, vertices_161, vertices_289, vertices_193, vertices_577, vertices_385, vertices_641, vertices_46, vertices_22, vertices_262, vertices_518, vertices_26, vertices_266, vertices_522, vertices_530, vertices_770, vertices_52, vertices_148, vertices_532, vertices_164, vertices_292, vertices_388, vertices_772, vertices_56, vertices_536, vertices_104, vertices_296, vertices_584, vertices_112, vertices_208, vertices_592, vertices_656, vertices_224, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_267), (false, vertices_899), (false, vertices_421), (false, vertices_233), (false, vertices_297), (false, vertices_721), (true, vertices_46), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_530), (true, vertices_52), (true, vertices_148), (true, vertices_532), (true, vertices_772), (true, vertices_56), (true, vertices_536), (true, vertices_112)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 15 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_899) then 16 else
  if p.val = (false, vertices_421) then 19 else
  if p.val = (false, vertices_233) then 21 else
  if p.val = (false, vertices_297) then 1 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (true, vertices_46) then 17 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_26) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_112) then 13 else
  0
cert_priority
cert_nodeAtPriority_23 267 297 22 262 518 26 530 52 148 532 772 56 536 112 587 899 46 421 233 721
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 4 46
cert_row_4 1 1 3 6 7 8 916 148 3
cert_row_4 2 1 3 4 5 6 244 52 3
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 0 0 1 2 3 46 62 3
cert_coverFacet 1 302
cert_cover_5 1 0 0 1 2 7 46 302 3
cert_coverFacet 2 534
cert_cover_2 2 1 0 3 8 22 534 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 538
cert_cover_2 4 2 0 3 8 26 538 3
cert_coverFacet 5 244
cert_cover_5 5 2 1 3 4 5 52 244 3
cert_coverFacet 6 916
cert_cover_5 6 1 1 3 6 7 148 916 3
cert_coverFacet 7 632
cert_cover_5 7 3 2 3 4 5 56 632 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0202

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m15e10q1_0203.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0203

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 157, 269, 565, 457, 433, 801, 334, 590, 626, 482, 802, 540, 248, 600, 13, 21, 261, 517, 137, 265, 49, 145, 289, 545, 385, 769, 78, 262, 518, 98, 290, 546, 322, 578, 770, 28, 268, 524, 532, 88, 152, 536, 200, 328, 584, 112, 176, 560, 592, 224, 416, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_157, vertices_269, vertices_565, vertices_457, vertices_433, vertices_801, vertices_334, vertices_590, vertices_626, vertices_482, vertices_802, vertices_540, vertices_248, vertices_600] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_261, vertices_517, vertices_137, vertices_265, vertices_49, vertices_145, vertices_289, vertices_545, vertices_385, vertices_769, vertices_78, vertices_262, vertices_518, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_28, vertices_268, vertices_524, vertices_532, vertices_88, vertices_152, vertices_536, vertices_200, vertices_328, vertices_584, vertices_112, vertices_176, vertices_560, vertices_592, vertices_224, vertices_416, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_157), (false, vertices_269), (false, vertices_565), (false, vertices_457), (false, vertices_433), (false, vertices_801), (true, vertices_78), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_322), (true, vertices_578), (true, vertices_524), (true, vertices_88), (true, vertices_536), (true, vertices_584), (true, vertices_112), (true, vertices_592), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 15 else
  if p.val = (false, vertices_157) then 18 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_565) then 19 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (false, vertices_801) then 1 else
  if p.val = (true, vertices_78) then 16 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_224) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 0 269 1 801 98 290 546 322 578 524 88 536 584 112 592 224 775 78 157 565 457 433
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 3 4 5 8 626 98 1
cert_row_4 2 0 4 5 6 7 482 98 3
cert_row_4 3 2 3 4 5 6 248 88 2
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 7 78 334 3
cert_coverFacet 1 590
cert_cover_5 1 0 0 1 2 8 78 590 3
cert_coverFacet 2 626
cert_cover_5 2 1 0 3 4 5 98 626 1
cert_coverFacet 3 482
cert_cover_5 3 2 0 4 5 6 98 482 3
cert_coverFacet 4 802
cert_cover_2 4 4 0 7 8 290 802 3
cert_coverFacet 5 540
cert_cover_2 5 2 1 3 8 28 540 3
cert_coverFacet 6 248
cert_cover_5 6 3 2 3 4 5 88 248 2
cert_coverFacet 7 600
cert_cover_2 7 3 2 5 8 88 600 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0203

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m15e10q1_0204.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0204

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [155, 299, 339, 357, 233, 721, 654, 782, 658, 786, 396, 852, 740, 420, 424, 11, 19, 259, 41, 137, 81, 145, 97, 289, 193, 321, 526, 138, 266, 146, 274, 530, 642, 770, 140, 268, 100, 164, 292, 324, 580, 388, 644, 772, 168, 296, 392, 336, 592, 656, 784, 224, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_155, vertices_299, vertices_339, vertices_357, vertices_233, vertices_721, vertices_654, vertices_782, vertices_658, vertices_786, vertices_396, vertices_852, vertices_740, vertices_420, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_259, vertices_41, vertices_137, vertices_81, vertices_145, vertices_97, vertices_289, vertices_193, vertices_321, vertices_526, vertices_138, vertices_266, vertices_146, vertices_274, vertices_530, vertices_642, vertices_770, vertices_140, vertices_268, vertices_100, vertices_164, vertices_292, vertices_324, vertices_580, vertices_388, vertices_644, vertices_772, vertices_168, vertices_296, vertices_392, vertices_336, vertices_592, vertices_656, vertices_784, vertices_224, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_155), (false, vertices_299), (false, vertices_339), (false, vertices_357), (false, vertices_233), (false, vertices_721), (true, vertices_526), (true, vertices_530), (true, vertices_642), (true, vertices_770), (true, vertices_140), (true, vertices_268), (true, vertices_164), (true, vertices_580), (true, vertices_388), (true, vertices_644), (true, vertices_772), (true, vertices_392), (true, vertices_784), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 13 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_155) then 17 else
  if p.val = (false, vertices_299) then 18 else
  if p.val = (false, vertices_339) then 19 else
  if p.val = (false, vertices_357) then 14 else
  if p.val = (false, vertices_233) then 21 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (true, vertices_526) then 15 else
  if p.val = (true, vertices_530) then 0 else
  if p.val = (true, vertices_642) then 1 else
  if p.val = (true, vertices_770) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_580) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_416) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_526), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_155), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
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
cert_row_2 0 0 1 2 8 526
cert_row_4 1 1 3 5 7 8 852 324 1
cert_row_4 2 1 4 5 6 8 740 100 3
cert_rows_3
cert_pivot_3 3 0 1
cert_heightProof 3
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 526 654 3
cert_coverFacet 1 782
cert_cover_5 1 0 0 1 2 7 526 782 3
cert_coverFacet 2 658
cert_cover_2 2 3 0 6 8 146 658 3
cert_coverFacet 3 786
cert_cover_2 3 3 0 7 8 274 786 3
cert_coverFacet 4 396
cert_cover_2 4 2 1 6 7 140 396 3
cert_coverFacet 5 852
cert_cover_5 5 1 1 3 5 7 324 852 1
cert_coverFacet 6 740
cert_cover_5 6 2 1 4 5 6 100 740 3
cert_coverFacet 7 420
cert_cover_2 7 4 1 6 7 164 420 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 3 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0204

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m15e10q1_0205.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0205

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [271, 527, 357, 709, 809, 625, 390, 646, 570, 154, 394, 722, 468, 376, 408, 15, 69, 261, 517, 265, 521, 97, 289, 545, 577, 134, 262, 518, 26, 138, 266, 522, 146, 530, 386, 642, 196, 324, 388, 644, 56, 152, 280, 296, 552, 392, 112, 560, 208, 336, 592, 400, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_271, vertices_527, vertices_357, vertices_709, vertices_809, vertices_625, vertices_390, vertices_646, vertices_570, vertices_154, vertices_394, vertices_722, vertices_468, vertices_376, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_15, vertices_69, vertices_261, vertices_517, vertices_265, vertices_521, vertices_97, vertices_289, vertices_545, vertices_577, vertices_134, vertices_262, vertices_518, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_530, vertices_386, vertices_642, vertices_196, vertices_324, vertices_388, vertices_644, vertices_56, vertices_152, vertices_280, vertices_296, vertices_552, vertices_392, vertices_112, vertices_560, vertices_208, vertices_336, vertices_592, vertices_400, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_271), (false, vertices_527), (false, vertices_357), (false, vertices_709), (false, vertices_809), (false, vertices_625), (true, vertices_134), (true, vertices_26), (true, vertices_138), (true, vertices_146), (true, vertices_530), (true, vertices_386), (true, vertices_642), (true, vertices_388), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_392), (true, vertices_208), (true, vertices_336), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_271) then 16 else
  if p.val = (false, vertices_527) then 17 else
  if p.val = (false, vertices_357) then 19 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_809) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
cert_nodeAtPriority_62 134 26 138 146 530 386 642 388 56 152 280 392 208 336 400 271 527 357 709 809 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 5 6 7 468 196 1
cert_row_4 1 0 3 5 6 8 722 146 2
cert_row_4 2 0 2 3 4 8 570 26 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 390
cert_cover_2 0 1 0 6 7 134 390 3
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 570
cert_cover_5 2 2 0 2 3 4 26 570 3
cert_coverFacet 3 154
cert_cover_2 3 2 0 3 6 26 154 3
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 722
cert_cover_5 5 1 0 3 5 6 146 722 2
cert_coverFacet 6 468
cert_cover_5 6 0 1 3 5 6 196 468 1
cert_coverFacet 7 376
cert_cover_5 7 3 2 3 4 5 56 376 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0205

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m15e10q1_0206.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0206

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [271, 527, 339, 707, 901, 481, 282, 538, 626, 572, 172, 396, 740, 376, 424, 15, 67, 259, 515, 261, 517, 193, 321, 385, 641, 26, 266, 522, 82, 274, 530, 578, 44, 140, 268, 524, 164, 548, 388, 644, 56, 280, 536, 168, 296, 392, 112, 560, 336, 224, 352, 608, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_271, vertices_527, vertices_339, vertices_707, vertices_901, vertices_481, vertices_282, vertices_538, vertices_626, vertices_572, vertices_172, vertices_396, vertices_740, vertices_376, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_15, vertices_67, vertices_259, vertices_515, vertices_261, vertices_517, vertices_193, vertices_321, vertices_385, vertices_641, vertices_26, vertices_266, vertices_522, vertices_82, vertices_274, vertices_530, vertices_578, vertices_44, vertices_140, vertices_268, vertices_524, vertices_164, vertices_548, vertices_388, vertices_644, vertices_56, vertices_280, vertices_536, vertices_168, vertices_296, vertices_392, vertices_112, vertices_560, vertices_336, vertices_224, vertices_352, vertices_608, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_271), (false, vertices_527), (false, vertices_339), (false, vertices_707), (false, vertices_901), (false, vertices_481), (true, vertices_26), (true, vertices_530), (true, vertices_44), (true, vertices_140), (true, vertices_164), (true, vertices_548), (true, vertices_56), (true, vertices_280), (true, vertices_536), (true, vertices_168), (true, vertices_296), (true, vertices_392), (true, vertices_112), (true, vertices_560), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 15 22 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_271) then 16 else
  if p.val = (false, vertices_527) then 17 else
  if p.val = (false, vertices_339) then 20 else
  if p.val = (false, vertices_707) then 21 else
  if p.val = (false, vertices_901) then 18 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_44) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_56) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_608) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_271), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 22 => Sum.inl 2
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
cert_row_4 0 0 3 4 5 8 626 82 2
cert_row_4 1 1 4 5 6 8 740 164 2
cert_row_4 2 1 2 3 4 8 572 44 2
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 282
cert_cover_2 0 2 0 3 7 26 282 3
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 626
cert_cover_5 2 0 0 3 4 5 82 626 2
cert_coverFacet 3 572
cert_cover_5 3 2 1 2 3 4 44 572 2
cert_coverFacet 4 172
cert_cover_2 4 2 1 4 6 44 172 3
cert_coverFacet 5 396
cert_cover_2 5 2 1 6 7 140 396 3
cert_coverFacet 6 740
cert_cover_5 6 1 1 4 5 6 164 740 2
cert_coverFacet 7 376
cert_cover_5 7 3 2 3 4 5 56 376 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0206

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m15e10q1_0207.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0207

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [143, 527, 789, 421, 681, 865, 150, 534, 218, 618, 850, 468, 360, 424, 456, 15, 133, 261, 517, 137, 521, 161, 289, 545, 769, 22, 134, 518, 74, 138, 522, 82, 146, 530, 578, 148, 276, 532, 388, 104, 168, 296, 552, 200, 328, 392, 208, 336, 784, 352, 608, 416, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_143, vertices_527, vertices_789, vertices_421, vertices_681, vertices_865, vertices_150, vertices_534, vertices_218, vertices_618, vertices_850, vertices_468, vertices_360, vertices_424, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_15, vertices_133, vertices_261, vertices_517, vertices_137, vertices_521, vertices_161, vertices_289, vertices_545, vertices_769, vertices_22, vertices_134, vertices_518, vertices_74, vertices_138, vertices_522, vertices_82, vertices_146, vertices_530, vertices_578, vertices_148, vertices_276, vertices_532, vertices_388, vertices_104, vertices_168, vertices_296, vertices_552, vertices_200, vertices_328, vertices_392, vertices_208, vertices_336, vertices_784, vertices_352, vertices_608, vertices_416, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_143), (false, vertices_527), (false, vertices_789), (false, vertices_421), (false, vertices_681), (false, vertices_865), (true, vertices_22), (true, vertices_74), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_578), (true, vertices_148), (true, vertices_104), (true, vertices_296), (true, vertices_200), (true, vertices_328), (true, vertices_392), (true, vertices_208), (true, vertices_336), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_143) then 16 else
  if p.val = (false, vertices_527) then 17 else
  if p.val = (false, vertices_789) then 19 else
  if p.val = (false, vertices_421) then 20 else
  if p.val = (false, vertices_681) then 22 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_104) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_143), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
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
cert_row_4 0 0 2 4 5 8 618 74 2
cert_row_4 1 0 2 3 5 6 218 74 2
cert_row_4 2 0 3 5 7 8 850 82 3
cert_row_4 3 1 3 5 6 7 468 148 2
cert_rows
cert_pivot_2 4 2 0 1
cert_heightProof 4
cert_coverFacet 0 150
cert_cover_2 0 1 0 3 6 22 150 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 218
cert_cover_5 2 1 0 2 3 5 74 218 2
cert_coverFacet 3 618
cert_cover_5 3 0 0 2 4 5 74 618 2
cert_coverFacet 4 850
cert_cover_5 4 2 0 3 5 7 82 850 3
cert_coverFacet 5 468
cert_cover_5 5 3 1 3 5 6 148 468 2
cert_coverFacet 6 360
cert_cover_2 6 4 2 5 7 104 360 3
cert_coverFacet 7 424
cert_cover_2 7 4 2 6 7 168 424 3
cert_coverFacet 8 456
cert_cover_2 8 5 2 6 7 200 456 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0207

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e10q1_0208.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0208

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [143, 527, 403, 835, 709, 481, 154, 538, 818, 572, 236, 868, 312, 408, 424, 15, 131, 259, 515, 133, 517, 193, 321, 577, 385, 26, 138, 522, 146, 274, 530, 770, 44, 140, 524, 100, 548, 196, 580, 56, 152, 280, 536, 168, 296, 392, 304, 560, 400, 224, 352, 416, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_143, vertices_527, vertices_403, vertices_835, vertices_709, vertices_481, vertices_154, vertices_538, vertices_818, vertices_572, vertices_236, vertices_868, vertices_312, vertices_408, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_15, vertices_131, vertices_259, vertices_515, vertices_133, vertices_517, vertices_193, vertices_321, vertices_577, vertices_385, vertices_26, vertices_138, vertices_522, vertices_146, vertices_274, vertices_530, vertices_770, vertices_44, vertices_140, vertices_524, vertices_100, vertices_548, vertices_196, vertices_580, vertices_56, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_392, vertices_304, vertices_560, vertices_400, vertices_224, vertices_352, vertices_416, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_143), (false, vertices_527), (false, vertices_403), (false, vertices_835), (false, vertices_709), (false, vertices_481), (true, vertices_26), (true, vertices_530), (true, vertices_44), (true, vertices_100), (true, vertices_548), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_168), (true, vertices_296), (true, vertices_392), (true, vertices_304), (true, vertices_560), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 15 22 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_143) then 16 else
  if p.val = (false, vertices_527) then 17 else
  if p.val = (false, vertices_403) then 20 else
  if p.val = (false, vertices_835) then 21 else
  if p.val = (false, vertices_709) then 18 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_44) then 2 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_56) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_800) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_143), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 22 => Sum.inl 2
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
cert_row_4 0 0 3 4 7 8 818 274 2
cert_row_4 1 1 2 3 4 8 572 44 2
cert_row_4 2 1 2 4 5 6 236 44 3
cert_row_4 3 1 4 5 7 8 868 100 3
cert_rows
cert_pivot_2 0 3 2 1
cert_heightProof 4
cert_coverFacet 0 154
cert_cover_2 0 2 0 3 6 26 154 3
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 818
cert_cover_5 2 0 0 3 4 7 274 818 2
cert_coverFacet 3 572
cert_cover_5 3 1 1 2 3 4 44 572 2
cert_coverFacet 4 236
cert_cover_5 4 2 1 2 4 5 44 236 3
cert_coverFacet 5 868
cert_cover_5 5 3 1 4 5 7 100 868 3
cert_coverFacet 6 312
cert_cover_2 6 3 2 4 7 56 312 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0208

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e10q1_0209.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0209

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 541, 45, 181, 425, 657, 961, 46, 526, 118, 838, 234, 458, 596, 752, 13, 21, 37, 41, 265, 521, 145, 529, 161, 385, 641, 769, 14, 38, 70, 518, 42, 202, 266, 522, 98, 322, 770, 44, 524, 52, 84, 532, 580, 168, 392, 112, 176, 592, 656, 224, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_541, vertices_45, vertices_181, vertices_425, vertices_657, vertices_961, vertices_46, vertices_526, vertices_118, vertices_838, vertices_234, vertices_458, vertices_596, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_37, vertices_41, vertices_265, vertices_521, vertices_145, vertices_529, vertices_161, vertices_385, vertices_641, vertices_769, vertices_14, vertices_38, vertices_70, vertices_518, vertices_42, vertices_202, vertices_266, vertices_522, vertices_98, vertices_322, vertices_770, vertices_44, vertices_524, vertices_52, vertices_84, vertices_532, vertices_580, vertices_168, vertices_392, vertices_112, vertices_176, vertices_592, vertices_656, vertices_224, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_541), (false, vertices_45), (false, vertices_181), (false, vertices_425), (false, vertices_657), (false, vertices_961), (true, vertices_14), (true, vertices_38), (true, vertices_70), (true, vertices_518), (true, vertices_42), (true, vertices_202), (true, vertices_98), (true, vertices_322), (true, vertices_84), (true, vertices_580), (true, vertices_112), (true, vertices_592), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 23 24 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_541) then 18 else
  if p.val = (false, vertices_45) then 0 else
  if p.val = (false, vertices_181) then 19 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_657) then 1 else
  if p.val = (false, vertices_961) then 25 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_38) then 3 else
  if p.val = (true, vertices_70) then 4 else
  if p.val = (true, vertices_518) then 5 else
  if p.val = (true, vertices_42) then 6 else
  if p.val = (true, vertices_202) then 16 else
  if p.val = (true, vertices_98) then 7 else
  if p.val = (true, vertices_322) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_224) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_45), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_657), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
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
cert_row_2 0 0 2 5 6 202
cert_row_4 1 0 1 5 7 8 838 70 3
cert_row_4 2 0 1 3 4 5 118 38 2
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 2 7 0 3
cert_heightProof 4
cert_coverFacet 0 46
cert_cover_2 0 1 0 2 4 14 46 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 118
cert_cover_5 2 2 0 1 3 4 38 118 2
cert_coverFacet 3 838
cert_cover_5 3 1 0 1 5 7 70 838 3
cert_coverFacet 4 234
cert_cover_5 4 0 0 2 4 5 42 234 3
cert_coverFacet 5 458
cert_cover_5 5 0 0 2 5 7 202 458 3
cert_coverFacet 6 596
cert_cover_2 6 3 1 5 8 84 596 3
cert_coverFacet 7 752
cert_cover_5 7 3 3 4 5 6 112 752 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0209

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e10q1_0210.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0210

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [211, 403, 109, 421, 709, 313, 89, 598, 794, 962, 92, 540, 556, 676, 936, 147, 37, 69, 133, 25, 41, 73, 81, 273, 289, 193, 385, 82, 274, 530, 194, 578, 386, 770, 28, 44, 76, 524, 84, 532, 164, 548, 580, 644, 88, 280, 536, 296, 552, 776, 416, 672, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_211, vertices_403, vertices_109, vertices_421, vertices_709, vertices_313, vertices_89, vertices_598, vertices_794, vertices_962, vertices_92, vertices_540, vertices_556, vertices_676, vertices_936] (by decide +kernel)
  polygons := literalFinset [vertices_147, vertices_37, vertices_69, vertices_133, vertices_25, vertices_41, vertices_73, vertices_81, vertices_273, vertices_289, vertices_193, vertices_385, vertices_82, vertices_274, vertices_530, vertices_194, vertices_578, vertices_386, vertices_770, vertices_28, vertices_44, vertices_76, vertices_524, vertices_84, vertices_532, vertices_164, vertices_548, vertices_580, vertices_644, vertices_88, vertices_280, vertices_536, vertices_296, vertices_552, vertices_776, vertices_416, vertices_672, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_211), (false, vertices_403), (false, vertices_109), (false, vertices_421), (false, vertices_709), (false, vertices_313), (false, vertices_89), (true, vertices_530), (true, vertices_578), (true, vertices_770), (true, vertices_28), (true, vertices_524), (true, vertices_84), (true, vertices_532), (true, vertices_548), (true, vertices_536), (true, vertices_552), (true, vertices_776), (true, vertices_672), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_211) then 15 else
  if p.val = (false, vertices_403) then 16 else
  if p.val = (false, vertices_109) then 18 else
  if p.val = (false, vertices_421) then 19 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_313) then 22 else
  if p.val = (false, vertices_89) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_578) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_672) then 12 else
  if p.val = (true, vertices_896) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_89), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 8 598 82 1
cert_row_4 1 0 2 3 7 8 794 274 1
cert_row_4 2 0 5 6 7 8 962 194 3
cert_row_4 3 2 4 6 7 8 936 296 2
cert_rows
cert_pivot_2 1 3 0 2
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 82 598 1
cert_coverFacet 1 794
cert_cover_5 1 1 0 2 3 7 274 794 1
cert_coverFacet 2 962
cert_cover_5 2 2 0 5 6 7 194 962 3
cert_coverFacet 3 92
cert_cover_2 3 2 1 3 5 28 92 3
cert_coverFacet 4 540
cert_cover_2 4 2 1 3 8 28 540 3
cert_coverFacet 5 556
cert_cover_2 5 2 1 4 8 44 556 3
cert_coverFacet 6 676
cert_cover_2 6 4 1 6 8 164 676 3
cert_coverFacet 7 936
cert_cover_5 7 3 2 4 6 7 296 936 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0210

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_2793 : Certifies 2793 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0181.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2794 : Certifies 2794 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0182.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2795 : Certifies 2795 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0183.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2796 : Certifies 2796 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0184.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2797 : Certifies 2797 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0185.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2798 : Certifies 2798 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0186.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2799 : Certifies 2799 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0187.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2800 : Certifies 2800 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0188.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2801 : Certifies 2801 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0189.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2802 : Certifies 2802 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0190.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2803 : Certifies 2803 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0191.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2804 : Certifies 2804 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0192.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2805 : Certifies 2805 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0193.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2806 : Certifies 2806 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0194.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2807 : Certifies 2807 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0195.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2808 : Certifies 2808 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0196.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2809 : Certifies 2809 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0197.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2810 : Certifies 2810 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0198.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2811 : Certifies 2811 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0199.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2812 : Certifies 2812 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0200.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2813 : Certifies 2813 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0201.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2814 : Certifies 2814 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0202.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2815 : Certifies 2815 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0203.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2816 : Certifies 2816 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0204.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2817 : Certifies 2817 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0205.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2818 : Certifies 2818 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0206.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2819 : Certifies 2819 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0207.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2820 : Certifies 2820 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0208.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2821 : Certifies 2821 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0209.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2822 : Certifies 2822 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0210.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B092 (j : Fin 30) :
    Certifies (2793 + j.val) := by
  fin_cases j
  · exact projection_2793
  · exact projection_2794
  · exact projection_2795
  · exact projection_2796
  · exact projection_2797
  · exact projection_2798
  · exact projection_2799
  · exact projection_2800
  · exact projection_2801
  · exact projection_2802
  · exact projection_2803
  · exact projection_2804
  · exact projection_2805
  · exact projection_2806
  · exact projection_2807
  · exact projection_2808
  · exact projection_2809
  · exact projection_2810
  · exact projection_2811
  · exact projection_2812
  · exact projection_2813
  · exact projection_2814
  · exact projection_2815
  · exact projection_2816
  · exact projection_2817
  · exact projection_2818
  · exact projection_2819
  · exact projection_2820
  · exact projection_2821
  · exact projection_2822

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
