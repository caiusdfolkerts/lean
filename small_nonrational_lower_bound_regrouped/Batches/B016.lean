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
/- Source: ProjectionCertificates/R_m15e10q1_0685.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0685

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 397, 229, 837, 793, 681, 310, 358, 666, 178, 850, 674, 180, 404, 408, 69, 133, 261, 137, 265, 521, 97, 161, 545, 577, 769, 294, 50, 146, 274, 530, 98, 162, 546, 322, 578, 642, 52, 148, 276, 100, 164, 324, 388, 152, 280, 536, 392, 648, 176, 400, 784, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_397, vertices_229, vertices_837, vertices_793, vertices_681, vertices_310, vertices_358, vertices_666, vertices_178, vertices_850, vertices_674, vertices_180, vertices_404, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_137, vertices_265, vertices_521, vertices_97, vertices_161, vertices_545, vertices_577, vertices_769, vertices_294, vertices_50, vertices_146, vertices_274, vertices_530, vertices_98, vertices_162, vertices_546, vertices_322, vertices_578, vertices_642, vertices_52, vertices_148, vertices_276, vertices_100, vertices_164, vertices_324, vertices_388, vertices_152, vertices_280, vertices_536, vertices_392, vertices_648, vertices_176, vertices_400, vertices_784, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_397), (false, vertices_229), (false, vertices_837), (false, vertices_793), (false, vertices_681), (true, vertices_294), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_322), (true, vertices_642), (true, vertices_52), (true, vertices_148), (true, vertices_276), (true, vertices_152), (true, vertices_176), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 14 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_229) then 18 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_793) then 21 else
  if p.val = (false, vertices_681) then 22 else
  if p.val = (true, vertices_294) then 15 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_400) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_294), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 4 7 294
cert_row_4 1 0 2 3 6 8 666 146 1
cert_row_4 2 0 3 5 7 8 850 274 2
cert_rows_3
cert_pivot_3 2 1 0
cert_heightProof 3
cert_coverFacet 0 310
cert_cover_5 0 0 0 1 3 4 294 310 2
cert_coverFacet 1 358
cert_cover_5 1 0 0 1 4 5 294 358 3
cert_coverFacet 2 666
cert_cover_5 2 1 0 2 3 6 146 666 1
cert_coverFacet 3 178
cert_cover_2 3 3 0 4 6 50 178 3
cert_coverFacet 4 850
cert_cover_5 4 2 0 3 5 7 274 850 2
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 180
cert_cover_2 6 3 1 4 6 52 180 3
cert_coverFacet 7 404
cert_cover_2 7 3 1 6 7 148 404 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 3 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0685

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e10q1_0702.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0702

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 173, 557, 793, 457, 433, 614, 842, 114, 210, 914, 450, 204, 588, 244, 45, 137, 265, 521, 49, 273, 529, 161, 545, 385, 50, 82, 146, 530, 98, 546, 194, 322, 578, 386, 770, 76, 140, 524, 100, 164, 548, 196, 580, 200, 328, 584, 776, 112, 176, 208, 400, 784, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_173, vertices_557, vertices_793, vertices_457, vertices_433, vertices_614, vertices_842, vertices_114, vertices_210, vertices_914, vertices_450, vertices_204, vertices_588, vertices_244] (by decide +kernel)
  polygons := literalFinset [vertices_45, vertices_137, vertices_265, vertices_521, vertices_49, vertices_273, vertices_529, vertices_161, vertices_545, vertices_385, vertices_50, vertices_82, vertices_146, vertices_530, vertices_98, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_76, vertices_140, vertices_524, vertices_100, vertices_164, vertices_548, vertices_196, vertices_580, vertices_200, vertices_328, vertices_584, vertices_776, vertices_112, vertices_176, vertices_208, vertices_400, vertices_784, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_173), (false, vertices_557), (false, vertices_793), (false, vertices_457), (false, vertices_433), (true, vertices_82), (true, vertices_146), (true, vertices_98), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_386), (true, vertices_770), (true, vertices_76), (true, vertices_100), (true, vertices_196), (true, vertices_580), (true, vertices_584), (true, vertices_112), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 16 else
  if p.val = (false, vertices_173) then 18 else
  if p.val = (false, vertices_557) then 19 else
  if p.val = (false, vertices_793) then 21 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_208) then 14 else
  0
cert_priority
cert_nodeAtPriority_52 82 1 146 2 98 194 322 578 386 770 76 100 196 580 584 112 208 563 173 557 793 457 433
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 7 8 842 322 1
cert_row_4 1 0 3 6 7 8 914 146 3
cert_row_4 2 0 1 4 5 8 614 98 1
cert_row_4 3 1 3 4 5 6 244 100 1
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_5 0 2 0 1 4 5 98 614 1
cert_coverFacet 1 842
cert_cover_5 1 0 0 2 5 7 322 842 1
cert_coverFacet 2 114
cert_cover_2 2 3 0 4 5 50 114 3
cert_coverFacet 3 210
cert_cover_2 3 3 0 5 6 82 210 3
cert_coverFacet 4 914
cert_cover_5 4 1 0 3 6 7 146 914 3
cert_coverFacet 5 450
cert_cover_2 5 5 0 6 7 194 450 3
cert_coverFacet 6 204
cert_cover_2 6 2 1 5 6 76 204 3
cert_coverFacet 7 588
cert_cover_2 7 2 1 5 8 76 588 3
cert_coverFacet 8 244
cert_cover_5 8 3 1 3 4 5 100 244 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0702

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e10q1_0704.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0704

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 213, 789, 613, 345, 361, 902, 618, 170, 650, 418, 716, 404, 440, 216, 21, 69, 517, 329, 81, 273, 97, 289, 545, 769, 42, 138, 522, 162, 290, 546, 386, 642, 770, 148, 276, 196, 580, 388, 644, 772, 88, 152, 280, 104, 168, 296, 200, 584, 648, 208, 400, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_213, vertices_789, vertices_613, vertices_345, vertices_361, vertices_902, vertices_618, vertices_170, vertices_650, vertices_418, vertices_716, vertices_404, vertices_440, vertices_216] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_517, vertices_329, vertices_81, vertices_273, vertices_97, vertices_289, vertices_545, vertices_769, vertices_42, vertices_138, vertices_522, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_148, vertices_276, vertices_196, vertices_580, vertices_388, vertices_644, vertices_772, vertices_88, vertices_152, vertices_280, vertices_104, vertices_168, vertices_296, vertices_200, vertices_584, vertices_648, vertices_208, vertices_400, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_213), (false, vertices_789), (false, vertices_613), (false, vertices_345), (false, vertices_361), (true, vertices_42), (true, vertices_138), (true, vertices_522), (true, vertices_162), (true, vertices_386), (true, vertices_642), (true, vertices_388), (true, vertices_644), (true, vertices_152), (true, vertices_168), (true, vertices_200), (true, vertices_584), (true, vertices_648), (true, vertices_400), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_213) then 18 else
  if p.val = (false, vertices_789) then 19 else
  if p.val = (false, vertices_613) then 20 else
  if p.val = (false, vertices_345) then 22 else
  if p.val = (false, vertices_361) then 23 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
cert_nodeAtPriority_36 0 42 1 138 2 522 162 386 642 388 644 152 168 200 584 648 400 416 803 213 789 613 345 361
cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 4 6 7 440 152 2
cert_row_4 1 0 1 6 7 8 902 386 1
cert_row_4 2 0 2 4 5 8 618 42 3
cert_row_4 3 1 2 5 6 8 716 196 1
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 1 0 1 6 7 386 902 1
cert_coverFacet 1 618
cert_cover_5 1 2 0 2 4 5 42 618 3
cert_coverFacet 2 170
cert_cover_2 2 2 0 4 6 42 170 3
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 418
cert_cover_2 4 4 0 6 7 162 418 3
cert_coverFacet 5 716
cert_cover_5 5 3 1 2 5 6 196 716 1
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 440
cert_cover_5 7 0 2 3 4 6 152 440 2
cert_coverFacet 8 216
cert_cover_2 8 3 2 5 6 88 216 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0704

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e10q1_0707.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0707

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 109, 781, 117, 405, 681, 177, 454, 842, 690, 210, 594, 332, 212, 632, 13, 21, 101, 261, 41, 521, 49, 145, 161, 385, 641, 769, 82, 146, 530, 194, 322, 578, 386, 642, 770, 76, 268, 84, 148, 196, 324, 388, 104, 552, 328, 584, 776, 112, 176, 560, 208, 592, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_109, vertices_781, vertices_117, vertices_405, vertices_681, vertices_177, vertices_454, vertices_842, vertices_690, vertices_210, vertices_594, vertices_332, vertices_212, vertices_632] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_101, vertices_261, vertices_41, vertices_521, vertices_49, vertices_145, vertices_161, vertices_385, vertices_641, vertices_769, vertices_82, vertices_146, vertices_530, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_76, vertices_268, vertices_84, vertices_148, vertices_196, vertices_324, vertices_388, vertices_104, vertices_552, vertices_328, vertices_584, vertices_776, vertices_112, vertices_176, vertices_560, vertices_208, vertices_592, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_109), (false, vertices_781), (false, vertices_117), (false, vertices_405), (false, vertices_681), (false, vertices_177), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_196), (true, vertices_324), (true, vertices_328), (true, vertices_584), (true, vertices_560), (true, vertices_208), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 19 16 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 15 else
  if p.val = (false, vertices_109) then 20 else
  if p.val = (false, vertices_781) then 17 else
  if p.val = (false, vertices_117) then 21 else
  if p.val = (false, vertices_405) then 22 else
  if p.val = (false, vertices_681) then 18 else
  if p.val = (false, vertices_177) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_592) then 13 else
  0
cert_priority
cert_nodeAtPriority_48 0 177 1 82 2 146 530 194 322 578 196 324 328 584 560 208 592 899 781 681 109 117 405
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 7 454 194 1
cert_row_4 1 0 2 5 7 8 842 322 1
cert_row_4 2 0 3 4 6 8 690 146 2
cert_row_4 3 2 3 4 5 8 632 104 1
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 454
cert_cover_5 0 0 0 1 5 6 194 454 1
cert_coverFacet 1 842
cert_cover_5 1 1 0 2 5 7 322 842 1
cert_coverFacet 2 690
cert_cover_5 2 2 0 3 4 6 146 690 2
cert_coverFacet 3 210
cert_cover_2 3 3 0 5 6 82 210 3
cert_coverFacet 4 594
cert_cover_2 4 3 0 5 8 82 594 3
cert_coverFacet 5 332
cert_cover_2 5 2 1 5 7 76 332 3
cert_coverFacet 6 212
cert_cover_2 6 3 1 5 6 84 212 3
cert_coverFacet 7 632
cert_cover_5 7 3 2 3 4 5 104 632 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0707

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e10q1_0711.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0711

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 109, 781, 661, 229, 425, 598, 842, 434, 338, 658, 588, 212, 376, 240, 13, 101, 133, 517, 41, 265, 161, 385, 641, 769, 82, 146, 274, 530, 322, 578, 386, 642, 770, 76, 524, 84, 148, 532, 196, 580, 104, 296, 328, 584, 776, 112, 176, 304, 208, 336, 656, 224, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_109, vertices_781, vertices_661, vertices_229, vertices_425, vertices_598, vertices_842, vertices_434, vertices_338, vertices_658, vertices_588, vertices_212, vertices_376, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_101, vertices_133, vertices_517, vertices_41, vertices_265, vertices_161, vertices_385, vertices_641, vertices_769, vertices_82, vertices_146, vertices_274, vertices_530, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_76, vertices_524, vertices_84, vertices_148, vertices_532, vertices_196, vertices_580, vertices_104, vertices_296, vertices_328, vertices_584, vertices_776, vertices_112, vertices_176, vertices_304, vertices_208, vertices_336, vertices_656, vertices_224, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_109), (false, vertices_781), (false, vertices_661), (false, vertices_229), (false, vertices_425), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_322), (true, vertices_578), (true, vertices_84), (true, vertices_580), (true, vertices_328), (true, vertices_584), (true, vertices_112), (true, vertices_176), (true, vertices_304), (true, vertices_208), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 20 17 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 16 else
  if p.val = (false, vertices_109) then 21 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_661) then 22 else
  if p.val = (false, vertices_229) then 23 else
  if p.val = (false, vertices_425) then 19 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_328) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_336) then 14 else
  0
cert_priority
cert_nodeAtPriority_42 82 1 146 2 274 530 322 578 84 580 328 584 112 176 304 208 336 899 781 425 109 661 229
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 8 598 82 1
cert_row_4 1 0 2 5 7 8 842 322 1
cert_row_4 2 0 3 4 6 7 434 146 2
cert_row_4 3 2 3 4 5 7 376 104 1
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 82 598 1
cert_coverFacet 1 842
cert_cover_5 1 1 0 2 5 7 322 842 1
cert_coverFacet 2 434
cert_cover_5 2 2 0 3 4 6 146 434 2
cert_coverFacet 3 338
cert_cover_2 3 3 0 5 7 82 338 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 588
cert_cover_2 5 2 1 5 8 76 588 3
cert_coverFacet 6 212
cert_cover_2 6 3 1 5 6 84 212 3
cert_coverFacet 7 376
cert_cover_5 7 3 2 3 4 5 104 376 1
cert_coverFacet 8 240
cert_cover_2 8 4 3 5 6 112 240 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0711

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e10q1_0715.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0715

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 653, 453, 217, 585, 865, 406, 662, 314, 538, 618, 802, 120, 664, 496, 133, 261, 517, 73, 137, 521, 193, 321, 577, 769, 150, 262, 518, 26, 42, 522, 274, 530, 290, 546, 770, 388, 644, 56, 88, 152, 536, 104, 584, 648, 112, 304, 208, 400, 656, 352, 608, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_653, vertices_453, vertices_217, vertices_585, vertices_865, vertices_406, vertices_662, vertices_314, vertices_538, vertices_618, vertices_802, vertices_120, vertices_664, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_521, vertices_193, vertices_321, vertices_577, vertices_769, vertices_150, vertices_262, vertices_518, vertices_26, vertices_42, vertices_522, vertices_274, vertices_530, vertices_290, vertices_546, vertices_770, vertices_388, vertices_644, vertices_56, vertices_88, vertices_152, vertices_536, vertices_104, vertices_584, vertices_648, vertices_112, vertices_304, vertices_208, vertices_400, vertices_656, vertices_352, vertices_608, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_653), (false, vertices_453), (false, vertices_217), (false, vertices_585), (false, vertices_865), (true, vertices_150), (true, vertices_26), (true, vertices_42), (true, vertices_522), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_546), (true, vertices_56), (true, vertices_536), (true, vertices_104), (true, vertices_112), (true, vertices_304), (true, vertices_400), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 16 else
  if p.val = (false, vertices_653) then 19 else
  if p.val = (false, vertices_453) then 20 else
  if p.val = (false, vertices_217) then 22 else
  if p.val = (false, vertices_585) then 0 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_150) then 17 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_656) then 14 else
  0
cert_priority
cert_nodeAtPriority_34 585 26 42 522 274 530 290 546 56 536 104 112 304 400 656 775 150 653 453 217 865
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 6 150
cert_row_4 1 0 2 4 5 8 618 42 3
cert_row_4 2 0 2 3 4 7 314 26 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 1 8 0 3
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 0 0 1 3 7 150 406 3
cert_coverFacet 1 662
cert_cover_5 1 0 0 1 3 8 150 662 3
cert_coverFacet 2 314
cert_cover_5 2 2 0 2 3 4 26 314 3
cert_coverFacet 3 538
cert_cover_2 3 2 0 3 8 26 538 3
cert_coverFacet 4 618
cert_cover_5 4 1 0 2 4 5 42 618 3
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 120
cert_cover_2 6 3 2 4 5 56 120 3
cert_coverFacet 7 664
cert_cover_2 7 3 2 6 8 152 664 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 112 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0715

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e10q1_0745.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0745

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 109, 205, 661, 805, 425, 214, 458, 818, 338, 658, 596, 612, 376, 624, 77, 37, 133, 517, 41, 137, 289, 385, 641, 769, 82, 146, 274, 530, 194, 322, 386, 642, 770, 84, 148, 532, 100, 548, 196, 580, 104, 296, 200, 328, 392, 112, 304, 560, 336, 592, 656, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_109, vertices_205, vertices_661, vertices_805, vertices_425, vertices_214, vertices_458, vertices_818, vertices_338, vertices_658, vertices_596, vertices_612, vertices_376, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_77, vertices_37, vertices_133, vertices_517, vertices_41, vertices_137, vertices_289, vertices_385, vertices_641, vertices_769, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_386, vertices_642, vertices_770, vertices_84, vertices_148, vertices_532, vertices_100, vertices_548, vertices_196, vertices_580, vertices_104, vertices_296, vertices_200, vertices_328, vertices_392, vertices_112, vertices_304, vertices_560, vertices_336, vertices_592, vertices_656, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_109), (false, vertices_205), (false, vertices_661), (false, vertices_805), (false, vertices_425), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_194), (true, vertices_322), (true, vertices_84), (true, vertices_580), (true, vertices_328), (true, vertices_112), (true, vertices_304), (true, vertices_560), (true, vertices_336), (true, vertices_592), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 21 17 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 16 else
  if p.val = (false, vertices_109) then 18 else
  if p.val = (false, vertices_205) then 19 else
  if p.val = (false, vertices_661) then 22 else
  if p.val = (false, vertices_805) then 23 else
  if p.val = (false, vertices_425) then 20 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_328) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_608) then 14 else
  0
cert_priority
cert_nodeAtPriority_36 0 82 2 146 1 274 530 194 322 84 580 328 112 304 560 336 592 608 899 109 205 425 661 805
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 6 214 82 1
cert_row_4 1 0 2 5 6 7 458 194 1
cert_row_4 2 0 3 4 7 8 818 274 2
cert_row_4 3 2 3 4 5 7 376 104 1
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 5 82 214 1
cert_coverFacet 1 458
cert_cover_5 1 1 0 2 5 6 194 458 1
cert_coverFacet 2 818
cert_cover_5 2 2 0 3 4 7 274 818 2
cert_coverFacet 3 338
cert_cover_2 3 3 0 5 7 82 338 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 596
cert_cover_2 5 3 1 5 8 84 596 3
cert_coverFacet 6 612
cert_cover_2 6 4 1 5 8 100 612 3
cert_coverFacet 7 376
cert_cover_5 7 3 2 3 4 5 104 376 1
cert_coverFacet 8 624
cert_cover_2 8 4 3 5 8 112 624 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0745

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e10q1_0791.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0791

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [339, 803, 707, 677, 425, 465, 790, 602, 316, 540, 172, 716, 804, 216, 408, 67, 259, 515, 337, 161, 289, 545, 193, 385, 641, 82, 274, 530, 578, 770, 28, 44, 140, 524, 276, 532, 164, 292, 548, 644, 772, 88, 152, 280, 536, 168, 296, 200, 584, 392, 208, 400, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_803, vertices_707, vertices_677, vertices_425, vertices_465, vertices_790, vertices_602, vertices_316, vertices_540, vertices_172, vertices_716, vertices_804, vertices_216, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_337, vertices_161, vertices_289, vertices_545, vertices_193, vertices_385, vertices_641, vertices_82, vertices_274, vertices_530, vertices_578, vertices_770, vertices_28, vertices_44, vertices_140, vertices_524, vertices_276, vertices_532, vertices_164, vertices_292, vertices_548, vertices_644, vertices_772, vertices_88, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_200, vertices_584, vertices_392, vertices_208, vertices_400, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_803), (false, vertices_707), (false, vertices_677), (false, vertices_425), (false, vertices_465), (true, vertices_530), (true, vertices_28), (true, vertices_44), (true, vertices_140), (true, vertices_524), (true, vertices_276), (true, vertices_532), (true, vertices_292), (true, vertices_772), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_200), (true, vertices_584)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 23 else
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_707) then 17 else
  if p.val = (false, vertices_677) then 19 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (true, vertices_530) then 0 else
  if p.val = (true, vertices_28) then 1 else
  if p.val = (true, vertices_44) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_200) then 13 else
  if p.val = (true, vertices_584) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 4 7 316 28 3
cert_row_4 1 0 1 3 7 8 790 274 1
cert_row_4 2 0 2 3 5 8 602 82 1
cert_row_4 3 1 2 5 6 8 716 140 2
cert_rows
cert_pivot_2 4 7 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 1 0 1 3 7 274 790 1
cert_coverFacet 1 602
cert_cover_5 1 2 0 2 3 5 82 602 1
cert_coverFacet 2 316
cert_cover_5 2 0 1 2 3 4 28 316 3
cert_coverFacet 3 540
cert_cover_2 3 2 1 3 8 28 540 3
cert_coverFacet 4 172
cert_cover_2 4 2 1 4 6 44 172 3
cert_coverFacet 5 716
cert_cover_5 5 3 1 2 5 6 140 716 2
cert_coverFacet 6 804
cert_cover_2 6 4 1 7 8 292 804 3
cert_coverFacet 7 216
cert_cover_2 7 3 2 5 6 88 216 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0791

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e10q1_0808.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0808

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 173, 557, 793, 457, 689, 614, 842, 114, 818, 210, 450, 204, 588, 244, 45, 137, 265, 521, 145, 273, 529, 161, 545, 385, 50, 82, 146, 274, 98, 546, 194, 322, 578, 386, 770, 76, 140, 524, 100, 164, 548, 196, 580, 200, 328, 584, 776, 112, 176, 560, 208, 784, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_173, vertices_557, vertices_793, vertices_457, vertices_689, vertices_614, vertices_842, vertices_114, vertices_818, vertices_210, vertices_450, vertices_204, vertices_588, vertices_244] (by decide +kernel)
  polygons := literalFinset [vertices_45, vertices_137, vertices_265, vertices_521, vertices_145, vertices_273, vertices_529, vertices_161, vertices_545, vertices_385, vertices_50, vertices_82, vertices_146, vertices_274, vertices_98, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_76, vertices_140, vertices_524, vertices_100, vertices_164, vertices_548, vertices_196, vertices_580, vertices_200, vertices_328, vertices_584, vertices_776, vertices_112, vertices_176, vertices_560, vertices_208, vertices_784, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_173), (false, vertices_557), (false, vertices_793), (false, vertices_457), (false, vertices_689), (true, vertices_50), (true, vertices_82), (true, vertices_98), (true, vertices_546), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_76), (true, vertices_100), (true, vertices_196), (true, vertices_580), (true, vertices_584), (true, vertices_112), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 16 else
  if p.val = (false, vertices_173) then 18 else
  if p.val = (false, vertices_557) then 19 else
  if p.val = (false, vertices_793) then 21 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (false, vertices_689) then 24 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_208) then 14 else
  0
cert_priority
cert_nodeAtPriority_52 50 1 82 2 98 546 194 322 578 770 76 100 196 580 584 112 208 403 173 557 793 457 689
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 7 8 842 322 1
cert_row_4 1 0 3 4 7 8 818 50 3
cert_row_4 2 0 1 4 5 8 614 98 1
cert_row_4 3 1 3 4 5 6 244 100 1
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_5 0 2 0 1 4 5 98 614 1
cert_coverFacet 1 842
cert_cover_5 1 0 0 2 5 7 322 842 1
cert_coverFacet 2 114
cert_cover_2 2 3 0 4 5 50 114 3
cert_coverFacet 3 818
cert_cover_5 3 1 0 3 4 7 50 818 3
cert_coverFacet 4 210
cert_cover_2 4 3 0 5 6 82 210 3
cert_coverFacet 5 450
cert_cover_2 5 5 0 6 7 194 450 3
cert_coverFacet 6 204
cert_cover_2 6 2 1 5 6 76 204 3
cert_coverFacet 7 588
cert_cover_2 7 2 1 5 8 76 588 3
cert_coverFacet 8 244
cert_cover_5 8 3 1 3 4 5 100 244 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0808

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m15e10q1_0809.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0809

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 587, 309, 569, 409, 865, 710, 666, 394, 482, 628, 404, 660, 228, 420, 75, 25, 265, 521, 49, 273, 289, 545, 321, 577, 138, 266, 522, 194, 322, 578, 386, 642, 52, 148, 276, 532, 100, 164, 292, 196, 580, 388, 644, 152, 536, 392, 560, 400, 656, 224, 352, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_587, vertices_309, vertices_569, vertices_409, vertices_865, vertices_710, vertices_666, vertices_394, vertices_482, vertices_628, vertices_404, vertices_660, vertices_228, vertices_420] (by decide +kernel)
  polygons := literalFinset [vertices_75, vertices_25, vertices_265, vertices_521, vertices_49, vertices_273, vertices_289, vertices_545, vertices_321, vertices_577, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_52, vertices_148, vertices_276, vertices_532, vertices_100, vertices_164, vertices_292, vertices_196, vertices_580, vertices_388, vertices_644, vertices_152, vertices_536, vertices_392, vertices_560, vertices_400, vertices_656, vertices_224, vertices_352, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_587), (false, vertices_309), (false, vertices_569), (false, vertices_409), (false, vertices_865), (true, vertices_138), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_148), (true, vertices_532), (true, vertices_100), (true, vertices_164), (true, vertices_196), (true, vertices_580), (true, vertices_388), (true, vertices_644), (true, vertices_656), (true, vertices_224), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 16 else
  if p.val = (false, vertices_587) then 17 else
  if p.val = (false, vertices_309) then 19 else
  if p.val = (false, vertices_569) then 21 else
  if p.val = (false, vertices_409) then 22 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_148) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
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
cert_row_4 0 0 2 3 6 8 666 138 2
cert_row_4 1 0 4 5 6 7 482 194 1
cert_row_4 2 0 1 5 6 8 710 194 1
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 2 0 1 5 6 194 710 1
cert_coverFacet 1 666
cert_cover_5 1 0 0 2 3 6 138 666 2
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 482
cert_cover_5 3 1 0 4 5 6 194 482 1
cert_coverFacet 4 628
cert_cover_5 4 3 1 3 4 5 52 628 3
cert_coverFacet 5 404
cert_cover_2 5 3 1 6 7 148 404 3
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 228
cert_cover_2 7 4 1 5 6 100 228 3
cert_coverFacet 8 420
cert_cover_2 8 4 1 6 7 164 420 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0809

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m15e10q1_0810.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0810

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 333, 453, 617, 425, 721, 790, 810, 178, 306, 658, 604, 780, 436, 212, 325, 41, 73, 265, 161, 545, 193, 577, 385, 641, 50, 146, 274, 530, 162, 290, 546, 642, 770, 76, 268, 524, 84, 148, 276, 532, 196, 388, 772, 296, 552, 584, 776, 176, 304, 208, 592, 656, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_333, vertices_453, vertices_617, vertices_425, vertices_721, vertices_790, vertices_810, vertices_178, vertices_306, vertices_658, vertices_604, vertices_780, vertices_436, vertices_212] (by decide +kernel)
  polygons := literalFinset [vertices_325, vertices_41, vertices_73, vertices_265, vertices_161, vertices_545, vertices_193, vertices_577, vertices_385, vertices_641, vertices_50, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_76, vertices_268, vertices_524, vertices_84, vertices_148, vertices_276, vertices_532, vertices_196, vertices_388, vertices_772, vertices_296, vertices_552, vertices_584, vertices_776, vertices_176, vertices_304, vertices_208, vertices_592, vertices_656, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_333), (false, vertices_453), (false, vertices_617), (false, vertices_425), (false, vertices_721), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_770), (true, vertices_524), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_772), (true, vertices_776), (true, vertices_176), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_333) then 18 else
  if p.val = (false, vertices_453) then 19 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (false, vertices_721) then 24 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_304) then 14 else
  0
cert_priority
cert_nodeAtPriority_52 50 1 146 2 274 530 290 770 524 84 148 276 532 772 776 176 304 675 333 453 617 425 721
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 5 8 604 76 2
cert_row_4 1 0 2 4 7 8 810 290 1
cert_row_4 2 0 1 3 7 8 790 274 1
cert_row_4 3 1 3 4 6 7 436 148 2
cert_rows
cert_pivot_2 5 2 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 2 0 1 3 7 274 790 1
cert_coverFacet 1 810
cert_cover_5 1 1 0 2 4 7 290 810 1
cert_coverFacet 2 178
cert_cover_2 2 3 0 4 6 50 178 3
cert_coverFacet 3 306
cert_cover_2 3 3 0 4 7 50 306 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 604
cert_cover_5 5 0 1 2 3 5 76 604 2
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 436
cert_cover_5 7 3 1 3 4 6 148 436 2
cert_coverFacet 8 212
cert_cover_2 8 3 1 5 6 84 212 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0810

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m15e10q1_0864.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0864

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [583, 339, 803, 557, 229, 481, 666, 282, 778, 594, 428, 652, 724, 472, 808, 67, 259, 515, 37, 69, 517, 225, 289, 545, 321, 26, 266, 522, 82, 274, 530, 578, 770, 44, 140, 524, 164, 196, 580, 644, 152, 280, 296, 552, 392, 648, 776, 208, 336, 592, 656, 416, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_583, vertices_339, vertices_803, vertices_557, vertices_229, vertices_481, vertices_666, vertices_282, vertices_778, vertices_594, vertices_428, vertices_652, vertices_724, vertices_472, vertices_808] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_37, vertices_69, vertices_517, vertices_225, vertices_289, vertices_545, vertices_321, vertices_26, vertices_266, vertices_522, vertices_82, vertices_274, vertices_530, vertices_578, vertices_770, vertices_44, vertices_140, vertices_524, vertices_164, vertices_196, vertices_580, vertices_644, vertices_152, vertices_280, vertices_296, vertices_552, vertices_392, vertices_648, vertices_776, vertices_208, vertices_336, vertices_592, vertices_656, vertices_416, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_583), (false, vertices_339), (false, vertices_803), (false, vertices_557), (false, vertices_229), (false, vertices_481), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_530), (true, vertices_140), (true, vertices_644), (true, vertices_152), (true, vertices_280), (true, vertices_296), (true, vertices_392), (true, vertices_648), (true, vertices_776), (true, vertices_208), (true, vertices_592), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 21 22 23 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_583) then 16 else
  if p.val = (false, vertices_339) then 17 else
  if p.val = (false, vertices_803) then 18 else
  if p.val = (false, vertices_557) then 20 else
  if p.val = (false, vertices_229) then 24 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_644) then 5 else
  if p.val = (true, vertices_152) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_656) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 8 666 26 3
cert_row_4 1 1 2 4 6 7 428 44 3
cert_row_4 2 1 3 5 6 8 724 196 1
cert_row_4 3 2 3 5 6 7 472 152 2
cert_rows
cert_pivot_2 0 4 1 2
cert_heightProof 4
cert_coverFacet 0 666
cert_cover_5 0 0 0 2 3 6 26 666 3
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 594
cert_cover_2 3 3 0 5 8 82 594 3
cert_coverFacet 4 428
cert_cover_5 4 1 1 2 4 6 44 428 3
cert_coverFacet 5 652
cert_cover_2 5 2 1 6 8 140 652 3
cert_coverFacet 6 724
cert_cover_5 6 2 1 3 5 6 196 724 1
cert_coverFacet 7 472
cert_cover_5 7 3 2 3 5 6 152 472 2
cert_coverFacet 8 808
cert_cover_2 8 4 2 7 8 296 808 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0864

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m15e10q1_0871.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0871

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 227, 803, 781, 309, 149, 241, 714, 626, 460, 652, 404, 856, 816, 464, 35, 131, 515, 21, 133, 261, 517, 49, 145, 225, 289, 769, 98, 546, 194, 578, 642, 140, 268, 524, 148, 276, 388, 644, 200, 328, 584, 648, 776, 112, 304, 560, 208, 336, 592, 400, 784, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_227, vertices_803, vertices_781, vertices_309, vertices_149, vertices_241, vertices_714, vertices_626, vertices_460, vertices_652, vertices_404, vertices_856, vertices_816, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_515, vertices_21, vertices_133, vertices_261, vertices_517, vertices_49, vertices_145, vertices_225, vertices_289, vertices_769, vertices_98, vertices_546, vertices_194, vertices_578, vertices_642, vertices_140, vertices_268, vertices_524, vertices_148, vertices_276, vertices_388, vertices_644, vertices_200, vertices_328, vertices_584, vertices_648, vertices_776, vertices_112, vertices_304, vertices_560, vertices_208, vertices_336, vertices_592, vertices_400, vertices_784, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_227), (false, vertices_803), (false, vertices_781), (false, vertices_309), (false, vertices_149), (false, vertices_241), (true, vertices_578), (true, vertices_140), (true, vertices_388), (true, vertices_200), (true, vertices_328), (true, vertices_584), (true, vertices_648), (true, vertices_560), (true, vertices_336), (true, vertices_592), (true, vertices_400), (true, vertices_784), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 21 22 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 15 else
  if p.val = (false, vertices_227) then 23 else
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_309) then 19 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_241) then 24 else
  if p.val = (true, vertices_578) then 1 else
  if p.val = (true, vertices_140) then 2 else
  if p.val = (true, vertices_388) then 3 else
  if p.val = (true, vertices_200) then 4 else
  if p.val = (true, vertices_328) then 5 else
  if p.val = (true, vertices_584) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_400) then 11 else
  if p.val = (true, vertices_784) then 12 else
  if p.val = (true, vertices_448) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_309), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 5 8 626 98 1
cert_row_4 1 0 2 5 6 8 714 194 1
cert_row_4 2 1 2 5 6 7 460 140 2
cert_row_4 3 2 3 5 7 8 856 328 1
cert_rows
cert_pivot_2 4 0 1 2
cert_heightProof 4
cert_coverFacet 0 714
cert_cover_5 0 1 0 2 5 6 194 714 1
cert_coverFacet 1 626
cert_cover_5 1 0 0 3 4 5 98 626 1
cert_coverFacet 2 460
cert_cover_5 2 2 1 2 5 6 140 460 2
cert_coverFacet 3 652
cert_cover_2 3 2 1 6 8 140 652 3
cert_coverFacet 4 404
cert_cover_2 4 3 1 6 7 148 404 3
cert_coverFacet 5 856
cert_cover_5 5 3 2 3 5 7 328 856 1
cert_coverFacet 6 816
cert_cover_2 6 4 3 7 8 304 816 3
cert_coverFacet 7 464
cert_cover_2 7 5 3 6 7 208 464 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0871

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m15e10q1_0896.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0896

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 301, 653, 597, 357, 233, 209, 838, 906, 370, 594, 402, 780, 440, 240, 13, 293, 69, 517, 41, 137, 81, 145, 529, 97, 193, 641, 82, 146, 274, 530, 322, 578, 386, 642, 770, 268, 524, 324, 580, 772, 168, 296, 392, 648, 776, 112, 176, 304, 208, 592, 400, 224, 352]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_301, vertices_653, vertices_597, vertices_357, vertices_233, vertices_209, vertices_838, vertices_906, vertices_370, vertices_594, vertices_402, vertices_780, vertices_440, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_293, vertices_69, vertices_517, vertices_41, vertices_137, vertices_81, vertices_145, vertices_529, vertices_97, vertices_193, vertices_641, vertices_82, vertices_146, vertices_274, vertices_530, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_268, vertices_524, vertices_324, vertices_580, vertices_772, vertices_168, vertices_296, vertices_392, vertices_648, vertices_776, vertices_112, vertices_176, vertices_304, vertices_208, vertices_592, vertices_400, vertices_224, vertices_352] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_301), (false, vertices_653), (false, vertices_597), (false, vertices_357), (false, vertices_233), (false, vertices_209), (true, vertices_82), (true, vertices_274), (true, vertices_322), (true, vertices_578), (true, vertices_386), (true, vertices_770), (true, vertices_772), (true, vertices_392), (true, vertices_776), (true, vertices_112), (true, vertices_176), (true, vertices_304), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 19 16 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 15 else
  if p.val = (false, vertices_301) then 20 else
  if p.val = (false, vertices_653) then 17 else
  if p.val = (false, vertices_597) then 21 else
  if p.val = (false, vertices_357) then 22 else
  if p.val = (false, vertices_233) then 18 else
  if p.val = (false, vertices_209) then 0 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_392) then 8 else
  if p.val = (true, vertices_776) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_400) then 13 else
  0
cert_priority
cert_nodeAtPriority_48 0 209 1 82 2 274 322 578 386 770 772 392 776 112 176 304 400 659 653 233 301 597 357
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 7 8 838 322 1
cert_row_4 1 0 2 6 7 8 906 386 1
cert_row_4 2 0 3 4 5 7 370 82 2
cert_row_4 3 2 3 4 6 7 440 168 1
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 0 0 1 5 7 322 838 1
cert_coverFacet 1 906
cert_cover_5 1 1 0 2 6 7 386 906 1
cert_coverFacet 2 370
cert_cover_5 2 2 0 3 4 5 82 370 2
cert_coverFacet 3 594
cert_cover_2 3 3 0 5 8 82 594 3
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 440
cert_cover_5 6 3 2 3 4 6 168 440 1
cert_coverFacet 7 240
cert_cover_2 7 4 3 5 6 112 240 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0896

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m15e10q1_0903.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0903

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 355, 707, 653, 409, 369, 209, 806, 626, 428, 780, 180, 564, 724, 432, 67, 259, 515, 137, 265, 521, 81, 145, 273, 353, 193, 641, 98, 290, 546, 578, 770, 140, 268, 524, 52, 148, 532, 164, 292, 548, 644, 772, 392, 776, 112, 176, 304, 560, 208, 592, 400, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_355, vertices_707, vertices_653, vertices_409, vertices_369, vertices_209, vertices_806, vertices_626, vertices_428, vertices_780, vertices_180, vertices_564, vertices_724, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_137, vertices_265, vertices_521, vertices_81, vertices_145, vertices_273, vertices_353, vertices_193, vertices_641, vertices_98, vertices_290, vertices_546, vertices_578, vertices_770, vertices_140, vertices_268, vertices_524, vertices_52, vertices_148, vertices_532, vertices_164, vertices_292, vertices_548, vertices_644, vertices_772, vertices_392, vertices_776, vertices_112, vertices_176, vertices_304, vertices_560, vertices_208, vertices_592, vertices_400, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_355), (false, vertices_707), (false, vertices_653), (false, vertices_409), (false, vertices_369), (false, vertices_209), (true, vertices_546), (true, vertices_268), (true, vertices_52), (true, vertices_148), (true, vertices_532), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_772), (true, vertices_176), (true, vertices_560), (true, vertices_592), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 19 21 22 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_355) then 23 else
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_409) then 20 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (false, vertices_209) then 0 else
  if p.val = (true, vertices_546) then 1 else
  if p.val = (true, vertices_268) then 2 else
  if p.val = (true, vertices_52) then 3 else
  if p.val = (true, vertices_148) then 4 else
  if p.val = (true, vertices_532) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_209), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 4 6 7 428 140 2
cert_row_4 1 0 1 4 7 8 806 290 1
cert_row_4 2 0 3 4 5 8 626 98 1
cert_row_4 3 1 3 5 6 8 724 148 2
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 1 0 1 4 7 290 806 1
cert_coverFacet 1 626
cert_cover_5 1 2 0 3 4 5 98 626 1
cert_coverFacet 2 428
cert_cover_5 2 0 1 2 4 6 140 428 2
cert_coverFacet 3 780
cert_cover_2 3 2 1 7 8 268 780 3
cert_coverFacet 4 180
cert_cover_2 4 3 1 4 6 52 180 3
cert_coverFacet 5 564
cert_cover_2 5 3 1 4 8 52 564 3
cert_coverFacet 6 724
cert_cover_5 6 3 1 3 5 6 148 724 2
cert_coverFacet 7 432
cert_cover_2 7 4 3 6 7 176 432 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0903

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m15e10q1_0907.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0907

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 677, 713, 849, 481, 286, 174, 598, 550, 426, 786, 92, 588, 652, 472, 161, 289, 545, 193, 321, 577, 641, 769, 14, 22, 38, 518, 170, 266, 274, 530, 290, 546, 770, 28, 76, 140, 524, 84, 164, 548, 580, 644, 88, 280, 200, 584, 392, 648, 336, 592, 784, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_677, vertices_713, vertices_849, vertices_481, vertices_286, vertices_174, vertices_598, vertices_550, vertices_426, vertices_786, vertices_92, vertices_588, vertices_652, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_14, vertices_22, vertices_38, vertices_518, vertices_170, vertices_266, vertices_274, vertices_530, vertices_290, vertices_546, vertices_770, vertices_28, vertices_76, vertices_140, vertices_524, vertices_84, vertices_164, vertices_548, vertices_580, vertices_644, vertices_88, vertices_280, vertices_200, vertices_584, vertices_392, vertices_648, vertices_336, vertices_592, vertices_784, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_677), (false, vertices_713), (false, vertices_849), (false, vertices_481), (true, vertices_14), (true, vertices_22), (true, vertices_38), (true, vertices_518), (true, vertices_170), (true, vertices_266), (true, vertices_274), (true, vertices_530), (true, vertices_28), (true, vertices_76), (true, vertices_140), (true, vertices_524), (true, vertices_84), (true, vertices_580), (true, vertices_88), (true, vertices_280), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 23 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 17 else
  if p.val = (false, vertices_677) then 20 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_849) then 24 else
  if p.val = (false, vertices_481) then 26 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_170) then 18 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_140) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_84) then 11 else
  if p.val = (true, vertices_580) then 12 else
  if p.val = (true, vertices_88) then 13 else
  if p.val = (true, vertices_280) then 14 else
  if p.val = (true, vertices_392) then 15 else
  0
cert_priority
cert_nodeAtPriority_64 14 22 38 518 266 274 530 28 76 140 524 84 580 88 280 392 803 170 677 713 849 481
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 4 6 170
cert_row_4 1 0 1 3 5 8 598 22 3
cert_row_4 2 0 1 2 3 7 286 14 3
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 4 8 0 2
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 2 0 1 2 3 14 286 3
cert_coverFacet 1 174
cert_cover_5 1 0 0 1 2 4 14 174 3
cert_coverFacet 2 598
cert_cover_5 2 1 0 1 3 5 22 598 3
cert_coverFacet 3 550
cert_cover_2 3 1 0 4 8 38 550 3
cert_coverFacet 4 426
cert_cover_5 4 0 0 2 4 7 170 426 3
cert_coverFacet 5 786
cert_cover_2 5 3 0 7 8 274 786 3
cert_coverFacet 6 92
cert_cover_2 6 2 1 3 5 28 92 3
cert_coverFacet 7 588
cert_cover_2 7 2 1 5 8 76 588 3
cert_coverFacet 8 652
cert_cover_2 8 2 1 6 8 140 652 3
cert_coverFacet 9 472
cert_cover_5 9 3 2 3 5 6 88 472 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0907

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e10q1_0908.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0908

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [583, 555, 227, 301, 525, 341, 481, 722, 930, 668, 284, 596, 472, 808, 904, 35, 67, 515, 13, 69, 261, 517, 41, 521, 225, 289, 321, 162, 546, 194, 578, 642, 28, 268, 524, 84, 276, 532, 580, 152, 280, 296, 552, 392, 648, 776, 208, 336, 592, 656, 416, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_583, vertices_555, vertices_227, vertices_301, vertices_525, vertices_341, vertices_481, vertices_722, vertices_930, vertices_668, vertices_284, vertices_596, vertices_472, vertices_808, vertices_904] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_67, vertices_515, vertices_13, vertices_69, vertices_261, vertices_517, vertices_41, vertices_521, vertices_225, vertices_289, vertices_321, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_28, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_580, vertices_152, vertices_280, vertices_296, vertices_552, vertices_392, vertices_648, vertices_776, vertices_208, vertices_336, vertices_592, vertices_656, vertices_416, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_583), (false, vertices_555), (false, vertices_227), (false, vertices_301), (false, vertices_525), (false, vertices_341), (false, vertices_481), (true, vertices_642), (true, vertices_28), (true, vertices_532), (true, vertices_152), (true, vertices_280), (true, vertices_392), (true, vertices_648), (true, vertices_776), (true, vertices_208), (true, vertices_592), (true, vertices_656), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 21 22 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_583) then 15 else
  if p.val = (false, vertices_555) then 16 else
  if p.val = (false, vertices_227) then 23 else
  if p.val = (false, vertices_301) then 18 else
  if p.val = (false, vertices_525) then 0 else
  if p.val = (false, vertices_341) then 19 else
  if p.val = (false, vertices_481) then 24 else
  if p.val = (true, vertices_642) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_532) then 3 else
  if p.val = (true, vertices_152) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_392) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_776) then 8 else
  if p.val = (true, vertices_208) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_656) then 11 else
  if p.val = (true, vertices_800) then 12 else
  if p.val = (true, vertices_896) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 4 6 7 8 930 162 3
cert_row_4 1 0 3 5 6 8 722 194 1
cert_row_4 2 1 2 3 6 8 668 28 3
cert_row_4 3 2 3 5 6 7 472 152 2
cert_rows
cert_pivot_2 4 0 1 2
cert_heightProof 4
cert_coverFacet 0 722
cert_cover_5 0 1 0 3 5 6 194 722 1
cert_coverFacet 1 930
cert_cover_5 1 0 0 4 6 7 162 930 3
cert_coverFacet 2 668
cert_cover_5 2 2 1 2 3 6 28 668 3
cert_coverFacet 3 284
cert_cover_2 3 2 1 3 7 28 284 3
cert_coverFacet 4 596
cert_cover_2 4 3 1 5 8 84 596 3
cert_coverFacet 5 472
cert_cover_5 5 3 2 3 5 6 152 472 2
cert_coverFacet 6 808
cert_cover_2 6 4 2 7 8 296 808 3
cert_coverFacet 7 904
cert_cover_2 7 6 2 7 8 392 904 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0908

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e10q1_0909.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0909

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 805, 713, 689, 481, 94, 558, 342, 774, 586, 60, 436, 568, 472, 664, 161, 289, 545, 193, 321, 577, 641, 769, 14, 86, 262, 518, 74, 522, 322, 578, 770, 28, 44, 52, 276, 292, 548, 772, 56, 88, 152, 536, 552, 200, 584, 648, 176, 560, 336, 400, 656, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_805, vertices_713, vertices_689, vertices_481, vertices_94, vertices_558, vertices_342, vertices_774, vertices_586, vertices_60, vertices_436, vertices_568, vertices_472, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_14, vertices_86, vertices_262, vertices_518, vertices_74, vertices_522, vertices_322, vertices_578, vertices_770, vertices_28, vertices_44, vertices_52, vertices_276, vertices_292, vertices_548, vertices_772, vertices_56, vertices_88, vertices_152, vertices_536, vertices_552, vertices_200, vertices_584, vertices_648, vertices_176, vertices_560, vertices_336, vertices_400, vertices_656, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_805), (false, vertices_713), (false, vertices_689), (false, vertices_481), (true, vertices_14), (true, vertices_86), (true, vertices_262), (true, vertices_518), (true, vertices_74), (true, vertices_522), (true, vertices_28), (true, vertices_44), (true, vertices_52), (true, vertices_276), (true, vertices_56), (true, vertices_88), (true, vertices_152), (true, vertices_536), (true, vertices_552), (true, vertices_336), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 23 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 17 else
  if p.val = (false, vertices_805) then 20 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_689) then 24 else
  if p.val = (false, vertices_481) then 26 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_86) then 18 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_74) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_552) then 13 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_400) then 15 else
  0
cert_priority
cert_nodeAtPriority_64 14 262 518 74 522 28 44 52 276 56 88 152 536 552 336 400 835 86 805 713 689 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 8 558 14 3
cert_row_2 1 0 1 3 5 86
cert_row_4 2 1 3 4 6 7 436 52 3
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 8 0 1 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 1 0 1 2 3 14 94 3
cert_coverFacet 1 558
cert_cover_5 1 0 0 1 2 4 14 558 3
cert_coverFacet 2 342
cert_cover_5 2 1 0 1 3 7 86 342 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 586
cert_cover_2 4 2 0 5 8 74 586 3
cert_coverFacet 5 60
cert_cover_2 5 2 1 3 4 28 60 3
cert_coverFacet 6 436
cert_cover_5 6 2 1 3 4 6 52 436 3
cert_coverFacet 7 568
cert_cover_2 7 3 2 4 8 56 568 3
cert_coverFacet 8 472
cert_cover_5 8 3 2 3 5 6 88 472 3
cert_coverFacet 9 664
cert_cover_2 9 3 2 6 8 152 664 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0909

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e10q1_0910.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0910

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 653, 269, 357, 581, 313, 233, 838, 794, 690, 466, 780, 568, 680, 496, 13, 69, 261, 517, 41, 137, 265, 97, 289, 193, 577, 641, 146, 274, 530, 194, 322, 578, 642, 770, 268, 524, 324, 580, 772, 56, 280, 536, 168, 552, 648, 776, 176, 304, 560, 464, 224, 352, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_653, vertices_269, vertices_357, vertices_581, vertices_313, vertices_233, vertices_838, vertices_794, vertices_690, vertices_466, vertices_780, vertices_568, vertices_680, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_261, vertices_517, vertices_41, vertices_137, vertices_265, vertices_97, vertices_289, vertices_193, vertices_577, vertices_641, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_268, vertices_524, vertices_324, vertices_580, vertices_772, vertices_56, vertices_280, vertices_536, vertices_168, vertices_552, vertices_648, vertices_776, vertices_176, vertices_304, vertices_560, vertices_464, vertices_224, vertices_352, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_653), (false, vertices_269), (false, vertices_357), (false, vertices_581), (false, vertices_313), (false, vertices_233), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_322), (true, vertices_770), (true, vertices_772), (true, vertices_536), (true, vertices_552), (true, vertices_776), (true, vertices_176), (true, vertices_560), (true, vertices_464), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 19 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 15 else
  if p.val = (false, vertices_653) then 17 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_357) then 18 else
  if p.val = (false, vertices_581) then 1 else
  if p.val = (false, vertices_313) then 20 else
  if p.val = (false, vertices_233) then 21 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_464) then 23 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_269), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_581), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
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
cert_row_4 0 0 1 5 7 8 838 322 1
cert_row_2 1 3 5 6 7 464
cert_row_4 2 0 2 3 7 8 794 274 1
cert_row_4 3 0 3 4 6 8 690 146 2
cert_rows
cert_pivot_2 1 5 2 0
cert_heightProof 4
cert_coverFacet 0 838
cert_cover_5 0 0 0 1 5 7 322 838 1
cert_coverFacet 1 794
cert_cover_5 1 2 0 2 3 7 274 794 1
cert_coverFacet 2 690
cert_cover_5 2 3 0 3 4 6 146 690 2
cert_coverFacet 3 466
cert_cover_5 3 1 0 3 5 6 146 466 2
cert_coverFacet 4 780
cert_cover_2 4 2 1 7 8 268 780 3
cert_coverFacet 5 568
cert_cover_2 5 3 2 4 8 56 568 3
cert_coverFacet 6 680
cert_cover_2 6 4 2 6 8 168 680 3
cert_coverFacet 7 496
cert_cover_5 7 1 3 4 5 6 176 496 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0910

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e10q1_0916.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0916

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [355, 301, 653, 789, 617, 849, 662, 682, 626, 210, 418, 450, 396, 468, 424, 13, 261, 517, 41, 521, 785, 97, 289, 321, 577, 82, 146, 530, 98, 162, 290, 546, 194, 322, 386, 642, 140, 268, 148, 276, 532, 388, 644, 168, 296, 552, 392, 648, 208, 336, 592, 608, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_355, vertices_301, vertices_653, vertices_789, vertices_617, vertices_849, vertices_662, vertices_682, vertices_626, vertices_210, vertices_418, vertices_450, vertices_396, vertices_468, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_261, vertices_517, vertices_41, vertices_521, vertices_785, vertices_97, vertices_289, vertices_321, vertices_577, vertices_82, vertices_146, vertices_530, vertices_98, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_386, vertices_642, vertices_140, vertices_268, vertices_148, vertices_276, vertices_532, vertices_388, vertices_644, vertices_168, vertices_296, vertices_552, vertices_392, vertices_648, vertices_208, vertices_336, vertices_592, vertices_608, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_355), (false, vertices_301), (false, vertices_653), (false, vertices_789), (false, vertices_617), (false, vertices_849), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_162), (true, vertices_546), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_148), (true, vertices_388), (true, vertices_168), (true, vertices_392), (true, vertices_208), (true, vertices_416), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_355) then 16 else
  if p.val = (false, vertices_301) then 18 else
  if p.val = (false, vertices_653) then 19 else
  if p.val = (false, vertices_789) then 23 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_849) then 24 else
  if p.val = (true, vertices_82) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_416) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 8 682 162 1
cert_row_4 1 0 3 4 5 8 626 82 2
cert_row_4 2 0 1 3 6 8 662 146 1
cert_row_4 3 1 3 5 6 7 468 148 2
cert_rows
cert_pivot_2 2 4 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 2 0 1 3 6 146 662 1
cert_coverFacet 1 682
cert_cover_5 1 0 0 2 4 6 162 682 1
cert_coverFacet 2 626
cert_cover_5 2 1 0 3 4 5 82 626 2
cert_coverFacet 3 210
cert_cover_2 3 3 0 5 6 82 210 3
cert_coverFacet 4 418
cert_cover_2 4 4 0 6 7 162 418 3
cert_coverFacet 5 450
cert_cover_2 5 5 0 6 7 194 450 3
cert_coverFacet 6 396
cert_cover_2 6 2 1 6 7 140 396 3
cert_coverFacet 7 468
cert_cover_5 7 3 1 3 5 6 148 468 2
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0916

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e10q1_1018.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1018

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 779, 451, 213, 613, 865, 666, 394, 124, 820, 660, 312, 216, 792, 488, 131, 259, 515, 69, 133, 517, 609, 193, 321, 769, 138, 266, 522, 386, 642, 52, 84, 148, 532, 100, 548, 644, 56, 88, 152, 280, 536, 104, 296, 200, 392, 776, 304, 208, 656, 784, 352, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_779, vertices_451, vertices_213, vertices_613, vertices_865, vertices_666, vertices_394, vertices_124, vertices_820, vertices_660, vertices_312, vertices_216, vertices_792, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_69, vertices_133, vertices_517, vertices_609, vertices_193, vertices_321, vertices_769, vertices_138, vertices_266, vertices_522, vertices_386, vertices_642, vertices_52, vertices_84, vertices_148, vertices_532, vertices_100, vertices_548, vertices_644, vertices_56, vertices_88, vertices_152, vertices_280, vertices_536, vertices_104, vertices_296, vertices_200, vertices_392, vertices_776, vertices_304, vertices_208, vertices_656, vertices_784, vertices_352, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_779), (false, vertices_451), (false, vertices_213), (false, vertices_613), (false, vertices_865), (true, vertices_138), (true, vertices_52), (true, vertices_532), (true, vertices_56), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_104), (true, vertices_296), (true, vertices_200), (true, vertices_392), (true, vertices_304), (true, vertices_656), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 21 22 23 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 16 else
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_451) then 18 else
  if p.val = (false, vertices_213) then 20 else
  if p.val = (false, vertices_613) then 24 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_52) then 1 else
  if p.val = (true, vertices_532) then 2 else
  if p.val = (true, vertices_56) then 3 else
  if p.val = (true, vertices_88) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_104) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_656) then 13 else
  if p.val = (true, vertices_784) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 8 666 138 2
cert_row_4 1 1 3 4 7 8 820 52 3
cert_row_4 2 1 2 3 4 5 124 52 1
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 666
cert_cover_5 0 0 0 2 3 6 138 666 2
cert_coverFacet 1 394
cert_cover_2 1 2 0 6 7 138 394 3
cert_coverFacet 2 124
cert_cover_5 2 2 1 2 3 4 52 124 1
cert_coverFacet 3 820
cert_cover_5 3 1 1 3 4 7 52 820 3
cert_coverFacet 4 660
cert_cover_2 4 3 1 6 8 148 660 3
cert_coverFacet 5 312
cert_cover_2 5 3 2 4 7 56 312 3
cert_coverFacet 6 216
cert_cover_2 6 3 2 5 6 88 216 3
cert_coverFacet 7 792
cert_cover_2 7 3 2 7 8 280 792 3
cert_coverFacet 8 488
cert_cover_5 8 3 2 4 5 6 104 488 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1018

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m15e10q1_1039.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1039

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 61, 405, 677, 281, 617, 777, 362, 714, 778, 466, 628, 724, 312, 368, 21, 37, 133, 25, 41, 265, 521, 273, 545, 385, 641, 769, 74, 266, 522, 194, 322, 386, 642, 770, 52, 596, 148, 548, 644, 56, 280, 104, 296, 584, 776, 112, 304, 208, 336, 400, 352, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_61, vertices_405, vertices_677, vertices_281, vertices_617, vertices_777, vertices_362, vertices_714, vertices_778, vertices_466, vertices_628, vertices_724, vertices_312, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_133, vertices_25, vertices_41, vertices_265, vertices_521, vertices_273, vertices_545, vertices_385, vertices_641, vertices_769, vertices_74, vertices_266, vertices_522, vertices_194, vertices_322, vertices_386, vertices_642, vertices_770, vertices_52, vertices_596, vertices_148, vertices_548, vertices_644, vertices_56, vertices_280, vertices_104, vertices_296, vertices_584, vertices_776, vertices_112, vertices_304, vertices_208, vertices_336, vertices_400, vertices_352, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_61), (false, vertices_405), (false, vertices_677), (false, vertices_281), (false, vertices_617), (false, vertices_777), (true, vertices_74), (true, vertices_266), (true, vertices_522), (true, vertices_194), (true, vertices_322), (true, vertices_596), (true, vertices_296), (true, vertices_112), (true, vertices_304), (true, vertices_208), (true, vertices_336), (true, vertices_352), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 19 16 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 15 else
  if p.val = (false, vertices_61) then 17 else
  if p.val = (false, vertices_405) then 20 else
  if p.val = (false, vertices_677) then 21 else
  if p.val = (false, vertices_281) then 0 else
  if p.val = (false, vertices_617) then 18 else
  if p.val = (false, vertices_777) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_596) then 22 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_352) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_61), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_596), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 5 8 596
cert_row_4 1 0 2 4 5 7 362 74 2
cert_row_4 2 0 2 5 6 8 714 74 3
cert_row_4 3 0 3 5 6 7 466 194 1
cert_rows
cert_pivot_2 1 4 2 0
cert_heightProof 4
cert_coverFacet 0 362
cert_cover_5 0 1 0 2 4 5 74 362 2
cert_coverFacet 1 714
cert_cover_5 1 2 0 2 5 6 74 714 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 466
cert_cover_5 3 3 0 3 5 6 194 466 1
cert_coverFacet 4 628
cert_cover_5 4 0 1 3 4 5 52 628 3
cert_coverFacet 5 724
cert_cover_5 5 0 1 3 5 6 596 724 3
cert_coverFacet 6 312
cert_cover_2 6 3 2 4 7 56 312 3
cert_coverFacet 7 368
cert_cover_2 7 4 3 5 7 112 368 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1039

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m15e10q1_1056.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1056

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 805, 569, 409, 361, 897, 710, 346, 602, 402, 482, 620, 228, 420, 900, 25, 41, 265, 145, 529, 289, 545, 385, 641, 769, 90, 146, 274, 530, 194, 322, 578, 386, 642, 100, 164, 292, 548, 196, 580, 388, 644, 772, 280, 536, 104, 552, 328, 584, 400, 224, 352, 416, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_805, vertices_569, vertices_409, vertices_361, vertices_897, vertices_710, vertices_346, vertices_602, vertices_402, vertices_482, vertices_620, vertices_228, vertices_420, vertices_900] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_265, vertices_145, vertices_529, vertices_289, vertices_545, vertices_385, vertices_641, vertices_769, vertices_90, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_100, vertices_164, vertices_292, vertices_548, vertices_196, vertices_580, vertices_388, vertices_644, vertices_772, vertices_280, vertices_536, vertices_104, vertices_552, vertices_328, vertices_584, vertices_400, vertices_224, vertices_352, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_805), (false, vertices_569), (false, vertices_409), (false, vertices_361), (false, vertices_897), (true, vertices_90), (true, vertices_274), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_386), (true, vertices_100), (true, vertices_164), (true, vertices_196), (true, vertices_580), (true, vertices_388), (true, vertices_644), (true, vertices_584), (true, vertices_224), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 16 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_569) then 21 else
  if p.val = (false, vertices_409) then 22 else
  if p.val = (false, vertices_361) then 23 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_90) then 17 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_90), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 5 90
cert_row_4 1 0 4 5 6 7 482 194 1
cert_row_4 2 0 1 5 6 8 710 194 1
cert_row_4 3 1 2 4 5 8 620 100 1
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 2 0 1 5 6 194 710 1
cert_coverFacet 1 346
cert_cover_5 1 0 0 2 3 7 90 346 3
cert_coverFacet 2 602
cert_cover_5 2 0 0 2 3 8 90 602 3
cert_coverFacet 3 402
cert_cover_2 3 3 0 6 7 146 402 3
cert_coverFacet 4 482
cert_cover_5 4 1 0 4 5 6 194 482 1
cert_coverFacet 5 620
cert_cover_5 5 3 1 2 4 5 100 620 1
cert_coverFacet 6 228
cert_cover_2 6 4 1 5 6 100 228 3
cert_coverFacet 7 420
cert_cover_2 7 4 1 6 7 164 420 3
cert_coverFacet 8 900
cert_cover_2 8 6 1 7 8 388 900 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1056

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m15e10q1_1086.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1086

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 109, 597, 421, 773, 169, 713, 790, 154, 282, 426, 722, 372, 376, 216, 37, 69, 261, 517, 41, 73, 137, 161, 577, 385, 641, 769, 26, 138, 266, 146, 274, 530, 386, 642, 770, 84, 276, 532, 100, 292, 772, 88, 152, 280, 104, 168, 296, 200, 368, 208, 592, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_109, vertices_597, vertices_421, vertices_773, vertices_169, vertices_713, vertices_790, vertices_154, vertices_282, vertices_426, vertices_722, vertices_372, vertices_376, vertices_216] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_261, vertices_517, vertices_41, vertices_73, vertices_137, vertices_161, vertices_577, vertices_385, vertices_641, vertices_769, vertices_26, vertices_138, vertices_266, vertices_146, vertices_274, vertices_530, vertices_386, vertices_642, vertices_770, vertices_84, vertices_276, vertices_532, vertices_100, vertices_292, vertices_772, vertices_88, vertices_152, vertices_280, vertices_104, vertices_168, vertices_296, vertices_200, vertices_368, vertices_208, vertices_592, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_109), (false, vertices_597), (false, vertices_421), (false, vertices_773), (false, vertices_169), (false, vertices_713), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_276), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_296), (true, vertices_368), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 15 else
  if p.val = (false, vertices_109) then 17 else
  if p.val = (false, vertices_597) then 18 else
  if p.val = (false, vertices_421) then 19 else
  if p.val = (false, vertices_773) then 0 else
  if p.val = (false, vertices_169) then 1 else
  if p.val = (false, vertices_713) then 21 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_368) then 23 else
  if p.val = (true, vertices_208) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_773), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_169), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(true, vertices_368), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 7 8 790 274 1
cert_row_4 1 0 2 4 6 7 426 138 2
cert_row_2 2 3 4 5 7 368
cert_row_4 3 0 3 5 6 8 722 146 2
cert_rows
cert_pivot_2 1 2 4 0
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 426
cert_cover_5 3 1 0 2 4 6 138 426 2
cert_coverFacet 4 722
cert_cover_5 4 3 0 3 5 6 146 722 2
cert_coverFacet 5 372
cert_cover_5 5 2 1 3 4 5 84 372 2
cert_coverFacet 6 376
cert_cover_5 6 2 2 3 4 5 88 376 2
cert_coverFacet 7 216
cert_cover_2 7 3 2 5 6 88 216 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1086

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m15e10q1_1121.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1121

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [339, 173, 397, 789, 613, 361, 593, 902, 458, 690, 210, 786, 676, 248, 624, 141, 37, 261, 517, 41, 265, 81, 273, 529, 97, 321, 577, 82, 146, 274, 530, 194, 322, 386, 642, 770, 164, 548, 388, 644, 772, 104, 168, 200, 328, 392, 112, 176, 560, 208, 592, 784, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_173, vertices_397, vertices_789, vertices_613, vertices_361, vertices_593, vertices_902, vertices_458, vertices_690, vertices_210, vertices_786, vertices_676, vertices_248, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_141, vertices_37, vertices_261, vertices_517, vertices_41, vertices_265, vertices_81, vertices_273, vertices_529, vertices_97, vertices_321, vertices_577, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_386, vertices_642, vertices_770, vertices_164, vertices_548, vertices_388, vertices_644, vertices_772, vertices_104, vertices_168, vertices_200, vertices_328, vertices_392, vertices_112, vertices_176, vertices_560, vertices_208, vertices_592, vertices_784, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_173), (false, vertices_397), (false, vertices_789), (false, vertices_613), (false, vertices_361), (false, vertices_593), (true, vertices_146), (true, vertices_530), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_644), (true, vertices_200), (true, vertices_112), (true, vertices_176), (true, vertices_560), (true, vertices_208), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 20 16 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 15 else
  if p.val = (false, vertices_173) then 17 else
  if p.val = (false, vertices_397) then 18 else
  if p.val = (false, vertices_789) then 21 else
  if p.val = (false, vertices_613) then 22 else
  if p.val = (false, vertices_361) then 19 else
  if p.val = (false, vertices_593) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_593), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 16 => Sum.inl 2
  | 17 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 8 902 386 1
cert_row_4 1 0 2 5 6 7 458 194 1
cert_row_4 2 0 3 4 6 8 690 146 2
cert_row_4 3 2 3 4 5 6 248 104 1
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 0 0 1 6 7 386 902 1
cert_coverFacet 1 458
cert_cover_5 1 1 0 2 5 6 194 458 1
cert_coverFacet 2 690
cert_cover_5 2 2 0 3 4 6 146 690 2
cert_coverFacet 3 210
cert_cover_2 3 3 0 5 6 82 210 3
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 676
cert_cover_2 5 4 1 6 8 164 676 3
cert_coverFacet 6 248
cert_cover_5 6 3 2 3 4 5 104 248 1
cert_coverFacet 7 624
cert_cover_2 7 4 3 5 8 112 624 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1121

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m15e10q1_1161.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1161

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 397, 345, 665, 625, 449, 654, 614, 166, 370, 418, 450, 316, 572, 420, 25, 137, 265, 81, 529, 193, 321, 577, 385, 641, 38, 134, 518, 98, 162, 290, 194, 322, 578, 386, 642, 60, 140, 268, 524, 164, 292, 548, 388, 280, 536, 648, 112, 304, 560, 336, 608, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_397, vertices_345, vertices_665, vertices_625, vertices_449, vertices_654, vertices_614, vertices_166, vertices_370, vertices_418, vertices_450, vertices_316, vertices_572, vertices_420] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_265, vertices_81, vertices_529, vertices_193, vertices_321, vertices_577, vertices_385, vertices_641, vertices_38, vertices_134, vertices_518, vertices_98, vertices_162, vertices_290, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_60, vertices_140, vertices_268, vertices_524, vertices_164, vertices_292, vertices_548, vertices_388, vertices_280, vertices_536, vertices_648, vertices_112, vertices_304, vertices_560, vertices_336, vertices_608, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_397), (false, vertices_345), (false, vertices_665), (false, vertices_625), (false, vertices_449), (true, vertices_38), (true, vertices_134), (true, vertices_518), (true, vertices_98), (true, vertices_162), (true, vertices_290), (true, vertices_322), (true, vertices_386), (true, vertices_60), (true, vertices_524), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_304), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_397) then 18 else
  if p.val = (false, vertices_345) then 21 else
  if p.val = (false, vertices_665) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (false, vertices_449) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_60) then 19 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_164) then 10 else
  if p.val = (true, vertices_292) then 11 else
  if p.val = (true, vertices_548) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
cert_nodeAtPriority_65 449 2 38 1 134 3 518 98 162 290 322 386 524 164 292 548 304 416 707 397 60 345 665 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 134 2
cert_row_2 1 1 2 3 4 60
cert_row_4 2 0 1 4 5 8 614 38 3
cert_row_4 3 0 3 4 5 7 370 98 1
cert_rows
cert_pivot_2 6 2 1 0
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 134 654 2
cert_coverFacet 1 614
cert_cover_5 1 2 0 1 4 5 38 614 3
cert_coverFacet 2 166
cert_cover_2 2 1 0 4 6 38 166 3
cert_coverFacet 3 370
cert_cover_5 3 3 0 3 4 5 98 370 1
cert_coverFacet 4 418
cert_cover_2 4 4 0 6 7 162 418 3
cert_coverFacet 5 450
cert_cover_2 5 5 0 6 7 194 450 3
cert_coverFacet 6 316
cert_cover_5 6 1 1 2 3 7 60 316 3
cert_coverFacet 7 572
cert_cover_5 7 1 1 2 3 8 60 572 3
cert_coverFacet 8 420
cert_cover_2 8 4 1 6 7 164 420 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1161

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m15e10q1_1166.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1166

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 677, 901, 185, 793, 617, 790, 614, 326, 602, 210, 450, 236, 452, 216, 645, 25, 41, 521, 145, 273, 161, 545, 385, 769, 70, 262, 518, 82, 146, 274, 530, 194, 322, 578, 386, 100, 164, 548, 196, 324, 388, 772, 88, 152, 536, 104, 168, 200, 584, 208, 784, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_677, vertices_901, vertices_185, vertices_793, vertices_617, vertices_790, vertices_614, vertices_326, vertices_602, vertices_210, vertices_450, vertices_236, vertices_452, vertices_216] (by decide +kernel)
  polygons := literalFinset [vertices_645, vertices_25, vertices_41, vertices_521, vertices_145, vertices_273, vertices_161, vertices_545, vertices_385, vertices_769, vertices_70, vertices_262, vertices_518, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_386, vertices_100, vertices_164, vertices_548, vertices_196, vertices_324, vertices_388, vertices_772, vertices_88, vertices_152, vertices_536, vertices_104, vertices_168, vertices_200, vertices_584, vertices_208, vertices_784, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_677), (false, vertices_901), (false, vertices_185), (false, vertices_793), (false, vertices_617), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_82), (true, vertices_530), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_100), (true, vertices_196), (true, vertices_324), (true, vertices_88), (true, vertices_200), (true, vertices_208), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 16 else
  if p.val = (false, vertices_677) then 18 else
  if p.val = (false, vertices_901) then 19 else
  if p.val = (false, vertices_185) then 21 else
  if p.val = (false, vertices_793) then 22 else
  if p.val = (false, vertices_617) then 23 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_88) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
cert_nodeAtPriority_42 70 2 262 1 518 82 530 194 322 578 100 196 324 88 200 208 448 403 677 901 185 793 617
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 7 8 790 262 2
cert_row_4 1 0 2 3 5 8 602 82 1
cert_row_4 2 0 1 4 5 8 614 70 2
cert_row_4 3 1 2 4 5 6 236 100 1
cert_rows
cert_pivot_2 7 3 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 262 790 2
cert_coverFacet 1 614
cert_cover_5 1 2 0 1 4 5 70 614 2
cert_coverFacet 2 326
cert_cover_2 2 1 0 5 7 70 326 3
cert_coverFacet 3 602
cert_cover_5 3 1 0 2 3 5 82 602 1
cert_coverFacet 4 210
cert_cover_2 4 3 0 5 6 82 210 3
cert_coverFacet 5 450
cert_cover_2 5 5 0 6 7 194 450 3
cert_coverFacet 6 236
cert_cover_5 6 3 1 2 4 5 100 236 1
cert_coverFacet 7 452
cert_cover_2 7 5 1 6 7 196 452 3
cert_coverFacet 8 216
cert_cover_2 8 3 2 5 6 88 216 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1166

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e10q1_1171.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1171

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 405, 357, 709, 617, 417, 662, 570, 154, 362, 394, 418, 796, 844, 408, 69, 133, 261, 97, 161, 289, 545, 577, 385, 641, 26, 42, 138, 266, 146, 530, 162, 290, 546, 386, 642, 780, 148, 276, 532, 324, 580, 644, 152, 280, 536, 104, 552, 328, 584, 392, 400, 352, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_405, vertices_357, vertices_709, vertices_617, vertices_417, vertices_662, vertices_570, vertices_154, vertices_362, vertices_394, vertices_418, vertices_796, vertices_844, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_97, vertices_161, vertices_289, vertices_545, vertices_577, vertices_385, vertices_641, vertices_26, vertices_42, vertices_138, vertices_266, vertices_146, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_780, vertices_148, vertices_276, vertices_532, vertices_324, vertices_580, vertices_644, vertices_152, vertices_280, vertices_536, vertices_104, vertices_552, vertices_328, vertices_584, vertices_392, vertices_400, vertices_352, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_405), (false, vertices_357), (false, vertices_709), (false, vertices_617), (false, vertices_417), (true, vertices_26), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_146), (true, vertices_530), (true, vertices_290), (true, vertices_386), (true, vertices_780), (true, vertices_532), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_328), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 20 17 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_405) then 21 else
  if p.val = (false, vertices_357) then 22 else
  if p.val = (false, vertices_709) then 23 else
  if p.val = (false, vertices_617) then 18 else
  if p.val = (false, vertices_417) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_780) then 19 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_328) then 13 else
  if p.val = (true, vertices_392) then 14 else
  0
cert_priority
cert_nodeAtPriority_43 417 1 26 2 42 138 266 146 530 290 386 532 152 280 536 328 392 675 617 780 405 357 709
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 8 662 146 1
cert_row_2 1 1 2 7 8 780
cert_row_4 2 0 2 3 4 8 570 26 3
cert_row_4 3 0 2 4 5 7 362 42 3
cert_rows
cert_pivot_2 6 1 3 0
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 146 662 1
cert_coverFacet 1 570
cert_cover_5 1 2 0 2 3 4 26 570 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 362
cert_cover_5 3 3 0 2 4 5 42 362 3
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 796
cert_cover_5 6 1 1 2 3 7 780 796 2
cert_coverFacet 7 844
cert_cover_5 7 1 1 2 5 7 780 844 2
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1171

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e10q1_1202.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1202

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 403, 803, 117, 213, 549, 313, 842, 394, 650, 716, 868, 248, 408, 360, 131, 259, 515, 85, 37, 133, 517, 49, 145, 273, 289, 545, 138, 266, 522, 386, 642, 770, 100, 548, 196, 580, 644, 56, 152, 280, 104, 296, 200, 328, 584, 392, 648, 112, 208, 400, 352, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_403, vertices_803, vertices_117, vertices_213, vertices_549, vertices_313, vertices_842, vertices_394, vertices_650, vertices_716, vertices_868, vertices_248, vertices_408, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_85, vertices_37, vertices_133, vertices_517, vertices_49, vertices_145, vertices_273, vertices_289, vertices_545, vertices_138, vertices_266, vertices_522, vertices_386, vertices_642, vertices_770, vertices_100, vertices_548, vertices_196, vertices_580, vertices_644, vertices_56, vertices_152, vertices_280, vertices_104, vertices_296, vertices_200, vertices_328, vertices_584, vertices_392, vertices_648, vertices_112, vertices_208, vertices_400, vertices_352, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_403), (false, vertices_803), (false, vertices_117), (false, vertices_213), (false, vertices_549), (false, vertices_313), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_580), (true, vertices_152), (true, vertices_104), (true, vertices_200), (true, vertices_328), (true, vertices_584), (true, vertices_392), (true, vertices_648), (true, vertices_352), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 15 else
  if p.val = (false, vertices_403) then 16 else
  if p.val = (false, vertices_803) then 17 else
  if p.val = (false, vertices_117) then 19 else
  if p.val = (false, vertices_213) then 20 else
  if p.val = (false, vertices_549) then 0 else
  if p.val = (false, vertices_313) then 22 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_580) then 4 else
  if p.val = (true, vertices_152) then 5 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_328) then 8 else
  if p.val = (true, vertices_584) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_648) then 11 else
  if p.val = (true, vertices_352) then 12 else
  if p.val = (true, vertices_832) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_549), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
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
cert_row_4 0 0 2 5 7 8 842 266 2
cert_row_4 1 1 4 5 7 8 868 100 3
cert_row_4 2 1 2 5 6 8 716 196 1
cert_row_4 3 2 3 4 5 6 248 56 3
cert_rows
cert_pivot_2 0 7 1 2
cert_heightProof 4
cert_coverFacet 0 842
cert_cover_5 0 0 0 2 5 7 266 842 2
cert_coverFacet 1 394
cert_cover_2 1 2 0 6 7 138 394 3
cert_coverFacet 2 650
cert_cover_2 2 2 0 6 8 138 650 3
cert_coverFacet 3 716
cert_cover_5 3 2 1 2 5 6 196 716 1
cert_coverFacet 4 868
cert_cover_5 4 1 1 4 5 7 100 868 3
cert_coverFacet 5 248
cert_cover_5 5 3 2 3 4 5 56 248 3
cert_coverFacet 6 408
cert_cover_2 6 3 2 6 7 152 408 3
cert_coverFacet 7 360
cert_cover_2 7 4 2 5 7 104 360 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1202

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e10q1_1237.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1237

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 587, 613, 569, 409, 369, 710, 666, 394, 482, 820, 404, 660, 228, 420, 75, 25, 265, 521, 49, 273, 97, 545, 321, 577, 138, 266, 522, 194, 322, 578, 386, 642, 148, 276, 532, 100, 164, 292, 548, 196, 580, 388, 644, 152, 536, 392, 304, 560, 400, 656, 224, 352, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_587, vertices_613, vertices_569, vertices_409, vertices_369, vertices_710, vertices_666, vertices_394, vertices_482, vertices_820, vertices_404, vertices_660, vertices_228, vertices_420] (by decide +kernel)
  polygons := literalFinset [vertices_75, vertices_25, vertices_265, vertices_521, vertices_49, vertices_273, vertices_97, vertices_545, vertices_321, vertices_577, vertices_138, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_148, vertices_276, vertices_532, vertices_100, vertices_164, vertices_292, vertices_548, vertices_196, vertices_580, vertices_388, vertices_644, vertices_152, vertices_536, vertices_392, vertices_304, vertices_560, vertices_400, vertices_656, vertices_224, vertices_352, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_587), (false, vertices_613), (false, vertices_569), (false, vertices_409), (false, vertices_369), (true, vertices_138), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_164), (true, vertices_292), (true, vertices_196), (true, vertices_388), (true, vertices_644), (true, vertices_656), (true, vertices_224), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 16 else
  if p.val = (false, vertices_587) then 17 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_569) then 21 else
  if p.val = (false, vertices_409) then 22 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_194) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_148) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
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
cert_row_4 0 0 2 3 6 8 666 138 2
cert_row_4 1 1 3 4 7 8 820 276 2
cert_row_4 2 0 1 5 6 8 710 194 1
cert_row_4 3 0 4 5 6 7 482 194 1
cert_rows
cert_pivot_2 2 3 1 0
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 2 0 1 5 6 194 710 1
cert_coverFacet 1 666
cert_cover_5 1 0 0 2 3 6 138 666 2
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 482
cert_cover_5 3 3 0 4 5 6 194 482 1
cert_coverFacet 4 820
cert_cover_5 4 1 1 3 4 7 276 820 2
cert_coverFacet 5 404
cert_cover_2 5 3 1 6 7 148 404 3
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 228
cert_cover_2 7 4 1 5 6 100 228 3
cert_coverFacet 8 420
cert_cover_2 8 4 1 6 7 164 420 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1237

end
end BundlePart29
-- Explicit facial frame witnesses.

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_0480 : Certifies 480 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0685.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0481 : Certifies 481 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0702.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0482 : Certifies 482 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0704.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0483 : Certifies 483 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0707.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0484 : Certifies 484 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0711.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0485 : Certifies 485 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0715.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0486 : Certifies 486 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0745.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0487 : Certifies 487 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0791.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0488 : Certifies 488 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0808.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0489 : Certifies 489 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0809.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0490 : Certifies 490 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0810.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0491 : Certifies 491 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0864.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0492 : Certifies 492 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0871.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0493 : Certifies 493 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0896.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0494 : Certifies 494 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0903.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0495 : Certifies 495 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0907.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0496 : Certifies 496 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0908.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0497 : Certifies 497 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0909.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0498 : Certifies 498 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0910.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0499 : Certifies 499 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0916.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0500 : Certifies 500 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1018.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0501 : Certifies 501 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1039.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0502 : Certifies 502 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1056.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0503 : Certifies 503 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1086.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0504 : Certifies 504 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1121.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0505 : Certifies 505 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1161.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0506 : Certifies 506 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1166.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0507 : Certifies 507 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1171.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0508 : Certifies 508 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1202.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_0509 : Certifies 509 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_1237.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B016 (j : Fin 30) :
    Certifies (480 + j.val) := by
  fin_cases j
  · exact projection_0480
  · exact projection_0481
  · exact projection_0482
  · exact projection_0483
  · exact projection_0484
  · exact projection_0485
  · exact projection_0486
  · exact projection_0487
  · exact projection_0488
  · exact projection_0489
  · exact projection_0490
  · exact projection_0491
  · exact projection_0492
  · exact projection_0493
  · exact projection_0494
  · exact projection_0495
  · exact projection_0496
  · exact projection_0497
  · exact projection_0498
  · exact projection_0499
  · exact projection_0500
  · exact projection_0501
  · exact projection_0502
  · exact projection_0503
  · exact projection_0504
  · exact projection_0505
  · exact projection_0506
  · exact projection_0507
  · exact projection_0508
  · exact projection_0509

end Nonrational.TerminalVerification
