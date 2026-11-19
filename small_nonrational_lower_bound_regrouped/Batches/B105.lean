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
/- Source: ProjectionCertificates/R_m15e10q1_0588.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0588

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 397, 709, 217, 617, 777, 406, 662, 810, 370, 562, 344, 408, 360, 752, 133, 261, 517, 73, 137, 265, 521, 193, 577, 769, 150, 262, 518, 50, 274, 530, 290, 546, 770, 388, 644, 88, 152, 280, 104, 296, 552, 328, 392, 776, 112, 560, 208, 336, 400, 656, 352, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_397, vertices_709, vertices_217, vertices_617, vertices_777, vertices_406, vertices_662, vertices_810, vertices_370, vertices_562, vertices_344, vertices_408, vertices_360, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_265, vertices_521, vertices_193, vertices_577, vertices_769, vertices_150, vertices_262, vertices_518, vertices_50, vertices_274, vertices_530, vertices_290, vertices_546, vertices_770, vertices_388, vertices_644, vertices_88, vertices_152, vertices_280, vertices_104, vertices_296, vertices_552, vertices_328, vertices_392, vertices_776, vertices_112, vertices_560, vertices_208, vertices_336, vertices_400, vertices_656, vertices_352, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_397), (false, vertices_709), (false, vertices_217), (false, vertices_617), (false, vertices_777), (true, vertices_150), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_546), (true, vertices_280), (true, vertices_296), (true, vertices_328), (true, vertices_112), (true, vertices_560), (true, vertices_336), (true, vertices_400), (true, vertices_656), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 16 else
  if p.val = (false, vertices_397) then 19 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_217) then 22 else
  if p.val = (false, vertices_617) then 23 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (true, vertices_150) then 17 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_328) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_560) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_656) then 13 else
  if p.val = (true, vertices_352) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_150), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 6 150
cert_row_4 1 0 2 4 7 8 810 290 1
cert_row_4 2 0 3 4 5 7 370 50 3
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 0 0 1 3 7 150 406 3
cert_coverFacet 1 662
cert_cover_5 1 0 0 1 3 8 150 662 3
cert_coverFacet 2 810
cert_cover_5 2 1 0 2 4 7 290 810 1
cert_coverFacet 3 370
cert_cover_5 3 2 0 3 4 5 50 370 3
cert_coverFacet 4 562
cert_cover_2 4 3 0 4 8 50 562 3
cert_coverFacet 5 344
cert_cover_2 5 3 2 5 7 88 344 3
cert_coverFacet 6 408
cert_cover_2 6 3 2 6 7 152 408 3
cert_coverFacet 7 360
cert_cover_2 7 4 2 5 7 104 360 3
cert_coverFacet 8 752
cert_cover_5 8 3 3 4 5 6 112 752 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0588

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e10q1_0589.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0589

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [179, 781, 661, 421, 369, 785, 654, 618, 458, 562, 658, 482, 396, 856, 624, 133, 261, 517, 49, 145, 273, 529, 161, 289, 769, 74, 138, 522, 50, 146, 530, 98, 162, 546, 450, 642, 140, 268, 524, 388, 644, 328, 584, 392, 776, 112, 560, 336, 592, 656, 784, 352, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_179, vertices_781, vertices_661, vertices_421, vertices_369, vertices_785, vertices_654, vertices_618, vertices_458, vertices_562, vertices_658, vertices_482, vertices_396, vertices_856, vertices_624] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_49, vertices_145, vertices_273, vertices_529, vertices_161, vertices_289, vertices_769, vertices_74, vertices_138, vertices_522, vertices_50, vertices_146, vertices_530, vertices_98, vertices_162, vertices_546, vertices_450, vertices_642, vertices_140, vertices_268, vertices_524, vertices_388, vertices_644, vertices_328, vertices_584, vertices_392, vertices_776, vertices_112, vertices_560, vertices_336, vertices_592, vertices_656, vertices_784, vertices_352, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_179), (false, vertices_781), (false, vertices_661), (false, vertices_421), (false, vertices_369), (false, vertices_785), (true, vertices_74), (true, vertices_138), (true, vertices_522), (true, vertices_530), (true, vertices_98), (true, vertices_546), (true, vertices_450), (true, vertices_642), (true, vertices_140), (true, vertices_328), (true, vertices_584), (true, vertices_392), (true, vertices_560), (true, vertices_592), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_179) then 16 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_661) then 20 else
  if p.val = (false, vertices_421) then 21 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (false, vertices_785) then 0 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_450) then 17 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_608) then 14 else
  0
cert_priority
cert_nodeAtPriority_19 0 785 1 74 138 522 530 98 546 642 140 328 584 392 560 592 608 179 450 781 661 421 369
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 138 1
cert_row_2 1 0 5 6 7 450
cert_row_4 2 0 2 4 5 8 618 74 2
cert_row_4 3 2 3 5 7 8 856 328 1
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 138 654 1
cert_coverFacet 1 618
cert_cover_5 1 2 0 2 4 5 74 618 2
cert_coverFacet 2 458
cert_cover_5 2 1 0 2 5 6 74 458 3
cert_coverFacet 3 562
cert_cover_2 3 3 0 4 8 50 562 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 482
cert_cover_5 5 1 0 4 5 6 98 482 3
cert_coverFacet 6 396
cert_cover_2 6 2 1 6 7 140 396 3
cert_coverFacet 7 856
cert_cover_5 7 3 2 3 5 7 328 856 1
cert_coverFacet 8 624
cert_cover_2 8 4 3 5 8 112 624 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0589

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e10q1_0590.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0590

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [339, 597, 409, 681, 841, 657, 214, 230, 170, 810, 394, 402, 354, 692, 868, 137, 265, 521, 81, 145, 273, 529, 321, 577, 641, 198, 42, 138, 266, 82, 146, 274, 98, 162, 290, 322, 386, 84, 148, 532, 100, 164, 548, 580, 168, 552, 392, 776, 400, 656, 352, 672, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_597, vertices_409, vertices_681, vertices_841, vertices_657, vertices_214, vertices_230, vertices_170, vertices_810, vertices_394, vertices_402, vertices_354, vertices_692, vertices_868] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_81, vertices_145, vertices_273, vertices_529, vertices_321, vertices_577, vertices_641, vertices_198, vertices_42, vertices_138, vertices_266, vertices_82, vertices_146, vertices_274, vertices_98, vertices_162, vertices_290, vertices_322, vertices_386, vertices_84, vertices_148, vertices_532, vertices_100, vertices_164, vertices_548, vertices_580, vertices_168, vertices_552, vertices_392, vertices_776, vertices_400, vertices_656, vertices_352, vertices_672, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_597), (false, vertices_409), (false, vertices_681), (false, vertices_841), (false, vertices_657), (true, vertices_198), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_146), (true, vertices_98), (true, vertices_162), (true, vertices_290), (true, vertices_386), (true, vertices_148), (true, vertices_100), (true, vertices_164), (true, vertices_548), (true, vertices_352), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 16 else
  if p.val = (false, vertices_597) then 19 else
  if p.val = (false, vertices_409) then 21 else
  if p.val = (false, vertices_681) then 22 else
  if p.val = (false, vertices_841) then 23 else
  if p.val = (false, vertices_657) then 0 else
  if p.val = (true, vertices_198) then 17 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_100) then 10 else
  if p.val = (true, vertices_164) then 11 else
  if p.val = (true, vertices_548) then 12 else
  if p.val = (true, vertices_352) then 13 else
  if p.val = (true, vertices_800) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_657), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_198), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 7 8 810 42 3
cert_row_2 1 0 1 5 6 198
cert_row_4 2 1 3 4 6 8 692 148 2
cert_row_4 3 1 4 5 7 8 868 100 3
cert_rows
cert_pivot_2 2 0 3 1
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 1 0 1 3 5 198 214 2
cert_coverFacet 1 230
cert_cover_5 1 1 0 1 4 5 198 230 2
cert_coverFacet 2 170
cert_cover_2 2 2 0 4 6 42 170 3
cert_coverFacet 3 810
cert_cover_5 3 0 0 2 4 7 42 810 3
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 354
cert_cover_2 6 4 0 5 7 98 354 3
cert_coverFacet 7 692
cert_cover_5 7 2 1 3 4 6 148 692 2
cert_coverFacet 8 868
cert_cover_5 8 3 1 4 5 7 100 868 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0590

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e10q1_0591.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0591

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 707, 387, 405, 101, 677, 617, 842, 690, 402, 786, 124, 348, 180, 824, 67, 131, 259, 37, 69, 133, 261, 97, 545, 577, 385, 641, 146, 274, 530, 322, 578, 386, 642, 770, 92, 52, 148, 276, 100, 164, 324, 56, 280, 104, 552, 328, 584, 776, 176, 560, 400, 784, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_707, vertices_387, vertices_405, vertices_101, vertices_677, vertices_617, vertices_842, vertices_690, vertices_402, vertices_786, vertices_124, vertices_348, vertices_180, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_37, vertices_69, vertices_133, vertices_261, vertices_97, vertices_545, vertices_577, vertices_385, vertices_641, vertices_146, vertices_274, vertices_530, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_92, vertices_52, vertices_148, vertices_276, vertices_100, vertices_164, vertices_324, vertices_56, vertices_280, vertices_104, vertices_552, vertices_328, vertices_584, vertices_776, vertices_176, vertices_560, vertices_400, vertices_784, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_707), (false, vertices_387), (false, vertices_405), (false, vertices_101), (false, vertices_677), (false, vertices_617), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_770), (true, vertices_92), (true, vertices_52), (true, vertices_56), (true, vertices_280), (true, vertices_328), (true, vertices_776), (true, vertices_176), (true, vertices_560), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 15 else
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_405) then 18 else
  if p.val = (false, vertices_101) then 1 else
  if p.val = (false, vertices_677) then 19 else
  if p.val = (false, vertices_617) then 22 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_92) then 20 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_776) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_784) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_387), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_101), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_92), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
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
cert_row_4 1 0 2 5 7 8 842 322 1
cert_row_4 2 0 3 4 6 8 690 146 2
cert_row_4 3 2 3 4 7 8 824 56 3
cert_rows
cert_pivot_2 1 5 0 2
cert_heightProof 4
cert_coverFacet 0 842
cert_cover_5 0 1 0 2 5 7 322 842 1
cert_coverFacet 1 690
cert_cover_5 1 2 0 3 4 6 146 690 2
cert_coverFacet 2 402
cert_cover_2 2 3 0 6 7 146 402 3
cert_coverFacet 3 786
cert_cover_2 3 3 0 7 8 274 786 3
cert_coverFacet 4 124
cert_cover_5 4 0 1 2 3 4 92 124 3
cert_coverFacet 5 348
cert_cover_5 5 0 1 2 3 7 92 348 3
cert_coverFacet 6 180
cert_cover_2 6 3 1 4 6 52 180 3
cert_coverFacet 7 824
cert_cover_5 7 3 2 3 4 7 56 824 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0591

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e10q1_0592.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0592

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 611, 195, 597, 277, 453, 409, 358, 426, 674, 450, 796, 812, 612, 696, 67, 131, 515, 21, 69, 261, 145, 273, 529, 193, 577, 385, 98, 162, 290, 546, 194, 322, 386, 642, 780, 276, 532, 100, 292, 548, 324, 580, 152, 280, 536, 168, 296, 552, 392, 656, 608, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_611, vertices_195, vertices_597, vertices_277, vertices_453, vertices_409, vertices_358, vertices_426, vertices_674, vertices_450, vertices_796, vertices_812, vertices_612, vertices_696] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_515, vertices_21, vertices_69, vertices_261, vertices_145, vertices_273, vertices_529, vertices_193, vertices_577, vertices_385, vertices_98, vertices_162, vertices_290, vertices_546, vertices_194, vertices_322, vertices_386, vertices_642, vertices_780, vertices_276, vertices_532, vertices_100, vertices_292, vertices_548, vertices_324, vertices_580, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_552, vertices_392, vertices_656, vertices_608, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_611), (false, vertices_195), (false, vertices_597), (false, vertices_277), (false, vertices_453), (false, vertices_409), (true, vertices_162), (true, vertices_290), (true, vertices_322), (true, vertices_386), (true, vertices_780), (true, vertices_100), (true, vertices_292), (true, vertices_548), (true, vertices_536), (true, vertices_168), (true, vertices_296), (true, vertices_552), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 15 else
  if p.val = (false, vertices_611) then 16 else
  if p.val = (false, vertices_195) then 0 else
  if p.val = (false, vertices_597) then 18 else
  if p.val = (false, vertices_277) then 1 else
  if p.val = (false, vertices_453) then 19 else
  if p.val = (false, vertices_409) then 22 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_780) then 20 else
  if p.val = (true, vertices_100) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_195), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_277), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_780), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 5 7 358 98 1
cert_row_2 1 1 2 7 8 780
cert_row_4 2 0 2 4 6 7 426 162 1
cert_row_4 3 2 3 4 6 8 696 152 2
cert_rows
cert_pivot_2 5 1 0 2
cert_heightProof 4
cert_coverFacet 0 358
cert_cover_5 0 0 0 1 4 5 98 358 1
cert_coverFacet 1 426
cert_cover_5 1 2 0 2 4 6 162 426 1
cert_coverFacet 2 674
cert_cover_2 2 4 0 6 8 162 674 3
cert_coverFacet 3 450
cert_cover_2 3 5 0 6 7 194 450 3
cert_coverFacet 4 796
cert_cover_5 4 1 1 2 3 7 780 796 2
cert_coverFacet 5 812
cert_cover_5 5 1 1 2 4 7 780 812 2
cert_coverFacet 6 612
cert_cover_2 6 4 1 5 8 100 612 3
cert_coverFacet 7 696
cert_cover_5 7 3 2 3 4 6 152 696 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0592

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e10q1_0593.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0593

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 611, 291, 229, 601, 425, 201, 678, 902, 418, 796, 628, 212, 404, 472, 35, 259, 515, 73, 137, 265, 521, 97, 161, 289, 193, 577, 646, 162, 290, 546, 386, 770, 84, 148, 276, 532, 100, 164, 548, 196, 388, 772, 88, 280, 536, 200, 392, 776, 208, 592, 400, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_611, vertices_291, vertices_229, vertices_601, vertices_425, vertices_201, vertices_678, vertices_902, vertices_418, vertices_796, vertices_628, vertices_212, vertices_404, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_259, vertices_515, vertices_73, vertices_137, vertices_265, vertices_521, vertices_97, vertices_161, vertices_289, vertices_193, vertices_577, vertices_646, vertices_162, vertices_290, vertices_546, vertices_386, vertices_770, vertices_84, vertices_148, vertices_276, vertices_532, vertices_100, vertices_164, vertices_548, vertices_196, vertices_388, vertices_772, vertices_88, vertices_280, vertices_536, vertices_200, vertices_392, vertices_776, vertices_208, vertices_592, vertices_400, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_611), (false, vertices_291), (false, vertices_229), (false, vertices_601), (false, vertices_425), (false, vertices_201), (true, vertices_646), (true, vertices_162), (true, vertices_386), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_548), (true, vertices_388), (true, vertices_772), (true, vertices_280), (true, vertices_208), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 14 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_611) then 19 else
  if p.val = (false, vertices_291) then 0 else
  if p.val = (false, vertices_229) then 15 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (false, vertices_201) then 1 else
  if p.val = (true, vertices_646) then 16 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_400) then 13 else
  0
cert_priority
cert_nodeAtPriority_25 1 291 0 201 162 386 84 148 276 532 548 388 772 280 208 400 229 646 779 611 601 425
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 8 646
cert_row_4 1 1 3 4 5 8 628 84 2
cert_row_4 2 1 2 3 7 8 796 276 1
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 0 4 1 2
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 646 678 2
cert_coverFacet 1 902
cert_cover_5 1 0 0 1 6 7 646 902 3
cert_coverFacet 2 418
cert_cover_2 2 4 0 6 7 162 418 3
cert_coverFacet 3 796
cert_cover_5 3 2 1 2 3 7 276 796 1
cert_coverFacet 4 628
cert_cover_5 4 1 1 3 4 5 84 628 2
cert_coverFacet 5 212
cert_cover_2 5 3 1 5 6 84 212 3
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 472
cert_cover_5 7 3 2 3 5 6 88 472 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0593

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e10q1_0594.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0594

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 341, 789, 665, 457, 241, 806, 426, 650, 626, 178, 658, 596, 484, 612, 277, 137, 265, 521, 81, 145, 529, 193, 321, 769, 138, 266, 522, 50, 146, 530, 162, 290, 546, 642, 770, 84, 532, 100, 292, 548, 324, 580, 772, 392, 648, 112, 176, 592, 656, 224, 608, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_341, vertices_789, vertices_665, vertices_457, vertices_241, vertices_806, vertices_426, vertices_650, vertices_626, vertices_178, vertices_658, vertices_596, vertices_484, vertices_612] (by decide +kernel)
  polygons := literalFinset [vertices_277, vertices_137, vertices_265, vertices_521, vertices_81, vertices_145, vertices_529, vertices_193, vertices_321, vertices_769, vertices_138, vertices_266, vertices_522, vertices_50, vertices_146, vertices_530, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_84, vertices_532, vertices_100, vertices_292, vertices_548, vertices_324, vertices_580, vertices_772, vertices_392, vertices_648, vertices_112, vertices_176, vertices_592, vertices_656, vertices_224, vertices_608, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_341), (false, vertices_789), (false, vertices_665), (false, vertices_457), (false, vertices_241), (true, vertices_138), (true, vertices_50), (true, vertices_146), (true, vertices_530), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_642), (true, vertices_100), (true, vertices_292), (true, vertices_548), (true, vertices_580), (true, vertices_592), (true, vertices_608), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_341) then 18 else
  if p.val = (false, vertices_789) then 19 else
  if p.val = (false, vertices_665) then 21 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (false, vertices_241) then 24 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_608) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
cert_nodeAtPriority_52 138 1 50 2 146 530 162 290 546 642 100 292 548 580 592 608 416 779 341 789 665 457 241
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 7 426 138 2
cert_row_4 1 0 3 4 5 8 626 50 3
cert_row_4 2 0 1 4 7 8 806 290 1
cert_row_4 3 1 4 5 6 7 484 100 3
cert_rows
cert_pivot_2 2 3 0 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 2 0 1 4 7 290 806 1
cert_coverFacet 1 426
cert_cover_5 1 0 0 2 4 6 138 426 2
cert_coverFacet 2 650
cert_cover_2 2 2 0 6 8 138 650 3
cert_coverFacet 3 626
cert_cover_5 3 1 0 3 4 5 50 626 3
cert_coverFacet 4 178
cert_cover_2 4 3 0 4 6 50 178 3
cert_coverFacet 5 658
cert_cover_2 5 3 0 6 8 146 658 3
cert_coverFacet 6 596
cert_cover_2 6 3 1 5 8 84 596 3
cert_coverFacet 7 484
cert_cover_5 7 3 1 4 5 6 100 484 3
cert_coverFacet 8 612
cert_cover_2 8 4 1 5 8 100 612 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0594

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e10q1_0595.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0595

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 661, 569, 425, 649, 369, 209, 214, 614, 390, 774, 810, 354, 908, 628, 41, 137, 521, 49, 81, 145, 529, 289, 193, 321, 385, 641, 70, 134, 262, 518, 98, 290, 546, 194, 322, 386, 770, 84, 148, 532, 612, 388, 644, 772, 296, 552, 392, 648, 776, 112, 560, 208, 352]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_661, vertices_569, vertices_425, vertices_649, vertices_369, vertices_209, vertices_214, vertices_614, vertices_390, vertices_774, vertices_810, vertices_354, vertices_908, vertices_628] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_137, vertices_521, vertices_49, vertices_81, vertices_145, vertices_529, vertices_289, vertices_193, vertices_321, vertices_385, vertices_641, vertices_70, vertices_134, vertices_262, vertices_518, vertices_98, vertices_290, vertices_546, vertices_194, vertices_322, vertices_386, vertices_770, vertices_84, vertices_148, vertices_532, vertices_612, vertices_388, vertices_644, vertices_772, vertices_296, vertices_552, vertices_392, vertices_648, vertices_776, vertices_112, vertices_560, vertices_208, vertices_352] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_661), (false, vertices_569), (false, vertices_425), (false, vertices_649), (false, vertices_369), (false, vertices_209), (true, vertices_70), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_84), (true, vertices_612), (true, vertices_388), (true, vertices_772), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 19 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 15 else
  if p.val = (false, vertices_661) then 17 else
  if p.val = (false, vertices_569) then 20 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_649) then 0 else
  if p.val = (false, vertices_369) then 23 else
  if p.val = (false, vertices_209) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_262) then 4 else
  if p.val = (true, vertices_518) then 5 else
  if p.val = (true, vertices_98) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_770) then 9 else
  if p.val = (true, vertices_84) then 10 else
  if p.val = (true, vertices_612) then 18 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_772) then 12 else
  if p.val = (true, vertices_776) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_649), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_209), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_612), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
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
cert_row_4 0 0 1 3 5 6 214 70 2
cert_row_2 1 1 4 5 8 612
cert_row_4 2 0 2 4 7 8 810 290 1
cert_row_4 3 1 2 6 7 8 908 388 1
cert_rows
cert_pivot_2 3 5 0 1
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 5 70 214 2
cert_coverFacet 1 614
cert_cover_5 1 1 0 1 4 5 70 614 2
cert_coverFacet 2 390
cert_cover_2 2 1 0 6 7 134 390 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 810
cert_cover_5 4 2 0 2 4 7 290 810 1
cert_coverFacet 5 354
cert_cover_2 5 4 0 5 7 98 354 3
cert_coverFacet 6 908
cert_cover_5 6 3 1 2 6 7 388 908 1
cert_coverFacet 7 628
cert_cover_5 7 1 1 3 4 5 84 628 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0595

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e10q1_0596.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0596

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 597, 233, 817, 465, 609, 286, 590, 806, 618, 170, 394, 220, 788, 408, 81, 273, 529, 97, 161, 289, 545, 193, 577, 385, 14, 262, 518, 42, 586, 138, 266, 162, 290, 546, 386, 28, 76, 84, 276, 532, 580, 772, 152, 280, 104, 168, 200, 392, 208, 400, 784, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_597, vertices_233, vertices_817, vertices_465, vertices_609, vertices_286, vertices_590, vertices_806, vertices_618, vertices_170, vertices_394, vertices_220, vertices_788, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_273, vertices_529, vertices_97, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_14, vertices_262, vertices_518, vertices_42, vertices_586, vertices_138, vertices_266, vertices_162, vertices_290, vertices_546, vertices_386, vertices_28, vertices_76, vertices_84, vertices_276, vertices_532, vertices_580, vertices_772, vertices_152, vertices_280, vertices_104, vertices_168, vertices_200, vertices_392, vertices_208, vertices_400, vertices_784, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_597), (false, vertices_233), (false, vertices_817), (false, vertices_465), (false, vertices_609), (true, vertices_14), (true, vertices_262), (true, vertices_518), (true, vertices_42), (true, vertices_586), (true, vertices_138), (true, vertices_266), (true, vertices_546), (true, vertices_28), (true, vertices_76), (true, vertices_276), (true, vertices_772), (true, vertices_152), (true, vertices_280), (true, vertices_392)] (by decide +kernel)
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
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_586) then 17 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_76) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_280) then 13 else
  if p.val = (true, vertices_392) then 14 else
  0
cert_priority
cert_nodeAtPriority_40 609 14 262 518 42 138 266 546 28 76 276 772 152 280 392 419 586 597 233 817 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 7 8 806 262 2
cert_row_2 1 0 2 5 8 586
cert_row_4 2 0 1 2 3 7 286 14 3
cert_row_4 3 1 2 3 5 6 220 28 3
cert_rows
cert_pivot_2 4 8 0 1
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 2 0 1 2 3 14 286 3
cert_coverFacet 1 590
cert_cover_5 1 1 0 1 2 5 14 590 3
cert_coverFacet 2 806
cert_cover_5 2 0 0 1 4 7 262 806 2
cert_coverFacet 3 618
cert_cover_5 3 1 0 2 4 5 42 618 3
cert_coverFacet 4 170
cert_cover_2 4 2 0 4 6 42 170 3
cert_coverFacet 5 394
cert_cover_2 5 2 0 6 7 138 394 3
cert_coverFacet 6 220
cert_cover_5 6 3 1 2 3 5 28 220 3
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0596

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m15e10q1_0597.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0597

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 613, 569, 433, 849, 225, 206, 270, 838, 186, 282, 402, 796, 236, 556, 49, 273, 529, 97, 161, 545, 193, 321, 577, 385, 14, 70, 262, 26, 138, 266, 146, 274, 194, 322, 386, 44, 204, 268, 524, 100, 548, 580, 772, 56, 280, 536, 168, 552, 176, 400, 784, 224, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_613, vertices_569, vertices_433, vertices_849, vertices_225, vertices_206, vertices_270, vertices_838, vertices_186, vertices_282, vertices_402, vertices_796, vertices_236, vertices_556] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_273, vertices_529, vertices_97, vertices_161, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_14, vertices_70, vertices_262, vertices_26, vertices_138, vertices_266, vertices_146, vertices_274, vertices_194, vertices_322, vertices_386, vertices_44, vertices_204, vertices_268, vertices_524, vertices_100, vertices_548, vertices_580, vertices_772, vertices_56, vertices_280, vertices_536, vertices_168, vertices_552, vertices_176, vertices_400, vertices_784, vertices_224, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_613), (false, vertices_569), (false, vertices_433), (false, vertices_849), (false, vertices_225), (true, vertices_14), (true, vertices_70), (true, vertices_262), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_146), (true, vertices_274), (true, vertices_44), (true, vertices_204), (true, vertices_268), (true, vertices_524), (true, vertices_772), (true, vertices_280), (true, vertices_168)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 16 else
  if p.val = (false, vertices_613) then 18 else
  if p.val = (false, vertices_569) then 21 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (false, vertices_849) then 24 else
  if p.val = (false, vertices_225) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_146) then 7 else
  if p.val = (true, vertices_274) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_204) then 19 else
  if p.val = (true, vertices_268) then 10 else
  if p.val = (true, vertices_524) then 11 else
  if p.val = (true, vertices_772) then 12 else
  if p.val = (true, vertices_280) then 13 else
  if p.val = (true, vertices_168) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_225), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 6 186 26 3
cert_row_2 1 1 2 5 6 204
cert_row_4 2 0 1 5 7 8 838 70 3
cert_row_4 3 1 2 3 7 8 796 268 2
cert_rows
cert_pivot_2 4 6 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 5 14 206 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 838
cert_cover_5 2 2 0 1 5 7 70 838 3
cert_coverFacet 3 186
cert_cover_5 3 0 0 2 3 4 26 186 3
cert_coverFacet 4 282
cert_cover_2 4 2 0 3 7 26 282 3
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 796
cert_cover_5 6 3 1 2 3 7 268 796 2
cert_coverFacet 7 236
cert_cover_5 7 1 1 2 4 5 44 236 3
cert_coverFacet 8 556
cert_cover_2 8 2 1 4 8 44 556 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0597

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m15e10q1_0598.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0598

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 805, 453, 361, 625, 705, 158, 782, 58, 810, 562, 722, 396, 248, 456, 133, 261, 517, 97, 289, 545, 193, 321, 577, 641, 14, 134, 518, 26, 42, 778, 50, 146, 530, 546, 642, 140, 268, 388, 772, 56, 152, 104, 296, 200, 328, 392, 112, 560, 208, 592, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_805, vertices_453, vertices_361, vertices_625, vertices_705, vertices_158, vertices_782, vertices_58, vertices_810, vertices_562, vertices_722, vertices_396, vertices_248, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_97, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_641, vertices_14, vertices_134, vertices_518, vertices_26, vertices_42, vertices_778, vertices_50, vertices_146, vertices_530, vertices_546, vertices_642, vertices_140, vertices_268, vertices_388, vertices_772, vertices_56, vertices_152, vertices_104, vertices_296, vertices_200, vertices_328, vertices_392, vertices_112, vertices_560, vertices_208, vertices_592, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_805), (false, vertices_453), (false, vertices_361), (false, vertices_625), (false, vertices_705), (true, vertices_14), (true, vertices_26), (true, vertices_42), (true, vertices_778), (true, vertices_50), (true, vertices_146), (true, vertices_530), (true, vertices_546), (true, vertices_140), (true, vertices_268), (true, vertices_56), (true, vertices_152), (true, vertices_200), (true, vertices_392), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 16 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_453) then 20 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (false, vertices_705) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_778) then 17 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_208) then 14 else
  0
cert_priority
cert_nodeAtPriority_22 705 14 26 42 50 146 530 546 140 268 56 152 200 392 208 647 778 805 453 361 625
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 7 8 778
cert_row_4 1 0 1 2 3 6 158 14 3
cert_row_4 2 0 3 5 6 8 722 146 2
cert_row_4 3 2 3 4 5 6 248 56 3
cert_rows
cert_pivot_2 7 1 0 2
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 1 0 1 2 3 14 158 3
cert_coverFacet 1 782
cert_cover_5 1 0 0 1 2 7 14 782 3
cert_coverFacet 2 58
cert_cover_2 2 2 0 3 4 26 58 3
cert_coverFacet 3 810
cert_cover_5 3 0 0 2 4 7 42 810 3
cert_coverFacet 4 562
cert_cover_2 4 3 0 4 8 50 562 3
cert_coverFacet 5 722
cert_cover_5 5 2 0 3 5 6 146 722 2
cert_coverFacet 6 396
cert_cover_2 6 2 1 6 7 140 396 3
cert_coverFacet 7 248
cert_cover_5 7 3 2 3 4 5 56 248 3
cert_coverFacet 8 456
cert_cover_2 8 5 2 6 7 200 456 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0598

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m15e10q1_0599.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0599

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [535, 275, 771, 157, 781, 425, 465, 810, 626, 338, 482, 172, 556, 724, 740, 19, 259, 515, 13, 21, 517, 137, 265, 145, 273, 385, 769, 82, 274, 530, 98, 290, 546, 322, 770, 44, 140, 524, 148, 532, 164, 548, 708, 168, 296, 552, 776, 208, 336, 592, 224, 608, 416, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_535, vertices_275, vertices_771, vertices_157, vertices_781, vertices_425, vertices_465, vertices_810, vertices_626, vertices_338, vertices_482, vertices_172, vertices_556, vertices_724, vertices_740] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_259, vertices_515, vertices_13, vertices_21, vertices_517, vertices_137, vertices_265, vertices_145, vertices_273, vertices_385, vertices_769, vertices_82, vertices_274, vertices_530, vertices_98, vertices_290, vertices_546, vertices_322, vertices_770, vertices_44, vertices_140, vertices_524, vertices_148, vertices_532, vertices_164, vertices_548, vertices_708, vertices_168, vertices_296, vertices_552, vertices_776, vertices_208, vertices_336, vertices_592, vertices_224, vertices_608, vertices_416, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_535), (false, vertices_275), (false, vertices_771), (false, vertices_157), (false, vertices_781), (false, vertices_425), (false, vertices_465), (true, vertices_82), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_322), (true, vertices_44), (true, vertices_164), (true, vertices_548), (true, vertices_708), (true, vertices_552), (true, vertices_592), (true, vertices_224), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_535) then 15 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_771) then 1 else
  if p.val = (false, vertices_157) then 17 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_44) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_708) then 19 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_608) then 13 else
  0
cert_priority
cert_nodeAtPriority_54 275 771 82 98 290 546 322 44 164 548 552 592 224 608 535 157 781 708 425 465
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 5 6 8 708
cert_row_4 1 0 2 4 7 8 810 290 1
cert_row_4 2 0 3 4 5 8 626 82 2
cert_row_4 3 0 4 5 6 7 482 98 3
cert_rows
cert_pivot_2 1 2 3 0
cert_heightProof 4
cert_coverFacet 0 810
cert_cover_5 0 1 0 2 4 7 290 810 1
cert_coverFacet 1 626
cert_cover_5 1 2 0 3 4 5 82 626 2
cert_coverFacet 2 338
cert_cover_2 2 3 0 5 7 82 338 3
cert_coverFacet 3 482
cert_cover_5 3 3 0 4 5 6 98 482 3
cert_coverFacet 4 172
cert_cover_2 4 2 1 4 6 44 172 3
cert_coverFacet 5 556
cert_cover_2 5 2 1 4 8 44 556 3
cert_coverFacet 6 724
cert_cover_5 6 0 1 3 5 6 148 724 2
cert_coverFacet 7 740
cert_cover_5 7 0 1 4 5 6 164 740 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0599

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m15e10q1_0600.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0600

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 595, 355, 569, 241, 801, 398, 198, 582, 450, 220, 604, 812, 440, 480, 67, 259, 515, 49, 81, 529, 97, 289, 545, 769, 70, 134, 262, 518, 194, 322, 578, 386, 92, 140, 268, 524, 196, 580, 772, 56, 152, 536, 296, 552, 392, 176, 208, 592, 224, 352, 416, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_595, vertices_355, vertices_569, vertices_241, vertices_801, vertices_398, vertices_198, vertices_582, vertices_450, vertices_220, vertices_604, vertices_812, vertices_440, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_49, vertices_81, vertices_529, vertices_97, vertices_289, vertices_545, vertices_769, vertices_70, vertices_134, vertices_262, vertices_518, vertices_194, vertices_322, vertices_578, vertices_386, vertices_92, vertices_140, vertices_268, vertices_524, vertices_196, vertices_580, vertices_772, vertices_56, vertices_152, vertices_536, vertices_296, vertices_552, vertices_392, vertices_176, vertices_208, vertices_592, vertices_224, vertices_352, vertices_416, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_595), (false, vertices_355), (false, vertices_569), (false, vertices_241), (false, vertices_801), (true, vertices_70), (true, vertices_134), (true, vertices_194), (true, vertices_386), (true, vertices_92), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_196), (true, vertices_580), (true, vertices_152), (true, vertices_296), (true, vertices_392), (true, vertices_416), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 16 else
  if p.val = (false, vertices_595) then 17 else
  if p.val = (false, vertices_355) then 18 else
  if p.val = (false, vertices_569) then 22 else
  if p.val = (false, vertices_241) then 24 else
  if p.val = (false, vertices_801) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_92) then 20 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_416) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_801), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(true, vertices_92), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
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
cert_row_2 0 1 2 3 5 92
cert_row_4 1 0 1 2 6 7 398 134 2
cert_row_4 2 1 2 4 7 8 812 268 2
cert_row_4 3 2 3 4 6 7 440 56 3
cert_rows
cert_pivot_2 5 0 1 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 1 0 1 2 6 134 398 2
cert_coverFacet 1 198
cert_cover_2 1 1 0 5 6 70 198 3
cert_coverFacet 2 582
cert_cover_2 2 1 0 5 8 70 582 3
cert_coverFacet 3 450
cert_cover_2 3 5 0 6 7 194 450 3
cert_coverFacet 4 220
cert_cover_5 4 0 1 2 3 6 92 220 3
cert_coverFacet 5 604
cert_cover_5 5 0 1 2 3 8 92 604 3
cert_coverFacet 6 812
cert_cover_5 6 2 1 2 4 7 268 812 2
cert_coverFacet 7 440
cert_cover_5 7 3 2 3 4 6 56 440 3
cert_coverFacet 8 480
cert_cover_2 8 5 4 6 7 224 480 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0600

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m15e10q1_0601.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0601

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 301, 557, 341, 709, 457, 598, 570, 426, 178, 210, 706, 308, 564, 496, 45, 69, 261, 517, 137, 265, 521, 193, 321, 641, 42, 138, 522, 50, 82, 146, 530, 162, 194, 578, 642, 52, 84, 276, 532, 292, 548, 580, 296, 552, 392, 176, 304, 560, 208, 336, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_301, vertices_557, vertices_341, vertices_709, vertices_457, vertices_598, vertices_570, vertices_426, vertices_178, vertices_210, vertices_706, vertices_308, vertices_564, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_45, vertices_69, vertices_261, vertices_517, vertices_137, vertices_265, vertices_521, vertices_193, vertices_321, vertices_641, vertices_42, vertices_138, vertices_522, vertices_50, vertices_82, vertices_146, vertices_530, vertices_162, vertices_194, vertices_578, vertices_642, vertices_52, vertices_84, vertices_276, vertices_532, vertices_292, vertices_548, vertices_580, vertices_296, vertices_552, vertices_392, vertices_176, vertices_304, vertices_560, vertices_208, vertices_336, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_301), (false, vertices_557), (false, vertices_341), (false, vertices_709), (false, vertices_457), (true, vertices_42), (true, vertices_50), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_162), (true, vertices_194), (true, vertices_578), (true, vertices_52), (true, vertices_532), (true, vertices_176), (true, vertices_304), (true, vertices_560), (true, vertices_208), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 21 17 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 16 else
  if p.val = (false, vertices_301) then 18 else
  if p.val = (false, vertices_557) then 19 else
  if p.val = (false, vertices_341) then 22 else
  if p.val = (false, vertices_709) then 23 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
cert_nodeAtPriority_36 0 42 2 50 1 82 146 530 162 194 578 52 532 176 304 560 208 416 651 301 557 457 341 709
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 8 598 82 1
cert_row_4 1 0 2 3 4 8 570 42 2
cert_row_4 2 0 2 4 6 7 426 42 3
cert_row_4 3 3 4 5 6 7 496 176 2
cert_rows
cert_pivot_2 1 8 0 3
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 0 0 1 3 5 82 598 1
cert_coverFacet 1 570
cert_cover_5 1 1 0 2 3 4 42 570 2
cert_coverFacet 2 426
cert_cover_5 2 2 0 2 4 6 42 426 3
cert_coverFacet 3 178
cert_cover_2 3 3 0 4 6 50 178 3
cert_coverFacet 4 210
cert_cover_2 4 3 0 5 6 82 210 3
cert_coverFacet 5 706
cert_cover_2 5 5 0 6 8 194 706 3
cert_coverFacet 6 308
cert_cover_2 6 3 1 4 7 52 308 3
cert_coverFacet 7 564
cert_cover_2 7 3 1 4 8 52 564 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 176 496 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0601

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m15e10q1_0602.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0602

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 341, 789, 569, 361, 241, 398, 214, 534, 774, 682, 658, 484, 424, 688, 277, 41, 265, 521, 49, 81, 529, 97, 321, 769, 22, 134, 262, 518, 138, 266, 522, 146, 530, 642, 770, 84, 532, 196, 324, 388, 772, 168, 296, 552, 392, 176, 560, 208, 656, 224, 352, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_341, vertices_789, vertices_569, vertices_361, vertices_241, vertices_398, vertices_214, vertices_534, vertices_774, vertices_682, vertices_658, vertices_484, vertices_424, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_277, vertices_41, vertices_265, vertices_521, vertices_49, vertices_81, vertices_529, vertices_97, vertices_321, vertices_769, vertices_22, vertices_134, vertices_262, vertices_518, vertices_138, vertices_266, vertices_522, vertices_146, vertices_530, vertices_642, vertices_770, vertices_84, vertices_532, vertices_196, vertices_324, vertices_388, vertices_772, vertices_168, vertices_296, vertices_552, vertices_392, vertices_176, vertices_560, vertices_208, vertices_656, vertices_224, vertices_352, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_341), (false, vertices_789), (false, vertices_569), (false, vertices_361), (false, vertices_241), (true, vertices_22), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_138), (true, vertices_146), (true, vertices_530), (true, vertices_642), (true, vertices_196), (true, vertices_388), (true, vertices_168), (true, vertices_392), (true, vertices_656), (true, vertices_416), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_341) then 18 else
  if p.val = (false, vertices_789) then 19 else
  if p.val = (false, vertices_569) then 21 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_241) then 24 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_416) then 13 else
  if p.val = (true, vertices_672) then 14 else
  0
cert_priority
cert_nodeAtPriority_52 22 1 134 2 262 518 138 146 530 642 196 388 168 392 656 416 672 779 341 789 569 361 241
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 6 214 22 3
cert_row_4 1 0 2 4 6 8 682 138 2
cert_row_4 2 0 1 2 6 7 398 134 2
cert_row_4 3 1 4 5 6 7 484 196 1
cert_rows
cert_pivot_2 3 8 0 1
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 2 0 1 2 6 134 398 2
cert_coverFacet 1 214
cert_cover_5 1 0 0 1 3 5 22 214 3
cert_coverFacet 2 534
cert_cover_2 2 1 0 3 8 22 534 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 682
cert_cover_5 4 1 0 2 4 6 138 682 2
cert_coverFacet 5 658
cert_cover_2 5 3 0 6 8 146 658 3
cert_coverFacet 6 484
cert_cover_5 6 3 1 4 5 6 196 484 1
cert_coverFacet 7 424
cert_cover_2 7 4 2 6 7 168 424 3
cert_coverFacet 8 688
cert_cover_2 8 4 3 6 8 176 688 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0602

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m15e10q1_0603.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0603

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 419, 835, 613, 677, 369, 542, 282, 394, 786, 124, 172, 652, 852, 440, 131, 259, 515, 549, 97, 161, 289, 321, 577, 641, 26, 138, 266, 522, 274, 530, 386, 770, 28, 44, 140, 524, 84, 532, 100, 164, 580, 644, 56, 280, 168, 392, 648, 112, 304, 336, 784, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_419, vertices_835, vertices_613, vertices_677, vertices_369, vertices_542, vertices_282, vertices_394, vertices_786, vertices_124, vertices_172, vertices_652, vertices_852, vertices_440] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_549, vertices_97, vertices_161, vertices_289, vertices_321, vertices_577, vertices_641, vertices_26, vertices_138, vertices_266, vertices_522, vertices_274, vertices_530, vertices_386, vertices_770, vertices_28, vertices_44, vertices_140, vertices_524, vertices_84, vertices_532, vertices_100, vertices_164, vertices_580, vertices_644, vertices_56, vertices_280, vertices_168, vertices_392, vertices_648, vertices_112, vertices_304, vertices_336, vertices_784, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_419), (false, vertices_835), (false, vertices_613), (false, vertices_677), (false, vertices_369), (true, vertices_26), (true, vertices_266), (true, vertices_274), (true, vertices_530), (true, vertices_28), (true, vertices_44), (true, vertices_140), (true, vertices_524), (true, vertices_84), (true, vertices_532), (true, vertices_56), (true, vertices_280), (true, vertices_168), (true, vertices_392), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 22 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 16 else
  if p.val = (false, vertices_419) then 17 else
  if p.val = (false, vertices_835) then 18 else
  if p.val = (false, vertices_613) then 20 else
  if p.val = (false, vertices_677) then 21 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_44) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_784) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 22 => Sum.inl 2
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
cert_row_4 1 1 3 5 7 8 852 84 3
cert_row_4 2 1 2 3 4 5 124 28 3
cert_row_4 3 2 3 4 6 7 440 56 3
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 26 542 1
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 786
cert_cover_2 3 3 0 7 8 274 786 3
cert_coverFacet 4 124
cert_cover_5 4 2 1 2 3 4 28 124 3
cert_coverFacet 5 172
cert_cover_2 5 2 1 4 6 44 172 3
cert_coverFacet 6 652
cert_cover_2 6 2 1 6 8 140 652 3
cert_coverFacet 7 852
cert_cover_5 7 1 1 3 5 7 84 852 3
cert_coverFacet 8 440
cert_cover_5 8 3 2 3 4 6 56 440 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0603

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e10q1_0604.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0604

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 781, 421, 313, 617, 673, 214, 342, 774, 842, 738, 404, 248, 344, 432, 133, 261, 517, 41, 265, 521, 161, 289, 545, 641, 86, 134, 262, 518, 194, 322, 578, 642, 770, 148, 276, 388, 772, 56, 88, 280, 104, 328, 584, 776, 176, 304, 208, 336, 400, 224, 608, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_781, vertices_421, vertices_313, vertices_617, vertices_673, vertices_214, vertices_342, vertices_774, vertices_842, vertices_738, vertices_404, vertices_248, vertices_344, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_41, vertices_265, vertices_521, vertices_161, vertices_289, vertices_545, vertices_641, vertices_86, vertices_134, vertices_262, vertices_518, vertices_194, vertices_322, vertices_578, vertices_642, vertices_770, vertices_148, vertices_276, vertices_388, vertices_772, vertices_56, vertices_88, vertices_280, vertices_104, vertices_328, vertices_584, vertices_776, vertices_176, vertices_304, vertices_208, vertices_336, vertices_400, vertices_224, vertices_608, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_781), (false, vertices_421), (false, vertices_313), (false, vertices_617), (false, vertices_673), (true, vertices_86), (true, vertices_262), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_148), (true, vertices_276), (true, vertices_88), (true, vertices_328), (true, vertices_176), (true, vertices_208), (true, vertices_336), (true, vertices_400), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 16 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_421) then 20 else
  if p.val = (false, vertices_313) then 22 else
  if p.val = (false, vertices_617) then 23 else
  if p.val = (false, vertices_673) then 0 else
  if p.val = (true, vertices_86) then 17 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_194) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_224) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_673), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_86), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 5 86
cert_row_4 1 0 2 5 7 8 842 322 1
cert_row_4 2 0 4 5 6 8 738 194 1
cert_row_4 3 2 3 4 5 6 248 56 3
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 6 86 214 3
cert_coverFacet 1 342
cert_cover_5 1 0 0 1 3 7 86 342 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 842
cert_cover_5 3 1 0 2 5 7 322 842 1
cert_coverFacet 4 738
cert_cover_5 4 2 0 4 5 6 194 738 1
cert_coverFacet 5 404
cert_cover_2 5 3 1 6 7 148 404 3
cert_coverFacet 6 248
cert_cover_5 6 3 2 3 4 5 56 248 3
cert_coverFacet 7 344
cert_cover_2 7 3 2 5 7 88 344 3
cert_coverFacet 8 432
cert_cover_2 8 4 3 6 7 176 432 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0604

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e10q1_0605.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0605

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 653, 421, 837, 369, 225, 542, 122, 234, 650, 850, 284, 396, 788, 440, 133, 261, 517, 97, 161, 289, 193, 321, 577, 641, 26, 106, 138, 522, 82, 530, 194, 578, 642, 28, 140, 268, 524, 276, 532, 388, 772, 56, 280, 168, 392, 648, 112, 304, 336, 784, 224, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_653, vertices_421, vertices_837, vertices_369, vertices_225, vertices_542, vertices_122, vertices_234, vertices_650, vertices_850, vertices_284, vertices_396, vertices_788, vertices_440] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_97, vertices_161, vertices_289, vertices_193, vertices_321, vertices_577, vertices_641, vertices_26, vertices_106, vertices_138, vertices_522, vertices_82, vertices_530, vertices_194, vertices_578, vertices_642, vertices_28, vertices_140, vertices_268, vertices_524, vertices_276, vertices_532, vertices_388, vertices_772, vertices_56, vertices_280, vertices_168, vertices_392, vertices_648, vertices_112, vertices_304, vertices_336, vertices_784, vertices_224, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_653), (false, vertices_421), (false, vertices_837), (false, vertices_369), (false, vertices_225), (true, vertices_26), (true, vertices_106), (true, vertices_138), (true, vertices_522), (true, vertices_82), (true, vertices_530), (true, vertices_28), (true, vertices_268), (true, vertices_276), (true, vertices_532), (true, vertices_56), (true, vertices_280), (true, vertices_168), (true, vertices_392), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_653) then 19 else
  if p.val = (false, vertices_421) then 20 else
  if p.val = (false, vertices_837) then 21 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (false, vertices_225) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_106) then 17 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_784) then 14 else
  0
cert_priority
cert_nodeAtPriority_19 0 225 1 26 138 522 82 530 28 268 276 532 56 280 168 392 784 707 106 653 421 837 369
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 8 542 26 1
cert_row_4 1 0 3 5 7 8 850 82 3
cert_row_2 2 0 2 4 5 106
cert_row_4 3 2 3 4 6 7 440 56 3
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 26 542 1
cert_coverFacet 1 122
cert_cover_5 1 2 0 2 3 4 26 122 3
cert_coverFacet 2 234
cert_cover_5 2 2 0 2 4 6 106 234 3
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 850
cert_cover_5 4 1 0 3 5 7 82 850 3
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 396
cert_cover_2 6 2 1 6 7 140 396 3
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coverFacet 8 440
cert_cover_5 8 3 2 3 4 6 56 440 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0605

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e10q1_0606.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0606

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 595, 675, 291, 709, 337, 481, 302, 558, 538, 604, 204, 396, 932, 472, 19, 35, 259, 515, 81, 273, 161, 289, 193, 321, 577, 641, 46, 26, 266, 522, 530, 290, 546, 76, 140, 268, 524, 292, 548, 196, 580, 388, 644, 88, 280, 536, 200, 392, 336, 592, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_595, vertices_675, vertices_291, vertices_709, vertices_337, vertices_481, vertices_302, vertices_558, vertices_538, vertices_604, vertices_204, vertices_396, vertices_932, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_259, vertices_515, vertices_81, vertices_273, vertices_161, vertices_289, vertices_193, vertices_321, vertices_577, vertices_641, vertices_46, vertices_26, vertices_266, vertices_522, vertices_530, vertices_290, vertices_546, vertices_76, vertices_140, vertices_268, vertices_524, vertices_292, vertices_548, vertices_196, vertices_580, vertices_388, vertices_644, vertices_88, vertices_280, vertices_536, vertices_200, vertices_392, vertices_336, vertices_592, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_595), (false, vertices_675), (false, vertices_291), (false, vertices_709), (false, vertices_337), (false, vertices_481), (true, vertices_46), (true, vertices_522), (true, vertices_76), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_292), (true, vertices_548), (true, vertices_388), (true, vertices_88), (true, vertices_536), (true, vertices_200), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 14 21 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 18 else
  if p.val = (false, vertices_595) then 19 else
  if p.val = (false, vertices_675) then 20 else
  if p.val = (false, vertices_291) then 0 else
  if p.val = (false, vertices_709) then 15 else
  if p.val = (false, vertices_337) then 1 else
  if p.val = (false, vertices_481) then 24 else
  if p.val = (true, vertices_46) then 16 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_292) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_392) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_291), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_337), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_46), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 21 => Sum.inl 2
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
cert_row_2 0 0 1 2 4 46
cert_row_4 1 1 4 6 7 8 932 292 2
cert_row_4 2 1 2 3 5 8 604 76 2
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 0 4 1 2
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 0 0 1 2 7 46 302 3
cert_coverFacet 1 558
cert_cover_5 1 0 0 1 2 8 46 558 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 604
cert_cover_5 3 2 1 2 3 5 76 604 2
cert_coverFacet 4 204
cert_cover_2 4 2 1 5 6 76 204 3
cert_coverFacet 5 396
cert_cover_2 5 2 1 6 7 140 396 3
cert_coverFacet 6 932
cert_cover_5 6 1 1 4 6 7 292 932 2
cert_coverFacet 7 472
cert_cover_5 7 3 2 3 5 6 88 472 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0606

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e10q1_0607.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0607

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 333, 229, 549, 713, 777, 689, 566, 358, 666, 282, 778, 370, 248, 344, 37, 69, 261, 517, 73, 265, 521, 161, 545, 193, 641, 769, 38, 262, 518, 26, 266, 522, 50, 274, 530, 354, 770, 100, 548, 324, 88, 152, 280, 200, 328, 648, 776, 112, 176, 560, 336, 656, 224]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_333, vertices_229, vertices_549, vertices_713, vertices_777, vertices_689, vertices_566, vertices_358, vertices_666, vertices_282, vertices_778, vertices_370, vertices_248, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_261, vertices_517, vertices_73, vertices_265, vertices_521, vertices_161, vertices_545, vertices_193, vertices_641, vertices_769, vertices_38, vertices_262, vertices_518, vertices_26, vertices_266, vertices_522, vertices_50, vertices_274, vertices_530, vertices_354, vertices_770, vertices_100, vertices_548, vertices_324, vertices_88, vertices_152, vertices_280, vertices_200, vertices_328, vertices_648, vertices_776, vertices_112, vertices_176, vertices_560, vertices_336, vertices_656, vertices_224] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_333), (false, vertices_229), (false, vertices_549), (false, vertices_713), (false, vertices_777), (false, vertices_689), (true, vertices_38), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_354), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_112), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 15 else
  if p.val = (false, vertices_333) then 18 else
  if p.val = (false, vertices_229) then 19 else
  if p.val = (false, vertices_549) then 0 else
  if p.val = (false, vertices_713) then 21 else
  if p.val = (false, vertices_777) then 1 else
  if p.val = (false, vertices_689) then 23 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_50) then 6 else
  if p.val = (true, vertices_274) then 7 else
  if p.val = (true, vertices_530) then 8 else
  if p.val = (true, vertices_354) then 16 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_336) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 0 549 1 777 38 26 266 522 50 274 530 88 152 280 112 336 775 354 333 229 713 689
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 4 5 7 354
cert_row_4 1 0 1 3 4 8 566 38 2
cert_row_4 2 0 2 3 6 8 666 26 3
cert_row_4 3 2 3 4 5 6 248 88 2
cert_rows
cert_pivot_2 7 1 0 2
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 1 0 1 3 4 38 566 2
cert_coverFacet 1 358
cert_cover_5 1 0 0 1 4 5 38 358 3
cert_coverFacet 2 666
cert_cover_5 2 2 0 2 3 6 26 666 3
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 370
cert_cover_5 5 0 0 3 4 5 50 370 3
cert_coverFacet 6 248
cert_cover_5 6 3 2 3 4 5 88 248 2
cert_coverFacet 7 344
cert_cover_2 7 3 2 5 7 88 344 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0607

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e10q1_0608.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0608

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [583, 541, 45, 101, 313, 849, 481, 206, 526, 186, 538, 658, 962, 236, 944, 13, 37, 69, 517, 25, 41, 273, 529, 97, 289, 321, 577, 14, 70, 518, 26, 138, 522, 146, 530, 194, 578, 642, 44, 204, 524, 100, 56, 536, 168, 176, 304, 656, 784, 224, 416, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_583, vertices_541, vertices_45, vertices_101, vertices_313, vertices_849, vertices_481, vertices_206, vertices_526, vertices_186, vertices_538, vertices_658, vertices_962, vertices_236, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_69, vertices_517, vertices_25, vertices_41, vertices_273, vertices_529, vertices_97, vertices_289, vertices_321, vertices_577, vertices_14, vertices_70, vertices_518, vertices_26, vertices_138, vertices_522, vertices_146, vertices_530, vertices_194, vertices_578, vertices_642, vertices_44, vertices_204, vertices_524, vertices_100, vertices_56, vertices_536, vertices_168, vertices_176, vertices_304, vertices_656, vertices_784, vertices_224, vertices_416, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_583), (false, vertices_541), (false, vertices_45), (false, vertices_101), (false, vertices_313), (false, vertices_849), (false, vertices_481), (true, vertices_14), (true, vertices_26), (true, vertices_138), (true, vertices_522), (true, vertices_146), (true, vertices_530), (true, vertices_194), (true, vertices_642), (true, vertices_204), (true, vertices_168), (true, vertices_176), (true, vertices_656), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 19 21 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_583) then 15 else
  if p.val = (false, vertices_541) then 17 else
  if p.val = (false, vertices_45) then 0 else
  if p.val = (false, vertices_101) then 1 else
  if p.val = (false, vertices_313) then 20 else
  if p.val = (false, vertices_849) then 22 else
  if p.val = (false, vertices_481) then 24 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_194) then 8 else
  if p.val = (true, vertices_642) then 9 else
  if p.val = (true, vertices_204) then 18 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_896) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_45), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_101), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 5 6 204
cert_row_4 1 0 2 3 4 6 186 26 3
cert_row_4 2 0 5 6 7 8 962 194 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 186
cert_cover_5 2 1 0 2 3 4 26 186 3
cert_coverFacet 3 538
cert_cover_2 3 2 0 3 8 26 538 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 962
cert_cover_5 5 2 0 5 6 7 194 962 3
cert_coverFacet 6 236
cert_cover_5 6 0 1 2 4 5 44 236 3
cert_coverFacet 7 944
cert_cover_5 7 3 3 4 6 7 176 944 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0608

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m15e10q1_0609.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0609

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 661, 453, 217, 625, 833, 302, 654, 682, 866, 396, 376, 184, 456, 688, 133, 261, 517, 81, 145, 529, 193, 321, 577, 769, 14, 262, 518, 42, 650, 290, 546, 770, 140, 268, 388, 644, 56, 88, 152, 168, 296, 200, 328, 392, 112, 176, 560, 656, 352, 608, 672, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_661, vertices_453, vertices_217, vertices_625, vertices_833, vertices_302, vertices_654, vertices_682, vertices_866, vertices_396, vertices_376, vertices_184, vertices_456, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_81, vertices_145, vertices_529, vertices_193, vertices_321, vertices_577, vertices_769, vertices_14, vertices_262, vertices_518, vertices_42, vertices_650, vertices_290, vertices_546, vertices_770, vertices_140, vertices_268, vertices_388, vertices_644, vertices_56, vertices_88, vertices_152, vertices_168, vertices_296, vertices_200, vertices_328, vertices_392, vertices_112, vertices_176, vertices_560, vertices_656, vertices_352, vertices_608, vertices_672, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_661), (false, vertices_453), (false, vertices_217), (false, vertices_625), (false, vertices_833), (true, vertices_14), (true, vertices_42), (true, vertices_650), (true, vertices_290), (true, vertices_546), (true, vertices_140), (true, vertices_268), (true, vertices_56), (true, vertices_168), (true, vertices_296), (true, vertices_328), (true, vertices_392), (true, vertices_176), (true, vertices_352), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 16 else
  if p.val = (false, vertices_661) then 19 else
  if p.val = (false, vertices_453) then 20 else
  if p.val = (false, vertices_217) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (false, vertices_833) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_650) then 17 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_168) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_352) then 13 else
  if p.val = (true, vertices_672) then 14 else
  0
cert_priority
cert_nodeAtPriority_22 833 14 42 290 546 140 268 56 168 296 328 392 176 352 672 775 650 661 453 217 625
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 6 8 650
cert_row_4 1 0 1 2 4 7 302 14 3
cert_row_4 2 0 4 5 7 8 866 290 2
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 6 1 0 2
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 1 0 1 2 4 14 302 3
cert_coverFacet 1 654
cert_cover_5 1 0 0 1 2 6 14 654 3
cert_coverFacet 2 682
cert_cover_5 2 0 0 2 4 6 42 682 3
cert_coverFacet 3 866
cert_cover_5 3 2 0 4 5 7 290 866 2
cert_coverFacet 4 396
cert_cover_2 4 2 1 6 7 140 396 3
cert_coverFacet 5 376
cert_cover_5 5 3 2 3 4 5 56 376 3
cert_coverFacet 6 184
cert_cover_2 6 3 2 4 6 56 184 3
cert_coverFacet 7 456
cert_cover_2 7 5 2 6 7 200 456 3
cert_coverFacet 8 688
cert_cover_2 8 4 3 6 8 176 688 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0609

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m15e10q1_0610.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0610

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [551, 291, 771, 229, 837, 425, 465, 570, 410, 298, 850, 684, 716, 216, 600, 35, 259, 515, 37, 69, 517, 161, 289, 193, 321, 385, 769, 26, 42, 266, 274, 530, 290, 546, 770, 652, 164, 548, 196, 580, 88, 152, 536, 168, 296, 552, 200, 584, 392, 208, 336, 592, 400, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_551, vertices_291, vertices_771, vertices_229, vertices_837, vertices_425, vertices_465, vertices_570, vertices_410, vertices_298, vertices_850, vertices_684, vertices_716, vertices_216, vertices_600] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_259, vertices_515, vertices_37, vertices_69, vertices_517, vertices_161, vertices_289, vertices_193, vertices_321, vertices_385, vertices_769, vertices_26, vertices_42, vertices_266, vertices_274, vertices_530, vertices_290, vertices_546, vertices_770, vertices_652, vertices_164, vertices_548, vertices_196, vertices_580, vertices_88, vertices_152, vertices_536, vertices_168, vertices_296, vertices_552, vertices_200, vertices_584, vertices_392, vertices_208, vertices_336, vertices_592, vertices_400, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_551), (false, vertices_291), (false, vertices_771), (false, vertices_229), (false, vertices_837), (false, vertices_425), (false, vertices_465), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_274), (true, vertices_530), (true, vertices_652), (true, vertices_88), (true, vertices_152), (true, vertices_536), (true, vertices_552), (true, vertices_200), (true, vertices_584), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_551) then 15 else
  if p.val = (false, vertices_291) then 0 else
  if p.val = (false, vertices_771) then 1 else
  if p.val = (false, vertices_229) then 17 else
  if p.val = (false, vertices_837) then 18 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_652) then 19 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_200) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_592) then 13 else
  0
cert_priority
cert_nodeAtPriority_54 291 771 26 42 266 274 530 88 152 536 552 200 584 592 551 229 837 652 425 465
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 8 652
cert_row_4 1 0 2 3 4 8 570 26 3
cert_row_4 2 0 2 3 6 7 410 26 3
cert_row_4 3 0 3 5 7 8 850 274 2
cert_rows
cert_pivot_2 1 4 2 0
cert_heightProof 4
cert_coverFacet 0 570
cert_cover_5 0 1 0 2 3 4 26 570 3
cert_coverFacet 1 410
cert_cover_5 1 2 0 2 3 6 26 410 3
cert_coverFacet 2 298
cert_cover_2 2 2 0 4 7 42 298 3
cert_coverFacet 3 850
cert_cover_5 3 3 0 3 5 7 274 850 2
cert_coverFacet 4 684
cert_cover_5 4 0 1 2 4 6 652 684 2
cert_coverFacet 5 716
cert_cover_5 5 0 1 2 5 6 652 716 2
cert_coverFacet 6 216
cert_cover_2 6 3 2 5 6 88 216 3
cert_coverFacet 7 600
cert_cover_2 7 3 2 5 8 88 600 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0610

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m15e10q1_0611.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0611

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 419, 707, 613, 233, 801, 286, 154, 394, 658, 668, 364, 716, 820, 424, 131, 259, 515, 97, 161, 289, 545, 193, 577, 769, 26, 138, 266, 146, 274, 530, 386, 642, 28, 76, 652, 268, 276, 532, 100, 292, 548, 580, 152, 104, 168, 296, 200, 392, 656, 784, 416, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_419, vertices_707, vertices_613, vertices_233, vertices_801, vertices_286, vertices_154, vertices_394, vertices_658, vertices_668, vertices_364, vertices_716, vertices_820, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_97, vertices_161, vertices_289, vertices_545, vertices_193, vertices_577, vertices_769, vertices_26, vertices_138, vertices_266, vertices_146, vertices_274, vertices_530, vertices_386, vertices_642, vertices_28, vertices_76, vertices_652, vertices_268, vertices_276, vertices_532, vertices_100, vertices_292, vertices_548, vertices_580, vertices_152, vertices_104, vertices_168, vertices_296, vertices_200, vertices_392, vertices_656, vertices_784, vertices_416, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_419), (false, vertices_707), (false, vertices_613), (false, vertices_233), (false, vertices_801), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_146), (true, vertices_28), (true, vertices_76), (true, vertices_652), (true, vertices_268), (true, vertices_276), (true, vertices_532), (true, vertices_292), (true, vertices_152), (true, vertices_296), (true, vertices_392), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 22 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 16 else
  if p.val = (false, vertices_419) then 17 else
  if p.val = (false, vertices_707) then 18 else
  if p.val = (false, vertices_613) then 20 else
  if p.val = (false, vertices_233) then 23 else
  if p.val = (false, vertices_801) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_652) then 21 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_656) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_801), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_652), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 6 8 652
cert_row_4 1 0 1 2 3 7 286 26 1
cert_row_4 2 1 2 4 5 7 364 76 2
cert_row_4 3 1 3 4 7 8 820 276 2
cert_rows
cert_pivot_2 6 0 2 1
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 1 0 1 2 3 26 286 1
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 658
cert_cover_2 3 3 0 6 8 146 658 3
cert_coverFacet 4 668
cert_cover_5 4 0 1 2 3 6 28 668 3
cert_coverFacet 5 364
cert_cover_5 5 2 1 2 4 5 76 364 2
cert_coverFacet 6 716
cert_cover_5 6 0 1 2 5 6 76 716 3
cert_coverFacet 7 820
cert_cover_5 7 3 1 3 4 7 276 820 2
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0611

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m15e10q1_0612.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0612

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 117, 601, 713, 817, 481, 654, 270, 566, 294, 458, 802, 92, 540, 364, 585, 49, 81, 529, 97, 289, 193, 385, 641, 769, 14, 38, 262, 518, 138, 266, 290, 546, 386, 642, 770, 28, 76, 268, 524, 52, 84, 532, 100, 292, 88, 536, 200, 328, 648, 560, 352, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_117, vertices_601, vertices_713, vertices_817, vertices_481, vertices_654, vertices_270, vertices_566, vertices_294, vertices_458, vertices_802, vertices_92, vertices_540, vertices_364] (by decide +kernel)
  polygons := literalFinset [vertices_585, vertices_49, vertices_81, vertices_529, vertices_97, vertices_289, vertices_193, vertices_385, vertices_641, vertices_769, vertices_14, vertices_38, vertices_262, vertices_518, vertices_138, vertices_266, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_28, vertices_76, vertices_268, vertices_524, vertices_52, vertices_84, vertices_532, vertices_100, vertices_292, vertices_88, vertices_536, vertices_200, vertices_328, vertices_648, vertices_560, vertices_352, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_117), (false, vertices_601), (false, vertices_713), (false, vertices_817), (false, vertices_481), (true, vertices_14), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_138), (true, vertices_266), (true, vertices_290), (true, vertices_546), (true, vertices_28), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_532), (true, vertices_292), (true, vertices_328)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 19 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 16 else
  if p.val = (false, vertices_117) then 18 else
  if p.val = (false, vertices_601) then 20 else
  if p.val = (false, vertices_713) then 21 else
  if p.val = (false, vertices_817) then 23 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_76) then 9 else
  if p.val = (true, vertices_268) then 10 else
  if p.val = (true, vertices_524) then 11 else
  if p.val = (true, vertices_532) then 12 else
  if p.val = (true, vertices_292) then 13 else
  if p.val = (true, vertices_328) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 8 566 38 2
cert_row_4 1 0 1 2 6 8 654 14 3
cert_row_4 2 0 2 5 6 7 458 138 2
cert_row_4 3 1 2 4 5 7 364 76 2
cert_rows
cert_pivot_2 3 8 0 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 1 0 1 2 6 14 654 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 566
cert_cover_5 2 0 0 1 3 4 38 566 2
cert_coverFacet 3 294
cert_cover_2 3 1 0 4 7 38 294 3
cert_coverFacet 4 458
cert_cover_5 4 2 0 2 5 6 138 458 2
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 92
cert_cover_2 6 2 1 3 5 28 92 3
cert_coverFacet 7 540
cert_cover_2 7 2 1 3 8 28 540 3
cert_coverFacet 8 364
cert_cover_5 8 3 1 2 4 5 76 364 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0612

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m15e10q1_0613.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0613

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 205, 589, 677, 809, 433, 598, 794, 202, 586, 242, 402, 116, 820, 228, 77, 133, 517, 137, 265, 521, 161, 289, 545, 385, 74, 138, 266, 522, 82, 146, 274, 530, 194, 578, 386, 52, 84, 532, 100, 164, 548, 196, 580, 200, 584, 776, 112, 176, 304, 400, 784, 224, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_205, vertices_589, vertices_677, vertices_809, vertices_433, vertices_598, vertices_794, vertices_202, vertices_586, vertices_242, vertices_402, vertices_116, vertices_820, vertices_228] (by decide +kernel)
  polygons := literalFinset [vertices_77, vertices_133, vertices_517, vertices_137, vertices_265, vertices_521, vertices_161, vertices_289, vertices_545, vertices_385, vertices_74, vertices_138, vertices_266, vertices_522, vertices_82, vertices_146, vertices_274, vertices_530, vertices_194, vertices_578, vertices_386, vertices_52, vertices_84, vertices_532, vertices_100, vertices_164, vertices_548, vertices_196, vertices_580, vertices_200, vertices_584, vertices_776, vertices_112, vertices_176, vertices_304, vertices_400, vertices_784, vertices_224, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_205), (false, vertices_589), (false, vertices_677), (false, vertices_809), (false, vertices_433), (true, vertices_74), (true, vertices_522), (true, vertices_82), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_194), (true, vertices_578), (true, vertices_52), (true, vertices_84), (true, vertices_532), (true, vertices_100), (true, vertices_112), (true, vertices_784), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 16 else
  if p.val = (false, vertices_205) then 18 else
  if p.val = (false, vertices_589) then 19 else
  if p.val = (false, vertices_677) then 20 else
  if p.val = (false, vertices_809) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_100) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_784) then 13 else
  if p.val = (true, vertices_224) then 14 else
  0
cert_priority
cert_nodeAtPriority_68 0 74 1 522 82 146 274 530 194 578 52 84 532 100 112 784 224 395 205 589 677 809 433
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 7 8 794 266 2
cert_row_4 1 0 3 4 5 6 242 82 2
cert_row_4 2 0 1 3 5 8 598 82 1
cert_row_4 3 1 3 4 7 8 820 52 3
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 2 0 1 3 5 82 598 1
cert_coverFacet 1 794
cert_cover_5 1 0 0 2 3 7 266 794 2
cert_coverFacet 2 202
cert_cover_2 2 2 0 5 6 74 202 3
cert_coverFacet 3 586
cert_cover_2 3 2 0 5 8 74 586 3
cert_coverFacet 4 242
cert_cover_5 4 1 0 3 4 5 82 242 2
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 116
cert_cover_2 6 3 1 4 5 52 116 3
cert_coverFacet 7 820
cert_cover_5 7 3 1 3 4 7 52 820 3
cert_coverFacet 8 228
cert_cover_2 8 4 1 5 6 100 228 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0613

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m15e10q1_0614.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0614

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 535, 653, 453, 849, 737, 302, 526, 682, 626, 306, 396, 376, 232, 456, 23, 133, 261, 517, 273, 529, 193, 321, 577, 641, 14, 262, 518, 42, 522, 50, 274, 530, 290, 546, 140, 268, 524, 388, 104, 168, 296, 200, 328, 392, 648, 112, 304, 336, 592, 224, 608, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_535, vertices_653, vertices_453, vertices_849, vertices_737, vertices_302, vertices_526, vertices_682, vertices_626, vertices_306, vertices_396, vertices_376, vertices_232, vertices_456] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_133, vertices_261, vertices_517, vertices_273, vertices_529, vertices_193, vertices_321, vertices_577, vertices_641, vertices_14, vertices_262, vertices_518, vertices_42, vertices_522, vertices_50, vertices_274, vertices_530, vertices_290, vertices_546, vertices_140, vertices_268, vertices_524, vertices_388, vertices_104, vertices_168, vertices_296, vertices_200, vertices_328, vertices_392, vertices_648, vertices_112, vertices_304, vertices_336, vertices_592, vertices_224, vertices_608, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_535), (false, vertices_653), (false, vertices_453), (false, vertices_849), (false, vertices_737), (true, vertices_14), (true, vertices_42), (true, vertices_522), (true, vertices_50), (true, vertices_290), (true, vertices_546), (true, vertices_268), (true, vertices_104), (true, vertices_168), (true, vertices_296), (true, vertices_200), (true, vertices_328), (true, vertices_392), (true, vertices_112), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 16 else
  if p.val = (false, vertices_535) then 17 else
  if p.val = (false, vertices_653) then 19 else
  if p.val = (false, vertices_453) then 20 else
  if p.val = (false, vertices_849) then 23 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_104) then 7 else
  if p.val = (true, vertices_168) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_304) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_279), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 7 302 14 3
cert_row_4 1 0 2 4 6 8 682 42 3
cert_row_4 2 0 3 4 5 8 626 50 3
cert_row_4 3 2 3 4 5 7 376 104 1
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 0 0 1 2 4 14 302 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 682
cert_cover_5 2 1 0 2 4 6 42 682 3
cert_coverFacet 3 626
cert_cover_5 3 2 0 3 4 5 50 626 3
cert_coverFacet 4 306
cert_cover_2 4 3 0 4 7 50 306 3
cert_coverFacet 5 396
cert_cover_2 5 2 1 6 7 140 396 3
cert_coverFacet 6 376
cert_cover_5 6 3 2 3 4 5 104 376 1
cert_coverFacet 7 232
cert_cover_2 7 4 2 5 6 104 232 3
cert_coverFacet 8 456
cert_cover_2 8 5 2 6 7 200 456 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0614

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e10q1_0615.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0615

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [539, 205, 525, 661, 345, 401, 481, 110, 558, 282, 330, 914, 866, 228, 932, 13, 133, 517, 25, 73, 521, 145, 273, 529, 193, 321, 385, 46, 26, 74, 266, 522, 274, 530, 98, 546, 322, 770, 76, 524, 100, 164, 548, 196, 644, 280, 328, 400, 656, 224, 352, 416, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_539, vertices_205, vertices_525, vertices_661, vertices_345, vertices_401, vertices_481, vertices_110, vertices_558, vertices_282, vertices_330, vertices_914, vertices_866, vertices_228, vertices_932] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_517, vertices_25, vertices_73, vertices_521, vertices_145, vertices_273, vertices_529, vertices_193, vertices_321, vertices_385, vertices_46, vertices_26, vertices_74, vertices_266, vertices_522, vertices_274, vertices_530, vertices_98, vertices_546, vertices_322, vertices_770, vertices_76, vertices_524, vertices_100, vertices_164, vertices_548, vertices_196, vertices_644, vertices_280, vertices_328, vertices_400, vertices_656, vertices_224, vertices_352, vertices_416, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_539), (false, vertices_205), (false, vertices_525), (false, vertices_661), (false, vertices_345), (false, vertices_401), (false, vertices_481), (true, vertices_46), (true, vertices_74), (true, vertices_266), (true, vertices_274), (true, vertices_98), (true, vertices_546), (true, vertices_322), (true, vertices_770), (true, vertices_100), (true, vertices_164), (true, vertices_548), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_539) then 15 else
  if p.val = (false, vertices_205) then 18 else
  if p.val = (false, vertices_525) then 0 else
  if p.val = (false, vertices_661) then 19 else
  if p.val = (false, vertices_345) then 21 else
  if p.val = (false, vertices_401) then 1 else
  if p.val = (false, vertices_481) then 24 else
  if p.val = (true, vertices_46) then 16 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_164) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_800) then 12 else
  if p.val = (true, vertices_896) then 13 else
  0
cert_priority
cert_nodeAtPriority_53 0 525 1 401 74 266 274 98 546 322 770 100 164 548 800 896 539 46 205 661 345 481
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 4 46
cert_row_4 1 0 3 6 7 8 914 274 2
cert_row_4 2 0 4 5 7 8 866 98 3
cert_row_4 3 1 4 6 7 8 932 164 3
cert_rows
cert_pivot_2 2 3 0 1
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 0 0 1 2 5 46 110 3
cert_coverFacet 1 558
cert_cover_5 1 0 0 1 2 8 46 558 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 330
cert_cover_2 3 2 0 5 7 74 330 3
cert_coverFacet 4 914
cert_cover_5 4 1 0 3 6 7 274 914 2
cert_coverFacet 5 866
cert_cover_5 5 2 0 4 5 7 98 866 3
cert_coverFacet 6 228
cert_cover_2 6 4 1 5 6 100 228 3
cert_coverFacet 7 932
cert_cover_5 7 3 1 4 6 7 164 932 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0615

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e10q1_0616.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0616

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 597, 665, 841, 369, 401, 174, 558, 778, 434, 802, 652, 244, 660, 868, 137, 265, 521, 81, 145, 273, 529, 321, 577, 385, 46, 138, 266, 522, 162, 290, 546, 386, 770, 140, 524, 84, 148, 532, 100, 164, 548, 580, 644, 648, 776, 112, 176, 304, 400, 656, 352, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_597, vertices_665, vertices_841, vertices_369, vertices_401, vertices_174, vertices_558, vertices_778, vertices_434, vertices_802, vertices_652, vertices_244, vertices_660, vertices_868] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_81, vertices_145, vertices_273, vertices_529, vertices_321, vertices_577, vertices_385, vertices_46, vertices_138, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_386, vertices_770, vertices_140, vertices_524, vertices_84, vertices_148, vertices_532, vertices_100, vertices_164, vertices_548, vertices_580, vertices_644, vertices_648, vertices_776, vertices_112, vertices_176, vertices_304, vertices_400, vertices_656, vertices_352, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_597), (false, vertices_665), (false, vertices_841), (false, vertices_369), (false, vertices_401), (true, vertices_46), (true, vertices_522), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_140), (true, vertices_524), (true, vertices_148), (true, vertices_100), (true, vertices_164), (true, vertices_548), (true, vertices_644), (true, vertices_176), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 16 else
  if p.val = (false, vertices_597) then 19 else
  if p.val = (false, vertices_665) then 21 else
  if p.val = (false, vertices_841) then 22 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (false, vertices_401) then 0 else
  if p.val = (true, vertices_46) then 17 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_290) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_164) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_644) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_800) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 401 522 162 290 546 770 140 524 148 100 164 548 644 176 800 395 46 597 665 841 369
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 4 46
cert_row_4 1 0 3 4 6 7 434 162 1
cert_row_4 2 1 3 4 5 6 244 84 2
cert_row_4 3 1 4 5 7 8 868 100 3
cert_rows
cert_pivot_2 2 0 3 1
cert_heightProof 4
cert_coverFacet 0 174
cert_cover_5 0 0 0 1 2 6 46 174 3
cert_coverFacet 1 558
cert_cover_5 1 0 0 1 2 8 46 558 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 434
cert_cover_5 3 1 0 3 4 6 162 434 1
cert_coverFacet 4 802
cert_cover_2 4 4 0 7 8 290 802 3
cert_coverFacet 5 652
cert_cover_2 5 2 1 6 8 140 652 3
cert_coverFacet 6 244
cert_cover_5 6 2 1 3 4 5 84 244 2
cert_coverFacet 7 660
cert_cover_2 7 3 1 6 8 148 660 3
cert_coverFacet 8 868
cert_cover_5 8 3 1 4 5 7 100 868 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0616

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e10q1_0617.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0617

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [59, 299, 837, 793, 625, 481, 158, 394, 690, 418, 540, 460, 780, 660, 740, 43, 25, 265, 49, 529, 97, 289, 321, 577, 769, 26, 138, 266, 50, 146, 162, 290, 386, 28, 140, 268, 524, 148, 532, 196, 324, 580, 644, 772, 536, 392, 776, 560, 656, 224, 608, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_59, vertices_299, vertices_837, vertices_793, vertices_625, vertices_481, vertices_158, vertices_394, vertices_690, vertices_418, vertices_540, vertices_460, vertices_780, vertices_660, vertices_740] (by decide +kernel)
  polygons := literalFinset [vertices_43, vertices_25, vertices_265, vertices_49, vertices_529, vertices_97, vertices_289, vertices_321, vertices_577, vertices_769, vertices_26, vertices_138, vertices_266, vertices_50, vertices_146, vertices_162, vertices_290, vertices_386, vertices_28, vertices_140, vertices_268, vertices_524, vertices_148, vertices_532, vertices_196, vertices_324, vertices_580, vertices_644, vertices_772, vertices_536, vertices_392, vertices_776, vertices_560, vertices_656, vertices_224, vertices_608, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_59), (false, vertices_299), (false, vertices_837), (false, vertices_793), (false, vertices_625), (false, vertices_481), (true, vertices_138), (true, vertices_146), (true, vertices_162), (true, vertices_386), (true, vertices_28), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_148), (true, vertices_532), (true, vertices_196), (true, vertices_644), (true, vertices_392), (true, vertices_656), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_59) then 16 else
  if p.val = (false, vertices_299) then 17 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_793) then 21 else
  if p.val = (false, vertices_625) then 23 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_140) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_656) then 13 else
  if p.val = (true, vertices_672) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_59), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 5 6 7 460 140 2
cert_row_4 1 0 1 2 3 6 158 26 1
cert_row_4 2 0 3 4 6 8 690 50 3
cert_row_4 3 1 4 5 6 8 740 196 1
cert_rows
cert_pivot_2 7 2 0 1
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 1 0 1 2 3 26 158 1
cert_coverFacet 1 394
cert_cover_2 1 2 0 6 7 138 394 3
cert_coverFacet 2 690
cert_cover_5 2 2 0 3 4 6 50 690 3
cert_coverFacet 3 418
cert_cover_2 3 4 0 6 7 162 418 3
cert_coverFacet 4 540
cert_cover_2 4 2 1 3 8 28 540 3
cert_coverFacet 5 460
cert_cover_5 5 0 1 2 5 6 140 460 2
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 660
cert_cover_2 7 3 1 6 8 148 660 3
cert_coverFacet 8 740
cert_cover_5 8 3 1 4 5 6 196 740 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0617

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_3183 : Certifies 3183 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0588.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3184 : Certifies 3184 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0589.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3185 : Certifies 3185 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0590.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3186 : Certifies 3186 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0591.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3187 : Certifies 3187 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0592.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3188 : Certifies 3188 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0593.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3189 : Certifies 3189 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0594.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3190 : Certifies 3190 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0595.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3191 : Certifies 3191 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0596.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3192 : Certifies 3192 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0597.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3193 : Certifies 3193 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0598.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3194 : Certifies 3194 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0599.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3195 : Certifies 3195 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0600.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3196 : Certifies 3196 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0601.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3197 : Certifies 3197 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0602.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3198 : Certifies 3198 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0603.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3199 : Certifies 3199 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0604.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3200 : Certifies 3200 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0605.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3201 : Certifies 3201 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0606.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3202 : Certifies 3202 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0607.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3203 : Certifies 3203 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0608.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3204 : Certifies 3204 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0609.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3205 : Certifies 3205 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0610.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3206 : Certifies 3206 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0611.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3207 : Certifies 3207 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0612.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3208 : Certifies 3208 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0613.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3209 : Certifies 3209 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0614.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3210 : Certifies 3210 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0615.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3211 : Certifies 3211 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0616.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3212 : Certifies 3212 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0617.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B105 (j : Fin 30) :
    Certifies (3183 + j.val) := by
  fin_cases j
  · exact projection_3183
  · exact projection_3184
  · exact projection_3185
  · exact projection_3186
  · exact projection_3187
  · exact projection_3188
  · exact projection_3189
  · exact projection_3190
  · exact projection_3191
  · exact projection_3192
  · exact projection_3193
  · exact projection_3194
  · exact projection_3195
  · exact projection_3196
  · exact projection_3197
  · exact projection_3198
  · exact projection_3199
  · exact projection_3200
  · exact projection_3201
  · exact projection_3202
  · exact projection_3203
  · exact projection_3204
  · exact projection_3205
  · exact projection_3206
  · exact projection_3207
  · exact projection_3208
  · exact projection_3209
  · exact projection_3210
  · exact projection_3211
  · exact projection_3212

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
