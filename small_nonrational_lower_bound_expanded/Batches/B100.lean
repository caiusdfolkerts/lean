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
/- Source: ProjectionCertificates/R_m15e10q1_0427.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0427

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 173, 781, 613, 313, 369, 902, 346, 154, 394, 626, 658, 396, 692, 184, 13, 37, 517, 41, 265, 305, 97, 321, 577, 769, 26, 138, 266, 82, 146, 530, 322, 578, 386, 642, 770, 140, 268, 164, 548, 388, 644, 772, 56, 152, 280, 168, 392, 112, 176, 560, 336, 656, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_173, vertices_781, vertices_613, vertices_313, vertices_369, vertices_902, vertices_346, vertices_154, vertices_394, vertices_626, vertices_658, vertices_396, vertices_692, vertices_184] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_517, vertices_41, vertices_265, vertices_305, vertices_97, vertices_321, vertices_577, vertices_769, vertices_26, vertices_138, vertices_266, vertices_82, vertices_146, vertices_530, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_140, vertices_268, vertices_164, vertices_548, vertices_388, vertices_644, vertices_772, vertices_56, vertices_152, vertices_280, vertices_168, vertices_392, vertices_112, vertices_176, vertices_560, vertices_336, vertices_656, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_173), (false, vertices_781), (false, vertices_613), (false, vertices_313), (false, vertices_369), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_386), (true, vertices_642), (true, vertices_388), (true, vertices_644), (true, vertices_152), (true, vertices_392), (true, vertices_176), (true, vertices_560), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_173) then 18 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_613) then 20 else
  if p.val = (false, vertices_313) then 23 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_656) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 7 346 26 3
cert_row_4 1 0 1 6 7 8 902 386 1
cert_row_4 2 0 3 4 5 8 626 82 2
cert_row_4 3 1 3 4 6 8 692 164 1
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 1 0 1 6 7 386 902 1
cert_coverFacet 1 346
cert_cover_5 1 0 0 2 3 5 26 346 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 626
cert_cover_5 4 2 0 3 4 5 82 626 2
cert_coverFacet 5 658
cert_cover_2 5 3 0 6 8 146 658 3
cert_coverFacet 6 396
cert_cover_2 6 2 1 6 7 140 396 3
cert_coverFacet 7 692
cert_cover_5 7 3 1 3 4 6 164 692 1
cert_coverFacet 8 184
cert_cover_2 8 3 2 4 6 56 184 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0427

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e10q1_0428.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0428

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 301, 141, 789, 681, 865, 94, 206, 534, 850, 738, 284, 472, 424, 480, 13, 133, 261, 517, 41, 137, 289, 545, 641, 769, 78, 22, 134, 518, 82, 530, 194, 578, 642, 28, 140, 268, 276, 532, 88, 280, 168, 296, 200, 392, 336, 784, 224, 352, 608, 416, 672, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_301, vertices_141, vertices_789, vertices_681, vertices_865, vertices_94, vertices_206, vertices_534, vertices_850, vertices_738, vertices_284, vertices_472, vertices_424, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_261, vertices_517, vertices_41, vertices_137, vertices_289, vertices_545, vertices_641, vertices_769, vertices_78, vertices_22, vertices_134, vertices_518, vertices_82, vertices_530, vertices_194, vertices_578, vertices_642, vertices_28, vertices_140, vertices_268, vertices_276, vertices_532, vertices_88, vertices_280, vertices_168, vertices_296, vertices_200, vertices_392, vertices_336, vertices_784, vertices_224, vertices_352, vertices_608, vertices_416, vertices_672, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_301), (false, vertices_141), (false, vertices_789), (false, vertices_681), (false, vertices_865), (true, vertices_78), (true, vertices_22), (true, vertices_82), (true, vertices_530), (true, vertices_194), (true, vertices_578), (true, vertices_28), (true, vertices_88), (true, vertices_280), (true, vertices_200), (true, vertices_392), (true, vertices_336), (true, vertices_224), (true, vertices_416), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 16 else
  if p.val = (false, vertices_301) then 19 else
  if p.val = (false, vertices_141) then 0 else
  if p.val = (false, vertices_789) then 20 else
  if p.val = (false, vertices_681) then 22 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_88) then 7 else
  if p.val = (true, vertices_280) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_416) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
cert_nodeAtPriority_34 141 22 82 530 194 578 28 88 280 200 392 336 224 416 448 647 78 301 789 681 865
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 4 5 6 8 738 194 1
cert_row_4 2 0 3 5 7 8 850 82 3
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 1 4 0 2
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 3 78 94 3
cert_coverFacet 1 206
cert_cover_5 1 0 0 1 2 6 78 206 3
cert_coverFacet 2 534
cert_cover_2 2 1 0 3 8 22 534 3
cert_coverFacet 3 850
cert_cover_5 3 2 0 3 5 7 82 850 3
cert_coverFacet 4 738
cert_cover_5 4 1 0 4 5 6 194 738 1
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 472
cert_cover_5 6 3 2 3 5 6 88 472 3
cert_coverFacet 7 424
cert_cover_2 7 4 2 6 7 168 424 3
cert_coverFacet 8 480
cert_cover_2 8 5 4 6 7 224 480 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0428

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e10q1_0429.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0429

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 557, 141, 181, 369, 913, 801, 590, 346, 410, 962, 92, 156, 116, 868, 13, 37, 133, 137, 521, 49, 145, 273, 289, 545, 641, 769, 282, 74, 138, 522, 322, 578, 386, 642, 28, 76, 140, 524, 52, 84, 148, 100, 548, 580, 88, 152, 112, 336, 400, 352, 800, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_557, vertices_141, vertices_181, vertices_369, vertices_913, vertices_801, vertices_590, vertices_346, vertices_410, vertices_962, vertices_92, vertices_156, vertices_116, vertices_868] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_133, vertices_137, vertices_521, vertices_49, vertices_145, vertices_273, vertices_289, vertices_545, vertices_641, vertices_769, vertices_282, vertices_74, vertices_138, vertices_522, vertices_322, vertices_578, vertices_386, vertices_642, vertices_28, vertices_76, vertices_140, vertices_524, vertices_52, vertices_84, vertices_148, vertices_100, vertices_548, vertices_580, vertices_88, vertices_152, vertices_112, vertices_336, vertices_400, vertices_352, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_557), (false, vertices_141), (false, vertices_181), (false, vertices_369), (false, vertices_913), (false, vertices_801), (true, vertices_282), (true, vertices_74), (true, vertices_322), (true, vertices_578), (true, vertices_386), (true, vertices_28), (true, vertices_76), (true, vertices_84), (true, vertices_100), (true, vertices_580), (true, vertices_88), (true, vertices_152), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 21 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 15 else
  if p.val = (false, vertices_557) then 18 else
  if p.val = (false, vertices_141) then 0 else
  if p.val = (false, vertices_181) then 19 else
  if p.val = (false, vertices_369) then 22 else
  if p.val = (false, vertices_913) then 23 else
  if p.val = (false, vertices_801) then 1 else
  if p.val = (true, vertices_282) then 16 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_580) then 10 else
  if p.val = (true, vertices_88) then 11 else
  if p.val = (true, vertices_152) then 12 else
  if p.val = (true, vertices_832) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_141), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_801), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_282), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 7 282
cert_row_4 1 0 1 2 5 8 590 74 1
cert_row_4 2 0 5 6 7 8 962 322 2
cert_row_4 3 1 4 5 7 8 868 100 3
cert_rows
cert_pivot_2 3 2 0 1
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 1 0 1 2 5 74 590 1
cert_coverFacet 1 346
cert_cover_5 1 0 0 2 3 5 282 346 3
cert_coverFacet 2 410
cert_cover_5 2 0 0 2 3 6 282 410 3
cert_coverFacet 3 962
cert_cover_5 3 2 0 5 6 7 322 962 2
cert_coverFacet 4 92
cert_cover_2 4 2 1 3 5 28 92 3
cert_coverFacet 5 156
cert_cover_2 5 2 1 3 6 28 156 3
cert_coverFacet 6 116
cert_cover_2 6 3 1 4 5 52 116 3
cert_coverFacet 7 868
cert_cover_5 7 3 1 4 5 7 100 868 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0429

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e10q1_0430.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0430

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 565, 341, 773, 185, 217, 361, 902, 426, 178, 562, 722, 460, 596, 708, 21, 261, 517, 153, 41, 73, 49, 81, 289, 545, 321, 769, 50, 146, 530, 162, 290, 546, 386, 642, 770, 84, 532, 196, 324, 580, 388, 644, 772, 168, 296, 200, 328, 392, 176, 560, 208, 592, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_565, vertices_341, vertices_773, vertices_185, vertices_217, vertices_361, vertices_902, vertices_426, vertices_178, vertices_562, vertices_722, vertices_460, vertices_596, vertices_708] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_261, vertices_517, vertices_153, vertices_41, vertices_73, vertices_49, vertices_81, vertices_289, vertices_545, vertices_321, vertices_769, vertices_50, vertices_146, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_84, vertices_532, vertices_196, vertices_324, vertices_580, vertices_388, vertices_644, vertices_772, vertices_168, vertices_296, vertices_200, vertices_328, vertices_392, vertices_176, vertices_560, vertices_208, vertices_592, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_565), (false, vertices_341), (false, vertices_773), (false, vertices_185), (false, vertices_217), (false, vertices_361), (true, vertices_50), (true, vertices_146), (true, vertices_530), (true, vertices_162), (true, vertices_386), (true, vertices_642), (true, vertices_196), (true, vertices_580), (true, vertices_388), (true, vertices_644), (true, vertices_392), (true, vertices_592), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 19 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 15 else
  if p.val = (false, vertices_565) then 17 else
  if p.val = (false, vertices_341) then 18 else
  if p.val = (false, vertices_773) then 0 else
  if p.val = (false, vertices_185) then 20 else
  if p.val = (false, vertices_217) then 21 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
cert_nodeAtPriority_48 0 773 2 50 1 146 530 162 386 642 196 580 388 644 392 592 704 803 565 341 185 217 361
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 7 426 162 1
cert_row_4 1 0 3 5 6 8 722 146 2
cert_row_4 2 0 1 6 7 8 902 386 1
cert_row_4 3 1 2 5 6 7 460 196 1
cert_rows
cert_pivot_2 4 3 0 1
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 2 0 1 6 7 386 902 1
cert_coverFacet 1 426
cert_cover_5 1 0 0 2 4 6 162 426 1
cert_coverFacet 2 178
cert_cover_2 2 3 0 4 6 50 178 3
cert_coverFacet 3 562
cert_cover_2 3 3 0 4 8 50 562 3
cert_coverFacet 4 722
cert_cover_5 4 1 0 3 5 6 146 722 2
cert_coverFacet 5 460
cert_cover_5 5 3 1 2 5 6 196 460 1
cert_coverFacet 6 596
cert_cover_2 6 3 1 5 8 84 596 3
cert_coverFacet 7 708
cert_cover_2 7 5 1 6 8 196 708 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0430

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e10q1_0432.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0432

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 531, 707, 323, 613, 569, 361, 406, 658, 482, 796, 812, 724, 228, 420, 19, 67, 259, 515, 25, 41, 265, 529, 97, 545, 321, 577, 146, 274, 530, 194, 322, 386, 642, 780, 148, 276, 532, 100, 164, 292, 548, 196, 580, 388, 280, 536, 296, 552, 656, 224, 352, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_531, vertices_707, vertices_323, vertices_613, vertices_569, vertices_361, vertices_406, vertices_658, vertices_482, vertices_796, vertices_812, vertices_724, vertices_228, vertices_420] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_259, vertices_515, vertices_25, vertices_41, vertices_265, vertices_529, vertices_97, vertices_545, vertices_321, vertices_577, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_386, vertices_642, vertices_780, vertices_148, vertices_276, vertices_532, vertices_100, vertices_164, vertices_292, vertices_548, vertices_196, vertices_580, vertices_388, vertices_280, vertices_536, vertices_296, vertices_552, vertices_656, vertices_224, vertices_352, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_531), (false, vertices_707), (false, vertices_323), (false, vertices_613), (false, vertices_569), (false, vertices_361), (true, vertices_146), (true, vertices_386), (true, vertices_780), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_164), (true, vertices_292), (true, vertices_196), (true, vertices_388), (true, vertices_656), (true, vertices_224), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 15 else
  if p.val = (false, vertices_531) then 0 else
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_323) then 1 else
  if p.val = (false, vertices_613) then 18 else
  if p.val = (false, vertices_569) then 21 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_780) then 19 else
  if p.val = (true, vertices_148) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_656) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_416) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_531), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_780), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
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
cert_row_2 0 1 2 7 8 780
cert_row_4 1 0 4 5 6 7 482 194 1
cert_row_4 2 0 1 3 6 7 406 146 1
cert_row_4 3 1 3 5 6 8 724 148 2
cert_rows
cert_pivot_2 2 4 0 1
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 2 0 1 3 6 146 406 1
cert_coverFacet 1 658
cert_cover_2 1 3 0 6 8 146 658 3
cert_coverFacet 2 482
cert_cover_5 2 1 0 4 5 6 194 482 1
cert_coverFacet 3 796
cert_cover_5 3 0 1 2 3 7 780 796 2
cert_coverFacet 4 812
cert_cover_5 4 0 1 2 4 7 780 812 2
cert_coverFacet 5 724
cert_cover_5 5 3 1 3 5 6 148 724 2
cert_coverFacet 6 228
cert_cover_2 6 4 1 5 6 100 228 3
cert_coverFacet 7 420
cert_cover_2 7 4 1 6 7 164 420 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0432

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e10q1_0433.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0433

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [167, 803, 707, 53, 789, 645, 313, 426, 458, 850, 60, 92, 236, 724, 344, 35, 131, 515, 21, 37, 133, 517, 49, 273, 289, 641, 769, 394, 162, 290, 194, 322, 578, 770, 28, 44, 76, 52, 84, 532, 164, 196, 644, 56, 88, 280, 168, 296, 200, 328, 336, 592, 784, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_167, vertices_803, vertices_707, vertices_53, vertices_789, vertices_645, vertices_313, vertices_426, vertices_458, vertices_850, vertices_60, vertices_92, vertices_236, vertices_724, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_515, vertices_21, vertices_37, vertices_133, vertices_517, vertices_49, vertices_273, vertices_289, vertices_641, vertices_769, vertices_394, vertices_162, vertices_290, vertices_194, vertices_322, vertices_578, vertices_770, vertices_28, vertices_44, vertices_76, vertices_52, vertices_84, vertices_532, vertices_164, vertices_196, vertices_644, vertices_56, vertices_88, vertices_280, vertices_168, vertices_296, vertices_200, vertices_328, vertices_336, vertices_592, vertices_784, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_167), (false, vertices_803), (false, vertices_707), (false, vertices_53), (false, vertices_789), (false, vertices_645), (false, vertices_313), (true, vertices_394), (true, vertices_322), (true, vertices_28), (true, vertices_44), (true, vertices_76), (true, vertices_84), (true, vertices_196), (true, vertices_88), (true, vertices_168), (true, vertices_200), (true, vertices_328), (true, vertices_336), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 14 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_167) then 15 else
  if p.val = (false, vertices_803) then 18 else
  if p.val = (false, vertices_707) then 19 else
  if p.val = (false, vertices_53) then 0 else
  if p.val = (false, vertices_789) then 16 else
  if p.val = (false, vertices_645) then 1 else
  if p.val = (false, vertices_313) then 22 else
  if p.val = (true, vertices_394) then 20 else
  if p.val = (true, vertices_322) then 2 else
  if p.val = (true, vertices_28) then 3 else
  if p.val = (true, vertices_44) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_196) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_592) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_53), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_645), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 14 => Sum.inl 1
  | 15 => Sum.inr ⟨(false, vertices_167), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_394), by decide +kernel⟩
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
cert_row_4 0 1 2 4 5 6 236 44 3
cert_row_2 1 0 2 6 7 394
cert_row_4 2 0 3 5 7 8 850 322 1
cert_row_4 3 1 3 5 6 8 724 84 3
cert_rows
cert_pivot_2 4 2 0 1
cert_heightProof 4
cert_coverFacet 0 426
cert_cover_5 0 1 0 2 4 6 394 426 2
cert_coverFacet 1 458
cert_cover_5 1 1 0 2 5 6 394 458 2
cert_coverFacet 2 850
cert_cover_5 2 2 0 3 5 7 322 850 1
cert_coverFacet 3 60
cert_cover_2 3 2 1 3 4 28 60 3
cert_coverFacet 4 92
cert_cover_2 4 2 1 3 5 28 92 3
cert_coverFacet 5 236
cert_cover_5 5 0 1 2 4 5 44 236 3
cert_coverFacet 6 724
cert_cover_5 6 3 1 3 5 6 84 724 3
cert_coverFacet 7 344
cert_cover_2 7 3 2 5 7 88 344 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0433

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e10q1_0434.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0434

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [555, 205, 781, 341, 233, 865, 406, 794, 170, 394, 626, 178, 396, 244, 848, 13, 69, 261, 41, 201, 521, 97, 545, 321, 769, 42, 138, 266, 522, 50, 146, 274, 530, 162, 546, 386, 140, 268, 84, 148, 276, 196, 388, 168, 392, 776, 112, 176, 336, 592, 784, 224, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_555, vertices_205, vertices_781, vertices_341, vertices_233, vertices_865, vertices_406, vertices_794, vertices_170, vertices_394, vertices_626, vertices_178, vertices_396, vertices_244, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_261, vertices_41, vertices_201, vertices_521, vertices_97, vertices_545, vertices_321, vertices_769, vertices_42, vertices_138, vertices_266, vertices_522, vertices_50, vertices_146, vertices_274, vertices_530, vertices_162, vertices_546, vertices_386, vertices_140, vertices_268, vertices_84, vertices_148, vertices_276, vertices_196, vertices_388, vertices_168, vertices_392, vertices_776, vertices_112, vertices_176, vertices_336, vertices_592, vertices_784, vertices_224, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_555), (false, vertices_205), (false, vertices_781), (false, vertices_341), (false, vertices_233), (false, vertices_865), (true, vertices_138), (true, vertices_266), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_386), (true, vertices_148), (true, vertices_388), (true, vertices_392), (true, vertices_112), (true, vertices_176), (true, vertices_592), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_555) then 16 else
  if p.val = (false, vertices_205) then 21 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_341) then 19 else
  if p.val = (false, vertices_233) then 22 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_784) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
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
cert_row_4 0 0 2 3 7 8 794 266 2
cert_row_4 1 0 1 3 6 7 406 146 1
cert_row_4 2 0 3 4 5 8 626 50 3
cert_row_4 3 1 3 4 5 6 244 84 2
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 1 0 1 3 6 146 406 1
cert_coverFacet 1 794
cert_cover_5 1 0 0 2 3 7 266 794 2
cert_coverFacet 2 170
cert_cover_2 2 2 0 4 6 42 170 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 626
cert_cover_5 4 2 0 3 4 5 50 626 3
cert_coverFacet 5 178
cert_cover_2 5 3 0 4 6 50 178 3
cert_coverFacet 6 396
cert_cover_2 6 2 1 6 7 140 396 3
cert_coverFacet 7 244
cert_cover_5 7 3 1 3 4 5 84 244 2
cert_coverFacet 8 848
cert_cover_2 8 5 3 7 8 336 848 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0434

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e10q1_0435.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0435

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [171, 205, 333, 809, 849, 737, 406, 794, 554, 394, 626, 178, 396, 244, 340, 77, 41, 137, 265, 161, 545, 193, 321, 577, 769, 42, 138, 266, 522, 50, 146, 274, 530, 162, 546, 386, 140, 268, 84, 148, 276, 196, 324, 388, 552, 392, 776, 112, 176, 336, 592, 784, 224, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_171, vertices_205, vertices_333, vertices_809, vertices_849, vertices_737, vertices_406, vertices_794, vertices_554, vertices_394, vertices_626, vertices_178, vertices_396, vertices_244, vertices_340] (by decide +kernel)
  polygons := literalFinset [vertices_77, vertices_41, vertices_137, vertices_265, vertices_161, vertices_545, vertices_193, vertices_321, vertices_577, vertices_769, vertices_42, vertices_138, vertices_266, vertices_522, vertices_50, vertices_146, vertices_274, vertices_530, vertices_162, vertices_546, vertices_386, vertices_140, vertices_268, vertices_84, vertices_148, vertices_276, vertices_196, vertices_324, vertices_388, vertices_552, vertices_392, vertices_776, vertices_112, vertices_176, vertices_336, vertices_592, vertices_784, vertices_224, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_171), (false, vertices_205), (false, vertices_333), (false, vertices_809), (false, vertices_849), (false, vertices_737), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_546), (true, vertices_386), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_388), (true, vertices_392), (true, vertices_112), (true, vertices_176)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_171) then 16 else
  if p.val = (false, vertices_205) then 18 else
  if p.val = (false, vertices_333) then 19 else
  if p.val = (false, vertices_809) then 21 else
  if p.val = (false, vertices_849) then 23 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_266) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_176) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_171), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
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
cert_row_4 0 0 2 3 7 8 794 266 2
cert_row_4 1 0 1 3 6 7 406 146 1
cert_row_4 2 0 3 4 5 8 626 50 3
cert_row_4 3 1 3 4 5 6 244 84 2
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 1 0 1 3 6 146 406 1
cert_coverFacet 1 794
cert_cover_5 1 0 0 2 3 7 266 794 2
cert_coverFacet 2 554
cert_cover_2 2 2 0 4 8 42 554 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 626
cert_cover_5 4 2 0 3 4 5 50 626 3
cert_coverFacet 5 178
cert_cover_2 5 3 0 4 6 50 178 3
cert_coverFacet 6 396
cert_cover_2 6 2 1 6 7 140 396 3
cert_coverFacet 7 244
cert_cover_5 7 3 1 3 4 5 84 244 2
cert_coverFacet 8 340
cert_cover_2 8 3 1 5 7 84 340 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0435

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e10q1_0436.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0436

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 555, 787, 163, 205, 781, 233, 626, 178, 402, 348, 244, 404, 872, 848, 35, 131, 259, 515, 13, 133, 261, 41, 201, 521, 161, 769, 50, 146, 274, 530, 162, 546, 386, 76, 268, 84, 148, 276, 196, 388, 104, 552, 328, 776, 112, 176, 336, 592, 400, 784, 224, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_555, vertices_787, vertices_163, vertices_205, vertices_781, vertices_233, vertices_626, vertices_178, vertices_402, vertices_348, vertices_244, vertices_404, vertices_872, vertices_848] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_13, vertices_133, vertices_261, vertices_41, vertices_201, vertices_521, vertices_161, vertices_769, vertices_50, vertices_146, vertices_274, vertices_530, vertices_162, vertices_546, vertices_386, vertices_76, vertices_268, vertices_84, vertices_148, vertices_276, vertices_196, vertices_388, vertices_104, vertices_552, vertices_328, vertices_776, vertices_112, vertices_176, vertices_336, vertices_592, vertices_400, vertices_784, vertices_224, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_555), (false, vertices_787), (false, vertices_163), (false, vertices_205), (false, vertices_781), (false, vertices_233), (true, vertices_50), (true, vertices_146), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_328), (true, vertices_112), (true, vertices_176), (true, vertices_336), (true, vertices_592), (true, vertices_400), (true, vertices_608), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 15 else
  if p.val = (false, vertices_555) then 16 else
  if p.val = (false, vertices_787) then 17 else
  if p.val = (false, vertices_163) then 0 else
  if p.val = (false, vertices_205) then 21 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_233) then 22 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_84) then 3 else
  if p.val = (true, vertices_148) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_328) then 6 else
  if p.val = (true, vertices_112) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_400) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_832) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_163), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 5 8 626 50 3
cert_row_4 1 1 3 4 5 6 244 84 2
cert_row_4 2 1 2 3 5 7 348 76 2
cert_row_4 3 2 4 5 7 8 872 104 3
cert_rows
cert_pivot_2 0 6 1 2
cert_heightProof 4
cert_coverFacet 0 626
cert_cover_5 0 0 0 3 4 5 50 626 3
cert_coverFacet 1 178
cert_cover_2 1 3 0 4 6 50 178 3
cert_coverFacet 2 402
cert_cover_2 2 3 0 6 7 146 402 3
cert_coverFacet 3 348
cert_cover_5 3 2 1 2 3 5 76 348 2
cert_coverFacet 4 244
cert_cover_5 4 1 1 3 4 5 84 244 2
cert_coverFacet 5 404
cert_cover_2 5 3 1 6 7 148 404 3
cert_coverFacet 6 872
cert_cover_5 6 3 2 4 5 7 104 872 3
cert_coverFacet 7 848
cert_cover_2 7 5 3 7 8 336 848 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0436

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m15e10q1_0437.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0437

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 299, 541, 617, 849, 481, 30, 46, 150, 230, 434, 108, 716, 916, 960, 267, 25, 41, 521, 273, 529, 97, 289, 321, 577, 14, 22, 38, 134, 26, 42, 146, 274, 162, 290, 28, 44, 76, 524, 148, 532, 100, 196, 644, 104, 584, 400, 784, 224, 416, 448, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_299, vertices_541, vertices_617, vertices_849, vertices_481, vertices_30, vertices_46, vertices_150, vertices_230, vertices_434, vertices_108, vertices_716, vertices_916, vertices_960] (by decide +kernel)
  polygons := literalFinset [vertices_267, vertices_25, vertices_41, vertices_521, vertices_273, vertices_529, vertices_97, vertices_289, vertices_321, vertices_577, vertices_14, vertices_22, vertices_38, vertices_134, vertices_26, vertices_42, vertices_146, vertices_274, vertices_162, vertices_290, vertices_28, vertices_44, vertices_76, vertices_524, vertices_148, vertices_532, vertices_100, vertices_196, vertices_644, vertices_104, vertices_584, vertices_400, vertices_784, vertices_224, vertices_416, vertices_448, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_299), (false, vertices_541), (false, vertices_617), (false, vertices_849), (false, vertices_481), (true, vertices_14), (true, vertices_22), (true, vertices_38), (true, vertices_134), (true, vertices_146), (true, vertices_162), (true, vertices_44), (true, vertices_76), (true, vertices_148), (true, vertices_100), (true, vertices_196), (true, vertices_644), (true, vertices_400), (true, vertices_704), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 16 else
  if p.val = (false, vertices_299) then 17 else
  if p.val = (false, vertices_541) then 19 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (false, vertices_849) then 23 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_134) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_644) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_704) then 13 else
  if p.val = (true, vertices_896) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 5 6 8 716 76 3
cert_row_4 1 0 1 4 5 6 230 38 3
cert_row_4 2 0 3 4 6 7 434 146 2
cert_row_4 3 1 3 6 7 8 916 148 3
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 46
cert_cover_2 1 1 0 2 4 14 46 3
cert_coverFacet 2 150
cert_cover_2 2 1 0 3 6 22 150 3
cert_coverFacet 3 230
cert_cover_5 3 1 0 1 4 5 38 230 3
cert_coverFacet 4 434
cert_cover_5 4 2 0 3 4 6 146 434 2
cert_coverFacet 5 108
cert_cover_2 5 2 1 4 5 44 108 3
cert_coverFacet 6 716
cert_cover_5 6 0 1 2 5 6 76 716 3
cert_coverFacet 7 916
cert_cover_5 7 3 1 3 6 7 148 916 3
cert_coverFacet 8 960
cert_cover_2 8 6 5 7 8 448 960 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0437

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m15e10q1_0438.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0438

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [307, 333, 805, 709, 345, 625, 782, 154, 282, 682, 242, 802, 220, 652, 736, 69, 261, 517, 329, 49, 81, 273, 289, 545, 577, 26, 138, 266, 522, 50, 146, 274, 162, 290, 546, 770, 76, 140, 268, 524, 196, 644, 772, 88, 152, 280, 648, 112, 208, 224, 608, 672, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_333, vertices_805, vertices_709, vertices_345, vertices_625, vertices_782, vertices_154, vertices_282, vertices_682, vertices_242, vertices_802, vertices_220, vertices_652, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_329, vertices_49, vertices_81, vertices_273, vertices_289, vertices_545, vertices_577, vertices_26, vertices_138, vertices_266, vertices_522, vertices_50, vertices_146, vertices_274, vertices_162, vertices_290, vertices_546, vertices_770, vertices_76, vertices_140, vertices_268, vertices_524, vertices_196, vertices_644, vertices_772, vertices_88, vertices_152, vertices_280, vertices_648, vertices_112, vertices_208, vertices_224, vertices_608, vertices_672, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_333), (false, vertices_805), (false, vertices_709), (false, vertices_345), (false, vertices_625), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_162), (true, vertices_546), (true, vertices_770), (true, vertices_140), (true, vertices_524), (true, vertices_152), (true, vertices_648), (true, vertices_208), (true, vertices_224), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 16 else
  if p.val = (false, vertices_333) then 21 else
  if p.val = (false, vertices_805) then 18 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_345) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_648) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_672) then 14 else
  0
cert_priority
cert_nodeAtPriority_52 26 1 138 2 266 522 146 162 546 770 140 524 152 648 208 224 672 307 805 709 333 345 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 266 1
cert_row_4 1 0 2 4 6 8 682 138 2
cert_row_4 2 0 3 4 5 6 242 50 3
cert_row_4 3 1 2 3 5 6 220 76 2
cert_rows
cert_pivot_2 7 8 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 266 782 1
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 682
cert_cover_5 3 1 0 2 4 6 138 682 2
cert_coverFacet 4 242
cert_cover_5 4 2 0 3 4 5 50 242 3
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 220
cert_cover_5 6 3 1 2 3 5 76 220 2
cert_coverFacet 7 652
cert_cover_2 7 2 1 6 8 140 652 3
cert_coverFacet 8 736
cert_cover_2 8 5 4 6 8 224 736 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0438

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m15e10q1_0440.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0440

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 677, 293, 453, 841, 721, 158, 174, 602, 298, 778, 690, 92, 364, 212, 37, 133, 261, 289, 545, 193, 321, 577, 641, 769, 142, 26, 42, 266, 522, 146, 530, 162, 290, 546, 770, 28, 44, 76, 84, 148, 164, 292, 196, 324, 88, 296, 328, 584, 776, 208, 592, 656, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_677, vertices_293, vertices_453, vertices_841, vertices_721, vertices_158, vertices_174, vertices_602, vertices_298, vertices_778, vertices_690, vertices_92, vertices_364, vertices_212] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_142, vertices_26, vertices_42, vertices_266, vertices_522, vertices_146, vertices_530, vertices_162, vertices_290, vertices_546, vertices_770, vertices_28, vertices_44, vertices_76, vertices_84, vertices_148, vertices_164, vertices_292, vertices_196, vertices_324, vertices_88, vertices_296, vertices_328, vertices_584, vertices_776, vertices_208, vertices_592, vertices_656, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_677), (false, vertices_293), (false, vertices_453), (false, vertices_841), (false, vertices_721), (true, vertices_142), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_530), (true, vertices_162), (true, vertices_28), (true, vertices_44), (true, vertices_76), (true, vertices_84), (true, vertices_148), (true, vertices_88), (true, vertices_296)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_677) then 19 else
  if p.val = (false, vertices_293) then 0 else
  if p.val = (false, vertices_453) then 20 else
  if p.val = (false, vertices_841) then 22 else
  if p.val = (false, vertices_721) then 24 else
  if p.val = (true, vertices_142) then 17 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_162) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_76) then 10 else
  if p.val = (true, vertices_84) then 11 else
  if p.val = (true, vertices_148) then 12 else
  if p.val = (true, vertices_88) then 13 else
  if p.val = (true, vertices_296) then 14 else
  0
cert_priority
cert_nodeAtPriority_22 293 26 42 266 522 146 530 162 28 44 76 84 148 88 296 803 142 677 453 841 721
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 4 5 7 364 44 3
cert_row_2 1 0 1 2 6 142
cert_row_4 2 0 2 3 5 8 602 26 3
cert_row_4 3 0 3 4 6 8 690 146 2
cert_rows
cert_pivot_2 7 1 2 0
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 1 0 1 2 3 142 158 3
cert_coverFacet 1 174
cert_cover_5 1 1 0 1 2 4 142 174 3
cert_coverFacet 2 602
cert_cover_5 2 2 0 2 3 5 26 602 3
cert_coverFacet 3 298
cert_cover_2 3 2 0 4 7 42 298 3
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 690
cert_cover_5 5 3 0 3 4 6 146 690 2
cert_coverFacet 6 92
cert_cover_2 6 2 1 3 5 28 92 3
cert_coverFacet 7 364
cert_cover_5 7 0 1 2 4 5 44 364 3
cert_coverFacet 8 212
cert_cover_2 8 3 1 5 6 84 212 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0440

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m15e10q1_0441.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0441

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 837, 793, 361, 169, 737, 118, 790, 710, 154, 538, 242, 316, 356, 184, 41, 137, 265, 521, 97, 161, 321, 577, 641, 769, 22, 70, 518, 26, 138, 522, 114, 146, 530, 194, 642, 52, 276, 100, 292, 324, 580, 772, 56, 152, 280, 536, 168, 296, 176, 784, 224, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_837, vertices_793, vertices_361, vertices_169, vertices_737, vertices_118, vertices_790, vertices_710, vertices_154, vertices_538, vertices_242, vertices_316, vertices_356, vertices_184] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_137, vertices_265, vertices_521, vertices_97, vertices_161, vertices_321, vertices_577, vertices_641, vertices_769, vertices_22, vertices_70, vertices_518, vertices_26, vertices_138, vertices_522, vertices_114, vertices_146, vertices_530, vertices_194, vertices_642, vertices_52, vertices_276, vertices_100, vertices_292, vertices_324, vertices_580, vertices_772, vertices_56, vertices_152, vertices_280, vertices_536, vertices_168, vertices_296, vertices_176, vertices_784, vertices_224, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_837), (false, vertices_793), (false, vertices_361), (false, vertices_169), (false, vertices_737), (true, vertices_22), (true, vertices_70), (true, vertices_518), (true, vertices_26), (true, vertices_114), (true, vertices_146), (true, vertices_530), (true, vertices_194), (true, vertices_52), (true, vertices_276), (true, vertices_100), (true, vertices_292), (true, vertices_56), (true, vertices_152), (true, vertices_176)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 16 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_793) then 21 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_169) then 0 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_114) then 17 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_100) then 10 else
  if p.val = (true, vertices_292) then 11 else
  if p.val = (true, vertices_56) then 12 else
  if p.val = (true, vertices_152) then 13 else
  if p.val = (true, vertices_176) then 14 else
  0
cert_priority
cert_nodeAtPriority_32 169 22 70 518 26 146 530 194 52 276 100 292 56 152 176 651 114 837 793 361 737
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 8 710 70 3
cert_row_2 1 0 3 4 5 114
cert_row_4 2 0 1 3 7 8 790 22 3
cert_row_4 3 1 2 3 4 7 316 52 1
cert_rows
cert_pivot_2 6 5 0 1
cert_heightProof 4
cert_coverFacet 0 118
cert_cover_5 0 1 0 1 3 4 22 118 3
cert_coverFacet 1 790
cert_cover_5 1 2 0 1 3 7 22 790 3
cert_coverFacet 2 710
cert_cover_5 2 0 0 1 5 6 70 710 3
cert_coverFacet 3 154
cert_cover_2 3 2 0 3 6 26 154 3
cert_coverFacet 4 538
cert_cover_2 4 2 0 3 8 26 538 3
cert_coverFacet 5 242
cert_cover_5 5 1 0 3 4 6 114 242 3
cert_coverFacet 6 316
cert_cover_5 6 3 1 2 3 4 52 316 1
cert_coverFacet 7 356
cert_cover_2 7 4 1 5 7 100 356 3
cert_coverFacet 8 184
cert_cover_2 8 3 2 4 6 56 184 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0441

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m15e10q1_0442.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0442

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 613, 841, 113, 689, 465, 142, 782, 678, 346, 154, 402, 124, 188, 588, 49, 81, 145, 97, 545, 321, 577, 385, 641, 769, 14, 134, 518, 26, 138, 266, 146, 274, 386, 642, 770, 60, 76, 140, 524, 100, 164, 548, 580, 88, 152, 328, 584, 776, 112, 176, 336, 400, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_613, vertices_841, vertices_113, vertices_689, vertices_465, vertices_142, vertices_782, vertices_678, vertices_346, vertices_154, vertices_402, vertices_124, vertices_188, vertices_588] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_81, vertices_145, vertices_97, vertices_545, vertices_321, vertices_577, vertices_385, vertices_641, vertices_769, vertices_14, vertices_134, vertices_518, vertices_26, vertices_138, vertices_266, vertices_146, vertices_274, vertices_386, vertices_642, vertices_770, vertices_60, vertices_76, vertices_140, vertices_524, vertices_100, vertices_164, vertices_548, vertices_580, vertices_88, vertices_152, vertices_328, vertices_584, vertices_776, vertices_112, vertices_176, vertices_336, vertices_400, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_613), (false, vertices_841), (false, vertices_113), (false, vertices_689), (false, vertices_465), (true, vertices_14), (true, vertices_134), (true, vertices_518), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_146), (true, vertices_274), (true, vertices_60), (true, vertices_76), (true, vertices_140), (true, vertices_524), (true, vertices_164), (true, vertices_88), (true, vertices_152)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 16 else
  if p.val = (false, vertices_613) then 18 else
  if p.val = (false, vertices_841) then 21 else
  if p.val = (false, vertices_113) then 0 else
  if p.val = (false, vertices_689) then 23 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_146) then 7 else
  if p.val = (true, vertices_274) then 8 else
  if p.val = (true, vertices_60) then 19 else
  if p.val = (true, vertices_76) then 9 else
  if p.val = (true, vertices_140) then 10 else
  if p.val = (true, vertices_524) then 11 else
  if p.val = (true, vertices_164) then 12 else
  if p.val = (true, vertices_88) then 13 else
  if p.val = (true, vertices_152) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_113), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_60), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
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
cert_row_4 0 0 1 4 6 8 678 134 2
cert_row_2 1 1 2 3 4 60
cert_row_4 2 0 1 2 7 8 782 14 3
cert_row_4 3 0 2 3 5 7 346 26 3
cert_rows
cert_pivot_2 6 4 1 0
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 782
cert_cover_5 1 2 0 1 2 7 14 782 3
cert_coverFacet 2 678
cert_cover_5 2 0 0 1 4 6 134 678 2
cert_coverFacet 3 346
cert_cover_5 3 3 0 2 3 5 26 346 3
cert_coverFacet 4 154
cert_cover_2 4 2 0 3 6 26 154 3
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 124
cert_cover_5 6 1 1 2 3 5 60 124 3
cert_coverFacet 7 188
cert_cover_5 7 1 1 2 3 6 60 188 3
cert_coverFacet 8 588
cert_cover_2 8 2 1 5 8 76 588 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0442

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m15e10q1_0443.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0443

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 173, 333, 613, 425, 849, 678, 154, 794, 394, 722, 418, 220, 708, 344, 13, 37, 69, 169, 265, 289, 545, 321, 577, 769, 26, 138, 266, 146, 530, 162, 290, 546, 386, 642, 770, 76, 140, 164, 548, 196, 580, 644, 88, 152, 280, 328, 392, 208, 336, 592, 784, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_173, vertices_333, vertices_613, vertices_425, vertices_849, vertices_678, vertices_154, vertices_794, vertices_394, vertices_722, vertices_418, vertices_220, vertices_708, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_69, vertices_169, vertices_265, vertices_289, vertices_545, vertices_321, vertices_577, vertices_769, vertices_26, vertices_138, vertices_266, vertices_146, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_76, vertices_140, vertices_164, vertices_548, vertices_196, vertices_580, vertices_644, vertices_88, vertices_152, vertices_280, vertices_328, vertices_392, vertices_208, vertices_336, vertices_592, vertices_784, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_173), (false, vertices_333), (false, vertices_613), (false, vertices_425), (false, vertices_849), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_146), (true, vertices_530), (true, vertices_162), (true, vertices_386), (true, vertices_642), (true, vertices_196), (true, vertices_644), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_208), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_173) then 21 else
  if p.val = (false, vertices_333) then 18 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_425) then 22 else
  if p.val = (false, vertices_849) then 24 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
cert_nodeAtPriority_52 26 1 138 2 266 146 530 162 386 642 196 644 88 152 280 208 704 803 333 613 173 425 849
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 162 1
cert_row_4 1 0 2 3 7 8 794 26 3
cert_row_4 2 0 3 5 6 8 722 146 2
cert_row_4 3 1 2 3 5 6 220 76 2
cert_rows
cert_pivot_2 4 7 0 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 0 0 1 4 6 162 678 1
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 794
cert_cover_5 2 1 0 2 3 7 26 794 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 722
cert_cover_5 4 2 0 3 5 6 146 722 2
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 220
cert_cover_5 6 3 1 2 3 5 76 220 2
cert_coverFacet 7 708
cert_cover_2 7 5 1 6 8 196 708 3
cert_coverFacet 8 344
cert_cover_2 8 3 2 5 7 88 344 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0443

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m15e10q1_0444.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0444

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 789, 313, 601, 105, 929, 214, 598, 902, 234, 674, 156, 284, 428, 216, 25, 41, 73, 273, 529, 97, 289, 545, 577, 769, 86, 134, 518, 98, 162, 546, 194, 578, 642, 28, 140, 268, 148, 276, 532, 388, 772, 88, 152, 280, 104, 168, 296, 200, 208, 592, 416, 672, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_789, vertices_313, vertices_601, vertices_105, vertices_929, vertices_214, vertices_598, vertices_902, vertices_234, vertices_674, vertices_156, vertices_284, vertices_428, vertices_216] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_73, vertices_273, vertices_529, vertices_97, vertices_289, vertices_545, vertices_577, vertices_769, vertices_86, vertices_134, vertices_518, vertices_98, vertices_162, vertices_546, vertices_194, vertices_578, vertices_642, vertices_28, vertices_140, vertices_268, vertices_148, vertices_276, vertices_532, vertices_388, vertices_772, vertices_88, vertices_152, vertices_280, vertices_104, vertices_168, vertices_296, vertices_200, vertices_208, vertices_592, vertices_416, vertices_672, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_789), (false, vertices_313), (false, vertices_601), (false, vertices_105), (false, vertices_929), (true, vertices_86), (true, vertices_134), (true, vertices_518), (true, vertices_162), (true, vertices_194), (true, vertices_642), (true, vertices_28), (true, vertices_140), (true, vertices_268), (true, vertices_148), (true, vertices_388), (true, vertices_152), (true, vertices_168), (true, vertices_200), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 16 else
  if p.val = (false, vertices_789) then 19 else
  if p.val = (false, vertices_313) then 21 else
  if p.val = (false, vertices_601) then 22 else
  if p.val = (false, vertices_105) then 0 else
  if p.val = (false, vertices_929) then 25 else
  if p.val = (true, vertices_86) then 17 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_200) then 13 else
  if p.val = (true, vertices_208) then 14 else
  0
cert_priority
cert_nodeAtPriority_32 105 134 518 162 194 642 28 140 268 148 388 152 168 200 208 611 86 789 313 601 929
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 5 86
cert_row_4 1 0 1 6 7 8 902 134 3
cert_row_4 2 0 2 4 5 6 234 98 1
cert_row_4 3 1 2 4 6 7 428 140 2
cert_rows
cert_pivot_2 3 8 0 1
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 6 86 214 3
cert_coverFacet 1 598
cert_cover_5 1 0 0 1 3 8 86 598 3
cert_coverFacet 2 902
cert_cover_5 2 1 0 1 6 7 134 902 3
cert_coverFacet 3 234
cert_cover_5 3 2 0 2 4 5 98 234 1
cert_coverFacet 4 674
cert_cover_2 4 4 0 6 8 162 674 3
cert_coverFacet 5 156
cert_cover_2 5 2 1 3 6 28 156 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 428
cert_cover_5 7 3 1 2 4 6 140 428 2
cert_coverFacet 8 216
cert_cover_2 8 3 2 5 6 88 216 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0444

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e10q1_0445.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0445

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [707, 285, 661, 357, 581, 465, 614, 666, 234, 810, 540, 780, 804, 408, 488, 21, 69, 261, 517, 145, 273, 193, 321, 577, 641, 42, 138, 522, 98, 546, 194, 578, 642, 28, 268, 524, 532, 100, 292, 548, 580, 772, 152, 280, 536, 232, 296, 392, 776, 400, 656, 352, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_707, vertices_285, vertices_661, vertices_357, vertices_581, vertices_465, vertices_614, vertices_666, vertices_234, vertices_810, vertices_540, vertices_780, vertices_804, vertices_408, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_69, vertices_261, vertices_517, vertices_145, vertices_273, vertices_193, vertices_321, vertices_577, vertices_641, vertices_42, vertices_138, vertices_522, vertices_98, vertices_546, vertices_194, vertices_578, vertices_642, vertices_28, vertices_268, vertices_524, vertices_532, vertices_100, vertices_292, vertices_548, vertices_580, vertices_772, vertices_152, vertices_280, vertices_536, vertices_232, vertices_296, vertices_392, vertices_776, vertices_400, vertices_656, vertices_352, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_707), (false, vertices_285), (false, vertices_661), (false, vertices_357), (false, vertices_581), (false, vertices_465), (true, vertices_42), (true, vertices_138), (true, vertices_522), (true, vertices_98), (true, vertices_546), (true, vertices_524), (true, vertices_548), (true, vertices_772), (true, vertices_152), (true, vertices_536), (true, vertices_232), (true, vertices_296), (true, vertices_392), (true, vertices_776), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_285) then 18 else
  if p.val = (false, vertices_661) then 19 else
  if p.val = (false, vertices_357) then 20 else
  if p.val = (false, vertices_581) then 0 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_524) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_232) then 22 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_776) then 13 else
  if p.val = (true, vertices_800) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_581), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_285), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(true, vertices_232), by decide +kernel⟩
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
cert_row_4 0 0 1 4 5 8 614 98 1
cert_row_2 1 2 4 5 6 232
cert_row_4 2 0 2 3 6 8 666 138 2
cert_row_4 3 0 2 4 7 8 810 42 3
cert_rows
cert_pivot_2 1 5 3 0
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_5 0 0 0 1 4 5 98 614 1
cert_coverFacet 1 666
cert_cover_5 1 2 0 2 3 6 138 666 2
cert_coverFacet 2 234
cert_cover_5 2 1 0 2 4 5 42 234 3
cert_coverFacet 3 810
cert_cover_5 3 3 0 2 4 7 42 810 3
cert_coverFacet 4 540
cert_cover_2 4 2 1 3 8 28 540 3
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 804
cert_cover_2 6 4 1 7 8 292 804 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 488
cert_cover_5 8 1 2 4 5 7 232 488 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0445

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e10q1_0446.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0446

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 421, 709, 809, 689, 590, 342, 314, 218, 778, 468, 568, 664, 712, 432, 133, 261, 517, 161, 289, 545, 641, 769, 70, 262, 518, 26, 74, 266, 522, 82, 274, 770, 340, 196, 580, 388, 56, 152, 536, 296, 552, 200, 584, 648, 776, 176, 304, 560, 208, 400, 656, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_421, vertices_709, vertices_809, vertices_689, vertices_590, vertices_342, vertices_314, vertices_218, vertices_778, vertices_468, vertices_568, vertices_664, vertices_712, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_161, vertices_289, vertices_545, vertices_641, vertices_769, vertices_70, vertices_262, vertices_518, vertices_26, vertices_74, vertices_266, vertices_522, vertices_82, vertices_274, vertices_770, vertices_340, vertices_196, vertices_580, vertices_388, vertices_56, vertices_152, vertices_536, vertices_296, vertices_552, vertices_200, vertices_584, vertices_648, vertices_776, vertices_176, vertices_304, vertices_560, vertices_208, vertices_400, vertices_656, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_421), (false, vertices_709), (false, vertices_809), (false, vertices_689), (true, vertices_70), (true, vertices_26), (true, vertices_74), (true, vertices_266), (true, vertices_522), (true, vertices_82), (true, vertices_274), (true, vertices_340), (true, vertices_56), (true, vertices_152), (true, vertices_536), (true, vertices_200), (true, vertices_584), (true, vertices_648), (true, vertices_304), (true, vertices_208), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_421) then 19 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_809) then 23 else
  if p.val = (false, vertices_689) then 25 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_340) then 21 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_200) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_400) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_340), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 70 2
cert_row_2 1 1 3 5 7 340
cert_row_4 2 0 2 3 4 7 314 26 3
cert_row_4 3 0 2 3 5 6 218 26 3
cert_rows
cert_pivot_2 8 1 4 0
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 70 590 2
cert_coverFacet 1 342
cert_cover_5 1 1 0 1 3 5 70 342 2
cert_coverFacet 2 314
cert_cover_5 2 2 0 2 3 4 26 314 3
cert_coverFacet 3 218
cert_cover_5 3 3 0 2 3 5 26 218 3
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 468
cert_cover_5 5 1 1 3 5 6 340 468 3
cert_coverFacet 6 568
cert_cover_2 6 3 2 4 8 56 568 3
cert_coverFacet 7 664
cert_cover_2 7 3 2 6 8 152 664 3
cert_coverFacet 8 712
cert_cover_2 8 5 2 6 8 200 712 3
cert_coverFacet 9 432
cert_cover_2 9 4 3 6 7 176 432 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0446

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e10q1_0447.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0447

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 653, 453, 217, 617, 833, 406, 662, 314, 538, 554, 866, 120, 664, 496, 133, 261, 517, 73, 137, 521, 193, 321, 577, 769, 150, 262, 518, 26, 42, 522, 274, 530, 290, 546, 770, 388, 644, 56, 88, 152, 536, 104, 552, 648, 112, 304, 208, 400, 656, 352, 608, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_653, vertices_453, vertices_217, vertices_617, vertices_833, vertices_406, vertices_662, vertices_314, vertices_538, vertices_554, vertices_866, vertices_120, vertices_664, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_521, vertices_193, vertices_321, vertices_577, vertices_769, vertices_150, vertices_262, vertices_518, vertices_26, vertices_42, vertices_522, vertices_274, vertices_530, vertices_290, vertices_546, vertices_770, vertices_388, vertices_644, vertices_56, vertices_88, vertices_152, vertices_536, vertices_104, vertices_552, vertices_648, vertices_112, vertices_304, vertices_208, vertices_400, vertices_656, vertices_352, vertices_608, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_653), (false, vertices_453), (false, vertices_217), (false, vertices_617), (false, vertices_833), (true, vertices_150), (true, vertices_26), (true, vertices_42), (true, vertices_522), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_546), (true, vertices_56), (true, vertices_536), (true, vertices_112), (true, vertices_304), (true, vertices_400), (true, vertices_656), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 16 else
  if p.val = (false, vertices_653) then 19 else
  if p.val = (false, vertices_453) then 20 else
  if p.val = (false, vertices_217) then 22 else
  if p.val = (false, vertices_617) then 23 else
  if p.val = (false, vertices_833) then 0 else
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
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_656) then 13 else
  if p.val = (true, vertices_352) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_833), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_150), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
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
cert_row_4 1 0 2 3 4 7 314 26 3
cert_row_4 2 0 4 5 7 8 866 290 2
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 0 0 1 3 7 150 406 3
cert_coverFacet 1 662
cert_cover_5 1 0 0 1 3 8 150 662 3
cert_coverFacet 2 314
cert_cover_5 2 1 0 2 3 4 26 314 3
cert_coverFacet 3 538
cert_cover_2 3 2 0 3 8 26 538 3
cert_coverFacet 4 554
cert_cover_2 4 2 0 4 8 42 554 3
cert_coverFacet 5 866
cert_cover_5 5 2 0 4 5 7 290 866 2
cert_coverFacet 6 120
cert_cover_2 6 3 2 4 5 56 120 3
cert_coverFacet 7 664
cert_cover_2 7 3 2 6 8 152 664 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 112 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0447

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e10q1_0448.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0448

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [107, 781, 661, 421, 297, 585, 737, 790, 58, 282, 842, 242, 722, 404, 440, 133, 261, 517, 41, 73, 265, 521, 97, 161, 289, 577, 641, 26, 42, 74, 266, 50, 210, 274, 530, 98, 578, 770, 148, 276, 532, 388, 772, 56, 280, 296, 584, 776, 176, 400, 656, 224, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_107, vertices_781, vertices_661, vertices_421, vertices_297, vertices_585, vertices_737, vertices_790, vertices_58, vertices_282, vertices_842, vertices_242, vertices_722, vertices_404, vertices_440] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_41, vertices_73, vertices_265, vertices_521, vertices_97, vertices_161, vertices_289, vertices_577, vertices_641, vertices_26, vertices_42, vertices_74, vertices_266, vertices_50, vertices_210, vertices_274, vertices_530, vertices_98, vertices_578, vertices_770, vertices_148, vertices_276, vertices_532, vertices_388, vertices_772, vertices_56, vertices_280, vertices_296, vertices_584, vertices_776, vertices_176, vertices_400, vertices_656, vertices_224, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_107), (false, vertices_781), (false, vertices_661), (false, vertices_421), (false, vertices_297), (false, vertices_585), (false, vertices_737), (true, vertices_26), (true, vertices_266), (true, vertices_50), (true, vertices_210), (true, vertices_274), (true, vertices_530), (true, vertices_578), (true, vertices_770), (true, vertices_276), (true, vertices_56), (true, vertices_280), (true, vertices_176), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_107) then 15 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_661) then 19 else
  if p.val = (false, vertices_421) then 20 else
  if p.val = (false, vertices_297) then 0 else
  if p.val = (false, vertices_585) then 1 else
  if p.val = (false, vertices_737) then 24 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_210) then 16 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_400) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_297), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_585), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_107), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_210), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 21 => Sum.inl 2
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
cert_row_4 1 0 2 5 7 8 842 74 3
cert_row_2 2 0 3 5 6 210
cert_row_4 3 2 3 4 6 7 440 56 3
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 842
cert_cover_5 3 1 0 2 5 7 74 842 3
cert_coverFacet 4 242
cert_cover_5 4 2 0 3 4 5 50 242 3
cert_coverFacet 5 722
cert_cover_5 5 2 0 3 5 8 210 722 3
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 440
cert_cover_5 7 3 2 3 4 6 56 440 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0448

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e10q1_0449.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0449

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [307, 157, 525, 277, 805, 713, 689, 342, 842, 242, 738, 802, 460, 780, 212, 13, 21, 261, 517, 137, 521, 49, 145, 273, 289, 545, 641, 50, 82, 274, 226, 290, 546, 322, 578, 770, 140, 268, 524, 84, 148, 276, 196, 324, 772, 200, 328, 584, 776, 176, 208, 672, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_157, vertices_525, vertices_277, vertices_805, vertices_713, vertices_689, vertices_342, vertices_842, vertices_242, vertices_738, vertices_802, vertices_460, vertices_780, vertices_212] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_261, vertices_517, vertices_137, vertices_521, vertices_49, vertices_145, vertices_273, vertices_289, vertices_545, vertices_641, vertices_50, vertices_82, vertices_274, vertices_226, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_140, vertices_268, vertices_524, vertices_84, vertices_148, vertices_276, vertices_196, vertices_324, vertices_772, vertices_200, vertices_328, vertices_584, vertices_776, vertices_176, vertices_208, vertices_672, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_157), (false, vertices_525), (false, vertices_277), (false, vertices_805), (false, vertices_713), (false, vertices_689), (true, vertices_82), (true, vertices_226), (true, vertices_546), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_268), (true, vertices_84), (true, vertices_196), (true, vertices_324), (true, vertices_328), (true, vertices_776), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 15 else
  if p.val = (false, vertices_157) then 18 else
  if p.val = (false, vertices_525) then 0 else
  if p.val = (false, vertices_277) then 1 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_713) then 21 else
  if p.val = (false, vertices_689) then 23 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_226) then 16 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_208) then 13 else
  0
cert_priority
cert_nodeAtPriority_27 0 525 1 277 82 546 322 578 770 268 84 196 324 328 776 208 307 226 157 805 713 689
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
cert_coverFacet 3 738
cert_cover_5 3 0 0 4 5 8 226 738 3
cert_coverFacet 4 802
cert_cover_2 4 4 0 7 8 290 802 3
cert_coverFacet 5 460
cert_cover_5 5 3 1 2 5 6 140 460 2
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 212
cert_cover_2 7 3 1 5 6 84 212 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0449

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m15e10q1_0450.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0450

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 117, 661, 805, 361, 593, 902, 234, 330, 394, 722, 316, 412, 184, 240, 21, 37, 517, 81, 529, 97, 289, 321, 577, 769, 74, 138, 266, 194, 322, 578, 386, 642, 770, 284, 52, 148, 292, 388, 644, 772, 56, 152, 104, 168, 296, 328, 392, 112, 176, 208, 592, 656, 224]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_117, vertices_661, vertices_805, vertices_361, vertices_593, vertices_902, vertices_234, vertices_330, vertices_394, vertices_722, vertices_316, vertices_412, vertices_184, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_517, vertices_81, vertices_529, vertices_97, vertices_289, vertices_321, vertices_577, vertices_769, vertices_74, vertices_138, vertices_266, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_284, vertices_52, vertices_148, vertices_292, vertices_388, vertices_644, vertices_772, vertices_56, vertices_152, vertices_104, vertices_168, vertices_296, vertices_328, vertices_392, vertices_112, vertices_176, vertices_208, vertices_592, vertices_656, vertices_224] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_117), (false, vertices_661), (false, vertices_805), (false, vertices_361), (false, vertices_593), (true, vertices_74), (true, vertices_138), (true, vertices_266), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_284), (true, vertices_388), (true, vertices_56), (true, vertices_152), (true, vertices_168), (true, vertices_392), (true, vertices_176), (true, vertices_208), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 20 17 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_117) then 21 else
  if p.val = (false, vertices_661) then 22 else
  if p.val = (false, vertices_805) then 23 else
  if p.val = (false, vertices_361) then 18 else
  if p.val = (false, vertices_593) then 0 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_284) then 19 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_224) then 14 else
  0
cert_priority
cert_nodeAtPriority_43 593 1 74 2 138 266 194 386 642 388 56 152 168 392 176 208 224 835 361 284 117 661 805
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 5 6 234 74 2
cert_row_2 1 1 2 3 7 284
cert_row_4 2 0 1 6 7 8 902 386 1
cert_row_4 3 0 3 5 6 8 722 194 1
cert_rows
cert_pivot_2 4 2 1 0
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 2 0 1 6 7 386 902 1
cert_coverFacet 1 234
cert_cover_5 1 0 0 2 4 5 74 234 2
cert_coverFacet 2 330
cert_cover_2 2 2 0 5 7 74 330 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 722
cert_cover_5 4 3 0 3 5 6 194 722 1
cert_coverFacet 5 316
cert_cover_5 5 1 1 2 3 4 284 316 3
cert_coverFacet 6 412
cert_cover_5 6 1 1 2 3 6 284 412 3
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coverFacet 8 240
cert_cover_2 8 4 3 5 6 112 240 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0450

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m15e10q1_0451.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0451

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [555, 779, 837, 185, 345, 625, 422, 710, 774, 298, 690, 460, 216, 424, 720, 523, 25, 41, 265, 49, 81, 545, 321, 577, 769, 134, 262, 518, 42, 266, 162, 290, 546, 642, 770, 196, 324, 580, 388, 772, 88, 152, 168, 296, 200, 328, 392, 176, 560, 208, 592, 656, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_555, vertices_779, vertices_837, vertices_185, vertices_345, vertices_625, vertices_422, vertices_710, vertices_774, vertices_298, vertices_690, vertices_460, vertices_216, vertices_424, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_523, vertices_25, vertices_41, vertices_265, vertices_49, vertices_81, vertices_545, vertices_321, vertices_577, vertices_769, vertices_134, vertices_262, vertices_518, vertices_42, vertices_266, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_196, vertices_324, vertices_580, vertices_388, vertices_772, vertices_88, vertices_152, vertices_168, vertices_296, vertices_200, vertices_328, vertices_392, vertices_176, vertices_560, vertices_208, vertices_592, vertices_656, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_555), (false, vertices_779), (false, vertices_837), (false, vertices_185), (false, vertices_345), (false, vertices_625), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_162), (true, vertices_290), (true, vertices_642), (true, vertices_196), (true, vertices_388), (true, vertices_296), (true, vertices_200), (true, vertices_392), (true, vertices_208), (true, vertices_656), (true, vertices_416), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_555) then 16 else
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_185) then 21 else
  if p.val = (false, vertices_345) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_416) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
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
cert_row_4 0 0 3 4 6 8 690 162 1
cert_row_4 1 0 1 4 6 7 422 134 2
cert_row_4 2 0 1 5 6 8 710 134 2
cert_row_4 3 1 2 5 6 7 460 196 1
cert_rows
cert_pivot_2 3 4 0 1
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 1 0 1 4 6 134 422 2
cert_coverFacet 1 710
cert_cover_5 1 2 0 1 5 6 134 710 2
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 298
cert_cover_2 3 2 0 4 7 42 298 3
cert_coverFacet 4 690
cert_cover_5 4 0 0 3 4 6 162 690 1
cert_coverFacet 5 460
cert_cover_5 5 3 1 2 5 6 196 460 1
cert_coverFacet 6 216
cert_cover_2 6 3 2 5 6 88 216 3
cert_coverFacet 7 424
cert_cover_2 7 4 2 6 7 168 424 3
cert_coverFacet 8 720
cert_cover_2 8 5 3 6 8 208 720 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0451

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m15e10q1_0453.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0453

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 589, 565, 229, 841, 369, 654, 154, 282, 778, 690, 460, 676, 440, 480, 37, 69, 517, 585, 49, 273, 529, 97, 321, 769, 26, 138, 266, 522, 146, 274, 530, 642, 770, 76, 140, 524, 164, 548, 196, 644, 152, 280, 328, 392, 776, 176, 304, 560, 224, 352, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_589, vertices_565, vertices_229, vertices_841, vertices_369, vertices_654, vertices_154, vertices_282, vertices_778, vertices_690, vertices_460, vertices_676, vertices_440, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_517, vertices_585, vertices_49, vertices_273, vertices_529, vertices_97, vertices_321, vertices_769, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_642, vertices_770, vertices_76, vertices_140, vertices_524, vertices_164, vertices_548, vertices_196, vertices_644, vertices_152, vertices_280, vertices_328, vertices_392, vertices_776, vertices_176, vertices_304, vertices_560, vertices_224, vertices_352, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_589), (false, vertices_565), (false, vertices_229), (false, vertices_841), (false, vertices_369), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_642), (true, vertices_140), (true, vertices_644), (true, vertices_152), (true, vertices_280), (true, vertices_392), (true, vertices_176), (true, vertices_416), (true, vertices_672), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 16 else
  if p.val = (false, vertices_589) then 21 else
  if p.val = (false, vertices_565) then 18 else
  if p.val = (false, vertices_229) then 19 else
  if p.val = (false, vertices_841) then 22 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_392) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_416) then 12 else
  if p.val = (true, vertices_672) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
cert_nodeAtPriority_52 26 1 138 2 266 522 146 642 140 644 152 280 392 176 416 672 448 787 565 229 589 841 369
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 5 6 7 460 76 3
cert_row_4 1 0 1 2 6 8 654 138 1
cert_row_4 2 0 3 4 6 8 690 146 2
cert_row_4 3 2 3 4 6 7 440 152 2
cert_rows
cert_pivot_2 5 1 0 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 1 0 1 2 6 138 654 1
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 690
cert_cover_5 4 2 0 3 4 6 146 690 2
cert_coverFacet 5 460
cert_cover_5 5 0 1 2 5 6 76 460 3
cert_coverFacet 6 676
cert_cover_2 6 4 1 6 8 164 676 3
cert_coverFacet 7 440
cert_cover_5 7 3 2 3 4 6 152 440 2
cert_coverFacet 8 480
cert_cover_2 8 5 4 6 7 224 480 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0453

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m15e10q1_0455.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0455

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 805, 345, 233, 297, 625, 406, 678, 774, 602, 154, 714, 428, 408, 736, 41, 73, 265, 81, 273, 529, 97, 289, 545, 769, 134, 262, 518, 26, 586, 138, 146, 274, 530, 642, 770, 164, 292, 548, 388, 772, 88, 152, 280, 168, 296, 200, 392, 592, 400, 224, 608, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_805, vertices_345, vertices_233, vertices_297, vertices_625, vertices_406, vertices_678, vertices_774, vertices_602, vertices_154, vertices_714, vertices_428, vertices_408, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_265, vertices_81, vertices_273, vertices_529, vertices_97, vertices_289, vertices_545, vertices_769, vertices_134, vertices_262, vertices_518, vertices_26, vertices_586, vertices_138, vertices_146, vertices_274, vertices_530, vertices_642, vertices_770, vertices_164, vertices_292, vertices_548, vertices_388, vertices_772, vertices_88, vertices_152, vertices_280, vertices_168, vertices_296, vertices_200, vertices_392, vertices_592, vertices_400, vertices_224, vertices_608, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_805), (false, vertices_345), (false, vertices_233), (false, vertices_297), (false, vertices_625), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_586), (true, vertices_138), (true, vertices_146), (true, vertices_642), (true, vertices_164), (true, vertices_388), (true, vertices_152), (true, vertices_392), (true, vertices_400), (true, vertices_672), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 16 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_345) then 21 else
  if p.val = (false, vertices_233) then 22 else
  if p.val = (false, vertices_297) then 0 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_586) then 17 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_672) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 297 134 262 518 26 138 146 642 164 388 152 392 400 672 704 787 586 805 345 233 625
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 8 586
cert_row_4 1 0 1 3 6 7 406 134 2
cert_row_4 2 0 1 4 6 8 678 134 2
cert_row_4 3 1 2 4 6 7 428 164 1
cert_rows
cert_pivot_2 5 3 0 1
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 1 0 1 3 6 134 406 2
cert_coverFacet 1 678
cert_cover_5 1 2 0 1 4 6 134 678 2
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 602
cert_cover_5 3 0 0 2 3 5 26 602 3
cert_coverFacet 4 154
cert_cover_2 4 2 0 3 6 26 154 3
cert_coverFacet 5 714
cert_cover_5 5 0 0 2 5 6 586 714 3
cert_coverFacet 6 428
cert_cover_5 6 3 1 2 4 6 164 428 1
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 736
cert_cover_2 8 5 4 6 8 224 736 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0455

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m15e10q1_0456.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0456

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 613, 421, 713, 465, 353, 398, 310, 566, 602, 282, 650, 216, 408, 880, 37, 133, 517, 97, 289, 193, 321, 577, 385, 641, 54, 134, 262, 518, 26, 138, 266, 522, 274, 530, 642, 292, 548, 388, 88, 152, 280, 200, 584, 392, 648, 304, 560, 208, 336, 592, 400, 352, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_613, vertices_421, vertices_713, vertices_465, vertices_353, vertices_398, vertices_310, vertices_566, vertices_602, vertices_282, vertices_650, vertices_216, vertices_408, vertices_880] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_517, vertices_97, vertices_289, vertices_193, vertices_321, vertices_577, vertices_385, vertices_641, vertices_54, vertices_134, vertices_262, vertices_518, vertices_26, vertices_138, vertices_266, vertices_522, vertices_274, vertices_530, vertices_642, vertices_292, vertices_548, vertices_388, vertices_88, vertices_152, vertices_280, vertices_200, vertices_584, vertices_392, vertices_648, vertices_304, vertices_560, vertices_208, vertices_336, vertices_592, vertices_400, vertices_352, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_613), (false, vertices_421), (false, vertices_713), (false, vertices_465), (false, vertices_353), (true, vertices_54), (true, vertices_262), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_530), (true, vertices_88), (true, vertices_152), (true, vertices_280), (true, vertices_392), (true, vertices_304), (true, vertices_560), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 16 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_421) then 20 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (false, vertices_353) then 0 else
  if p.val = (true, vertices_54) then 17 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_592) then 14 else
  0
cert_priority
cert_nodeAtPriority_22 353 262 26 138 266 522 274 530 88 152 280 392 304 560 592 647 54 613 421 713 465
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 134 2
cert_row_2 1 0 1 3 4 54
cert_row_4 2 0 2 3 5 8 602 26 3
cert_row_4 3 3 4 5 7 8 880 304 2
cert_rows
cert_pivot_2 6 1 0 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 134 398 2
cert_coverFacet 1 310
cert_cover_5 1 1 0 1 3 7 54 310 3
cert_coverFacet 2 566
cert_cover_5 2 1 0 1 3 8 54 566 3
cert_coverFacet 3 602
cert_cover_5 3 2 0 2 3 5 26 602 3
cert_coverFacet 4 282
cert_cover_2 4 2 0 3 7 26 282 3
cert_coverFacet 5 650
cert_cover_2 5 2 0 6 8 138 650 3
cert_coverFacet 6 216
cert_cover_2 6 3 2 5 6 88 216 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 880
cert_cover_5 8 3 3 4 5 7 304 880 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0456

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m15e10q1_0457.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0457

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [419, 789, 601, 369, 737, 897, 94, 174, 342, 390, 618, 354, 540, 908, 680, 81, 273, 529, 97, 161, 289, 577, 385, 641, 769, 14, 86, 134, 262, 42, 74, 98, 162, 290, 322, 386, 28, 140, 524, 276, 532, 388, 772, 88, 536, 168, 552, 584, 648, 336, 352, 608, 672, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_419, vertices_789, vertices_601, vertices_369, vertices_737, vertices_897, vertices_94, vertices_174, vertices_342, vertices_390, vertices_618, vertices_354, vertices_540, vertices_908, vertices_680] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_273, vertices_529, vertices_97, vertices_161, vertices_289, vertices_577, vertices_385, vertices_641, vertices_769, vertices_14, vertices_86, vertices_134, vertices_262, vertices_42, vertices_74, vertices_98, vertices_162, vertices_290, vertices_322, vertices_386, vertices_28, vertices_140, vertices_524, vertices_276, vertices_532, vertices_388, vertices_772, vertices_88, vertices_536, vertices_168, vertices_552, vertices_584, vertices_648, vertices_336, vertices_352, vertices_608, vertices_672, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_419), (false, vertices_789), (false, vertices_601), (false, vertices_369), (false, vertices_737), (false, vertices_897), (true, vertices_14), (true, vertices_86), (true, vertices_134), (true, vertices_262), (true, vertices_42), (true, vertices_74), (true, vertices_98), (true, vertices_322), (true, vertices_28), (true, vertices_140), (true, vertices_524), (true, vertices_388), (true, vertices_168), (true, vertices_552), (true, vertices_648)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_419) then 16 else
  if p.val = (false, vertices_789) then 19 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_369) then 23 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (false, vertices_897) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_86) then 17 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_74) then 5 else
  if p.val = (true, vertices_98) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_140) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_552) then 13 else
  if p.val = (true, vertices_648) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 897 14 134 262 42 74 98 322 28 140 524 388 168 552 648 419 86 789 601 369 737
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 5 86
cert_row_4 1 0 2 4 5 8 618 42 3
cert_row_4 2 0 1 2 4 6 174 14 3
cert_row_4 3 1 2 6 7 8 908 140 3
cert_rows
cert_pivot_2 3 5 0 1
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 3 14 94 3
cert_coverFacet 1 174
cert_cover_5 1 2 0 1 2 4 14 174 3
cert_coverFacet 2 342
cert_cover_5 2 0 0 1 3 7 86 342 3
cert_coverFacet 3 390
cert_cover_2 3 1 0 6 7 134 390 3
cert_coverFacet 4 618
cert_cover_5 4 1 0 2 4 5 42 618 3
cert_coverFacet 5 354
cert_cover_2 5 4 0 5 7 98 354 3
cert_coverFacet 6 540
cert_cover_2 6 2 1 3 8 28 540 3
cert_coverFacet 7 908
cert_cover_5 7 3 1 2 6 7 140 908 3
cert_coverFacet 8 680
cert_cover_2 8 4 2 6 8 168 680 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0457

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e10q1_0458.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0458

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [91, 779, 211, 675, 805, 313, 177, 710, 586, 844, 692, 308, 404, 452, 472, 11, 83, 131, 515, 25, 265, 49, 145, 161, 289, 545, 769, 74, 522, 194, 578, 642, 52, 148, 276, 292, 548, 196, 324, 580, 388, 644, 772, 88, 280, 328, 584, 776, 176, 304, 208, 400, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_91, vertices_779, vertices_211, vertices_675, vertices_805, vertices_313, vertices_177, vertices_710, vertices_586, vertices_844, vertices_692, vertices_308, vertices_404, vertices_452, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_83, vertices_131, vertices_515, vertices_25, vertices_265, vertices_49, vertices_145, vertices_161, vertices_289, vertices_545, vertices_769, vertices_74, vertices_522, vertices_194, vertices_578, vertices_642, vertices_52, vertices_148, vertices_276, vertices_292, vertices_548, vertices_196, vertices_324, vertices_580, vertices_388, vertices_644, vertices_772, vertices_88, vertices_280, vertices_328, vertices_584, vertices_776, vertices_176, vertices_304, vertices_208, vertices_400, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_91), (false, vertices_779), (false, vertices_211), (false, vertices_675), (false, vertices_805), (false, vertices_313), (false, vertices_177), (true, vertices_578), (true, vertices_52), (true, vertices_148), (true, vertices_276), (true, vertices_196), (true, vertices_324), (true, vertices_580), (true, vertices_388), (true, vertices_644), (true, vertices_328), (true, vertices_584), (true, vertices_400), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 14 16 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_91) then 20 else
  if p.val = (false, vertices_779) then 17 else
  if p.val = (false, vertices_211) then 21 else
  if p.val = (false, vertices_675) then 22 else
  if p.val = (false, vertices_805) then 15 else
  if p.val = (false, vertices_313) then 18 else
  if p.val = (false, vertices_177) then 0 else
  if p.val = (true, vertices_578) then 1 else
  if p.val = (true, vertices_52) then 2 else
  if p.val = (true, vertices_148) then 3 else
  if p.val = (true, vertices_276) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_324) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_448) then 13 else
  0
cert_priority
cert_nodeAtPriority_48 1 177 0 578 2 52 148 276 196 324 580 388 644 328 584 400 448 805 779 313 91 211 675
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 5 6 8 710 194 1
cert_row_4 1 1 3 4 6 8 692 52 3
cert_row_4 2 1 2 5 7 8 844 324 1
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 0 4 1 2
cert_heightProof 4
cert_coverFacet 0 710
cert_cover_5 0 0 0 1 5 6 194 710 1
cert_coverFacet 1 586
cert_cover_2 1 2 0 5 8 74 586 3
cert_coverFacet 2 844
cert_cover_5 2 2 1 2 5 7 324 844 1
cert_coverFacet 3 692
cert_cover_5 3 1 1 3 4 6 52 692 3
cert_coverFacet 4 308
cert_cover_2 4 3 1 4 7 52 308 3
cert_coverFacet 5 404
cert_cover_2 5 3 1 6 7 148 404 3
cert_coverFacet 6 452
cert_cover_2 6 5 1 6 7 196 452 3
cert_coverFacet 7 472
cert_cover_5 7 3 2 3 5 6 88 472 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0458

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e10q1_0459.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0459

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 173, 405, 533, 613, 369, 417, 654, 662, 410, 618, 330, 338, 556, 488, 21, 37, 133, 517, 81, 273, 529, 97, 161, 289, 577, 385, 646, 74, 138, 266, 522, 82, 146, 274, 530, 322, 578, 44, 140, 524, 148, 532, 548, 104, 168, 552, 328, 392, 336, 400, 352, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_173, vertices_405, vertices_533, vertices_613, vertices_369, vertices_417, vertices_654, vertices_662, vertices_410, vertices_618, vertices_330, vertices_338, vertices_556, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_133, vertices_517, vertices_81, vertices_273, vertices_529, vertices_97, vertices_161, vertices_289, vertices_577, vertices_385, vertices_646, vertices_74, vertices_138, vertices_266, vertices_522, vertices_82, vertices_146, vertices_274, vertices_530, vertices_322, vertices_578, vertices_44, vertices_140, vertices_524, vertices_148, vertices_532, vertices_548, vertices_104, vertices_168, vertices_552, vertices_328, vertices_392, vertices_336, vertices_400, vertices_352, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_173), (false, vertices_405), (false, vertices_533), (false, vertices_613), (false, vertices_369), (false, vertices_417), (true, vertices_646), (true, vertices_74), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_274), (true, vertices_322), (true, vertices_524), (true, vertices_104), (true, vertices_552), (true, vertices_328), (true, vertices_392)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 15 else
  if p.val = (false, vertices_173) then 18 else
  if p.val = (false, vertices_405) then 19 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_613) then 20 else
  if p.val = (false, vertices_369) then 23 else
  if p.val = (false, vertices_417) then 1 else
  if p.val = (true, vertices_646) then 16 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_274) then 7 else
  if p.val = (true, vertices_322) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_328) then 12 else
  if p.val = (true, vertices_392) then 13 else
  0
cert_priority
cert_nodeAtPriority_15 0 533 1 417 74 138 266 522 146 274 322 524 104 552 328 392 595 646 173 405 613 369
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 8 646
cert_row_4 1 0 2 3 6 7 410 138 2
cert_row_4 2 0 2 4 5 8 618 74 2
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 1 3 0 2
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 0 0 1 2 6 646 654 2
cert_coverFacet 1 662
cert_cover_5 1 0 0 1 3 6 646 662 2
cert_coverFacet 2 410
cert_cover_5 2 1 0 2 3 6 138 410 2
cert_coverFacet 3 618
cert_cover_5 3 2 0 2 4 5 74 618 2
cert_coverFacet 4 330
cert_cover_2 4 2 0 5 7 74 330 3
cert_coverFacet 5 338
cert_cover_2 5 3 0 5 7 82 338 3
cert_coverFacet 6 556
cert_cover_2 6 2 1 4 8 44 556 3
cert_coverFacet 7 488
cert_cover_5 7 3 2 4 5 6 104 488 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0459

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e10q1_0460.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0460

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 285, 557, 229, 389, 57, 369, 398, 654, 778, 850, 738, 676, 632, 792, 13, 37, 133, 261, 25, 41, 49, 273, 97, 193, 321, 385, 142, 266, 522, 194, 322, 578, 386, 642, 770, 268, 524, 164, 548, 388, 644, 56, 280, 536, 552, 776, 112, 336, 592, 784, 224, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_285, vertices_557, vertices_229, vertices_389, vertices_57, vertices_369, vertices_398, vertices_654, vertices_778, vertices_850, vertices_738, vertices_676, vertices_632, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_133, vertices_261, vertices_25, vertices_41, vertices_49, vertices_273, vertices_97, vertices_193, vertices_321, vertices_385, vertices_142, vertices_266, vertices_522, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_268, vertices_524, vertices_164, vertices_548, vertices_388, vertices_644, vertices_56, vertices_280, vertices_536, vertices_552, vertices_776, vertices_112, vertices_336, vertices_592, vertices_784, vertices_224, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_285), (false, vertices_557), (false, vertices_229), (false, vertices_389), (false, vertices_57), (false, vertices_369), (true, vertices_142), (true, vertices_266), (true, vertices_522), (true, vertices_578), (true, vertices_642), (true, vertices_770), (true, vertices_644), (true, vertices_536), (true, vertices_776), (true, vertices_592), (true, vertices_784), (true, vertices_608), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 15 else
  if p.val = (false, vertices_285) then 18 else
  if p.val = (false, vertices_557) then 19 else
  if p.val = (false, vertices_229) then 20 else
  if p.val = (false, vertices_389) then 0 else
  if p.val = (false, vertices_57) then 1 else
  if p.val = (false, vertices_369) then 23 else
  if p.val = (true, vertices_142) then 16 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_776) then 9 else
  if p.val = (true, vertices_592) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
cert_nodeAtPriority_15 0 389 1 57 266 522 578 642 770 644 536 776 592 784 608 672 451 142 285 557 229 369
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 6 142
cert_row_4 1 0 3 5 7 8 850 322 1
cert_row_4 2 0 4 5 6 8 738 194 1
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 1 7 0 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 7 142 398 3
cert_coverFacet 1 654
cert_cover_5 1 0 0 1 2 8 142 654 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 850
cert_cover_5 3 1 0 3 5 7 322 850 1
cert_coverFacet 4 738
cert_cover_5 4 2 0 4 5 6 194 738 1
cert_coverFacet 5 676
cert_cover_2 5 4 1 6 8 164 676 3
cert_coverFacet 6 632
cert_cover_5 6 3 2 3 4 5 56 632 3
cert_coverFacet 7 792
cert_cover_2 7 3 2 7 8 280 792 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0460

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_3033 : Certifies 3033 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0427.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3034 : Certifies 3034 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0428.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3035 : Certifies 3035 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0429.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3036 : Certifies 3036 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0430.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3037 : Certifies 3037 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0432.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3038 : Certifies 3038 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0433.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3039 : Certifies 3039 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0434.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3040 : Certifies 3040 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0435.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3041 : Certifies 3041 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0436.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3042 : Certifies 3042 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0437.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3043 : Certifies 3043 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0438.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3044 : Certifies 3044 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0440.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3045 : Certifies 3045 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0441.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3046 : Certifies 3046 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0442.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3047 : Certifies 3047 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0443.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3048 : Certifies 3048 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0444.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3049 : Certifies 3049 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0445.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3050 : Certifies 3050 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0446.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3051 : Certifies 3051 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0447.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3052 : Certifies 3052 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0448.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3053 : Certifies 3053 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0449.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3054 : Certifies 3054 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0450.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3055 : Certifies 3055 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0451.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3056 : Certifies 3056 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0453.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3057 : Certifies 3057 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0455.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3058 : Certifies 3058 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0456.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3059 : Certifies 3059 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0457.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3060 : Certifies 3060 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0458.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3061 : Certifies 3061 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0459.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3062 : Certifies 3062 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0460.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B100 (j : Fin 30) :
    Certifies (3033 + j.val) := by
  fin_cases j
  · exact projection_3033
  · exact projection_3034
  · exact projection_3035
  · exact projection_3036
  · exact projection_3037
  · exact projection_3038
  · exact projection_3039
  · exact projection_3040
  · exact projection_3041
  · exact projection_3042
  · exact projection_3043
  · exact projection_3044
  · exact projection_3045
  · exact projection_3046
  · exact projection_3047
  · exact projection_3048
  · exact projection_3049
  · exact projection_3050
  · exact projection_3051
  · exact projection_3052
  · exact projection_3053
  · exact projection_3054
  · exact projection_3055
  · exact projection_3056
  · exact projection_3057
  · exact projection_3058
  · exact projection_3059
  · exact projection_3060
  · exact projection_3061
  · exact projection_3062

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
