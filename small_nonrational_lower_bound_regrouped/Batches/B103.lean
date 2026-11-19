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
/- Source: ProjectionCertificates/R_m15e10q1_0524.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0524

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 405, 229, 805, 217, 361, 902, 90, 842, 626, 690, 402, 676, 240, 864, 37, 133, 261, 25, 73, 265, 145, 273, 97, 289, 193, 26, 74, 266, 562, 82, 146, 274, 578, 386, 642, 770, 164, 548, 388, 644, 772, 88, 328, 112, 176, 208, 400, 224, 352, 608, 672, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_405, vertices_229, vertices_805, vertices_217, vertices_361, vertices_902, vertices_90, vertices_842, vertices_626, vertices_690, vertices_402, vertices_676, vertices_240, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_25, vertices_73, vertices_265, vertices_145, vertices_273, vertices_97, vertices_289, vertices_193, vertices_26, vertices_74, vertices_266, vertices_562, vertices_82, vertices_146, vertices_274, vertices_578, vertices_386, vertices_642, vertices_770, vertices_164, vertices_548, vertices_388, vertices_644, vertices_772, vertices_88, vertices_328, vertices_112, vertices_176, vertices_208, vertices_400, vertices_224, vertices_352, vertices_608, vertices_672, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_405), (false, vertices_229), (false, vertices_805), (false, vertices_217), (false, vertices_361), (true, vertices_74), (true, vertices_562), (true, vertices_82), (true, vertices_146), (true, vertices_578), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_644), (true, vertices_112), (true, vertices_176), (true, vertices_608), (true, vertices_672), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 14 else
  if p.val = (false, vertices_405) then 17 else
  if p.val = (false, vertices_229) then 18 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_217) then 21 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_562) then 15 else
  if p.val = (true, vertices_82) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_176) then 9 else
  if p.val = (true, vertices_608) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_832) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_562), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
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
cert_row_2 0 0 3 4 8 562
cert_row_4 1 0 1 6 7 8 902 386 1
cert_row_4 2 0 2 5 7 8 842 74 3
cert_rows_3
cert_pivot_3 1 3 0
cert_heightProof 3
cert_coverFacet 0 902
cert_cover_5 0 1 0 1 6 7 386 902 1
cert_coverFacet 1 90
cert_cover_2 1 2 0 3 5 26 90 3
cert_coverFacet 2 842
cert_cover_5 2 2 0 2 5 7 74 842 3
cert_coverFacet 3 626
cert_cover_5 3 0 0 3 4 5 562 626 3
cert_coverFacet 4 690
cert_cover_5 4 0 0 3 4 6 562 690 3
cert_coverFacet 5 402
cert_cover_2 5 3 0 6 7 146 402 3
cert_coverFacet 6 676
cert_cover_2 6 4 1 6 8 164 676 3
cert_coverFacet 7 240
cert_cover_2 7 4 3 5 6 112 240 3
cert_coverFacet 8 864
cert_cover_2 8 5 4 7 8 352 864 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 3 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0524

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e10q1_0525.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0525

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 333, 421, 709, 689, 833, 286, 406, 570, 842, 178, 418, 92, 212, 728, 69, 133, 261, 161, 289, 545, 321, 577, 641, 769, 278, 26, 266, 522, 50, 146, 162, 290, 546, 386, 770, 28, 76, 268, 84, 148, 196, 388, 88, 536, 328, 584, 176, 560, 208, 656, 416, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_333, vertices_421, vertices_709, vertices_689, vertices_833, vertices_286, vertices_406, vertices_570, vertices_842, vertices_178, vertices_418, vertices_92, vertices_212, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_161, vertices_289, vertices_545, vertices_321, vertices_577, vertices_641, vertices_769, vertices_278, vertices_26, vertices_266, vertices_522, vertices_50, vertices_146, vertices_162, vertices_290, vertices_546, vertices_386, vertices_770, vertices_28, vertices_76, vertices_268, vertices_84, vertices_148, vertices_196, vertices_388, vertices_88, vertices_536, vertices_328, vertices_584, vertices_176, vertices_560, vertices_208, vertices_656, vertices_416, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_333), (false, vertices_421), (false, vertices_709), (false, vertices_689), (false, vertices_833), (true, vertices_278), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_146), (true, vertices_162), (true, vertices_386), (true, vertices_28), (true, vertices_84), (true, vertices_148), (true, vertices_88), (true, vertices_536), (true, vertices_584), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_333) then 19 else
  if p.val = (false, vertices_421) then 20 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_689) then 24 else
  if p.val = (false, vertices_833) then 0 else
  if p.val = (true, vertices_278) then 17 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_88) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_584) then 13 else
  if p.val = (true, vertices_208) then 14 else
  0
cert_priority
cert_nodeAtPriority_19 0 833 1 26 266 522 50 146 162 386 28 84 148 88 536 584 208 803 278 333 421 709 689
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 7 278
cert_row_4 1 0 2 3 4 8 570 26 3
cert_row_4 2 0 2 5 7 8 842 266 2
cert_row_4 3 2 3 5 6 8 728 88 3
cert_rows
cert_pivot_2 1 4 0 2
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 3 278 286 2
cert_coverFacet 1 406
cert_cover_5 1 0 0 1 3 6 278 406 3
cert_coverFacet 2 570
cert_cover_5 2 1 0 2 3 4 26 570 3
cert_coverFacet 3 842
cert_cover_5 3 2 0 2 5 7 266 842 2
cert_coverFacet 4 178
cert_cover_2 4 3 0 4 6 50 178 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 92
cert_cover_2 6 2 1 3 5 28 92 3
cert_coverFacet 7 212
cert_cover_2 7 3 1 5 6 84 212 3
cert_coverFacet 8 728
cert_cover_5 8 3 2 3 5 6 88 728 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0525

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e10q1_0526.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0526

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 661, 793, 361, 681, 417, 334, 782, 214, 534, 786, 482, 620, 708, 736, 41, 265, 521, 145, 273, 529, 161, 289, 385, 641, 270, 22, 70, 518, 146, 274, 530, 194, 322, 386, 770, 76, 524, 148, 532, 196, 580, 644, 104, 552, 328, 776, 784, 224, 352, 608, 416, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_661, vertices_793, vertices_361, vertices_681, vertices_417, vertices_334, vertices_782, vertices_214, vertices_534, vertices_786, vertices_482, vertices_620, vertices_708, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_265, vertices_521, vertices_145, vertices_273, vertices_529, vertices_161, vertices_289, vertices_385, vertices_641, vertices_270, vertices_22, vertices_70, vertices_518, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_386, vertices_770, vertices_76, vertices_524, vertices_148, vertices_532, vertices_196, vertices_580, vertices_644, vertices_104, vertices_552, vertices_328, vertices_776, vertices_784, vertices_224, vertices_352, vertices_608, vertices_416, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_661), (false, vertices_793), (false, vertices_361), (false, vertices_681), (false, vertices_417), (true, vertices_270), (true, vertices_22), (true, vertices_70), (true, vertices_518), (true, vertices_530), (true, vertices_194), (true, vertices_322), (true, vertices_770), (true, vertices_76), (true, vertices_524), (true, vertices_196), (true, vertices_580), (true, vertices_224), (true, vertices_608), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 16 else
  if p.val = (false, vertices_661) then 19 else
  if p.val = (false, vertices_793) then 21 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_681) then 23 else
  if p.val = (false, vertices_417) then 0 else
  if p.val = (true, vertices_270) then 17 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_196) then 10 else
  if p.val = (true, vertices_580) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_608) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_417), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_270), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 6 214 22 3
cert_row_4 1 0 4 5 6 7 482 194 1
cert_row_2 2 0 1 2 7 270
cert_row_4 3 1 2 4 5 8 620 76 2
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 2 0 1 2 5 270 334 3
cert_coverFacet 1 782
cert_cover_5 1 2 0 1 2 8 270 782 3
cert_coverFacet 2 214
cert_cover_5 2 0 0 1 3 5 22 214 3
cert_coverFacet 3 534
cert_cover_2 3 1 0 3 8 22 534 3
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 482
cert_cover_5 5 1 0 4 5 6 194 482 1
cert_coverFacet 6 620
cert_cover_5 6 3 1 2 4 5 76 620 2
cert_coverFacet 7 708
cert_cover_2 7 5 1 6 8 196 708 3
cert_coverFacet 8 736
cert_cover_2 8 5 4 6 8 224 736 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0526

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e10q1_0527.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0527

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 45, 333, 165, 709, 793, 681, 454, 570, 178, 402, 786, 738, 316, 436, 13, 37, 69, 133, 41, 265, 521, 161, 321, 577, 641, 769, 50, 146, 274, 530, 162, 546, 194, 322, 578, 386, 770, 44, 268, 308, 164, 196, 324, 388, 56, 280, 536, 552, 176, 400, 784, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_45, vertices_333, vertices_165, vertices_709, vertices_793, vertices_681, vertices_454, vertices_570, vertices_178, vertices_402, vertices_786, vertices_738, vertices_316, vertices_436] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_37, vertices_69, vertices_133, vertices_41, vertices_265, vertices_521, vertices_161, vertices_321, vertices_577, vertices_641, vertices_769, vertices_50, vertices_146, vertices_274, vertices_530, vertices_162, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_44, vertices_268, vertices_308, vertices_164, vertices_196, vertices_324, vertices_388, vertices_56, vertices_280, vertices_536, vertices_552, vertices_176, vertices_400, vertices_784, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_45), (false, vertices_333), (false, vertices_165), (false, vertices_709), (false, vertices_793), (false, vertices_681), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_546), (true, vertices_194), (true, vertices_386), (true, vertices_308), (true, vertices_388), (true, vertices_56), (true, vertices_176), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 15 else
  if p.val = (false, vertices_45) then 0 else
  if p.val = (false, vertices_333) then 17 else
  if p.val = (false, vertices_165) then 1 else
  if p.val = (false, vertices_709) then 18 else
  if p.val = (false, vertices_793) then 21 else
  if p.val = (false, vertices_681) then 22 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_194) then 8 else
  if p.val = (true, vertices_386) then 9 else
  if p.val = (true, vertices_308) then 19 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_400) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_45), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_165), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_308), by decide +kernel⟩
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
cert_row_4 0 0 2 3 4 8 570 50 1
cert_row_2 1 1 3 4 7 308
cert_row_4 2 0 1 5 6 7 454 194 1
cert_row_4 3 0 4 5 6 8 738 162 2
cert_rows
cert_pivot_2 2 3 1 0
cert_heightProof 4
cert_coverFacet 0 454
cert_cover_5 0 2 0 1 5 6 194 454 1
cert_coverFacet 1 570
cert_cover_5 1 0 0 2 3 4 50 570 1
cert_coverFacet 2 178
cert_cover_2 2 3 0 4 6 50 178 3
cert_coverFacet 3 402
cert_cover_2 3 3 0 6 7 146 402 3
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 738
cert_cover_5 5 3 0 4 5 6 162 738 2
cert_coverFacet 6 316
cert_cover_5 6 1 1 2 3 4 44 316 2
cert_coverFacet 7 436
cert_cover_5 7 1 1 3 4 6 308 436 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0527

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e10q1_0528.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0528

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 557, 361, 713, 433, 673, 182, 534, 710, 842, 402, 786, 316, 796, 676, 41, 73, 521, 161, 289, 545, 193, 321, 385, 641, 22, 134, 518, 146, 274, 530, 194, 322, 578, 386, 770, 284, 44, 524, 52, 532, 164, 548, 644, 296, 328, 584, 776, 176, 304, 400, 784, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_557, vertices_361, vertices_713, vertices_433, vertices_673, vertices_182, vertices_534, vertices_710, vertices_842, vertices_402, vertices_786, vertices_316, vertices_796, vertices_676] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_521, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_385, vertices_641, vertices_22, vertices_134, vertices_518, vertices_146, vertices_274, vertices_530, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_284, vertices_44, vertices_524, vertices_52, vertices_532, vertices_164, vertices_548, vertices_644, vertices_296, vertices_328, vertices_584, vertices_776, vertices_176, vertices_304, vertices_400, vertices_784, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_557), (false, vertices_361), (false, vertices_713), (false, vertices_433), (false, vertices_673), (true, vertices_22), (true, vertices_134), (true, vertices_518), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_578), (true, vertices_770), (true, vertices_284), (true, vertices_52), (true, vertices_532), (true, vertices_164), (true, vertices_644), (true, vertices_776), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 16 else
  if p.val = (false, vertices_557) then 18 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (false, vertices_673) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_284) then 19 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_532) then 10 else
  if p.val = (true, vertices_164) then 11 else
  if p.val = (true, vertices_644) then 12 else
  if p.val = (true, vertices_776) then 13 else
  if p.val = (true, vertices_784) then 14 else
  0
cert_priority
cert_nodeAtPriority_65 673 2 22 1 134 3 518 146 274 530 578 770 52 532 164 644 776 784 451 557 284 361 713 433
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 6 182 22 3
cert_row_2 1 1 2 3 7 284
cert_row_4 2 0 1 5 6 8 710 134 2
cert_row_4 3 0 2 5 7 8 842 322 1
cert_rows
cert_pivot_2 4 3 1 0
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 0 0 1 3 4 22 182 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 710
cert_cover_5 2 2 0 1 5 6 134 710 2
cert_coverFacet 3 842
cert_cover_5 3 3 0 2 5 7 322 842 1
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 786
cert_cover_2 5 3 0 7 8 274 786 3
cert_coverFacet 6 316
cert_cover_5 6 1 1 2 3 4 284 316 3
cert_coverFacet 7 796
cert_cover_5 7 1 1 2 3 8 284 796 3
cert_coverFacet 8 676
cert_cover_2 8 4 1 6 8 164 676 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0528

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e10q1_0529.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0529

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 333, 665, 617, 393, 481, 158, 310, 390, 626, 658, 418, 604, 396, 372, 73, 137, 265, 521, 97, 161, 545, 321, 385, 641, 22, 134, 262, 50, 146, 530, 162, 290, 546, 386, 642, 28, 76, 140, 268, 308, 84, 324, 388, 152, 536, 584, 392, 112, 592, 656, 352, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_333, vertices_665, vertices_617, vertices_393, vertices_481, vertices_158, vertices_310, vertices_390, vertices_626, vertices_658, vertices_418, vertices_604, vertices_396, vertices_372] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_265, vertices_521, vertices_97, vertices_161, vertices_545, vertices_321, vertices_385, vertices_641, vertices_22, vertices_134, vertices_262, vertices_50, vertices_146, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_28, vertices_76, vertices_140, vertices_268, vertices_308, vertices_84, vertices_324, vertices_388, vertices_152, vertices_536, vertices_584, vertices_392, vertices_112, vertices_592, vertices_656, vertices_352, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_333), (false, vertices_665), (false, vertices_617), (false, vertices_393), (false, vertices_481), (true, vertices_22), (true, vertices_134), (true, vertices_262), (true, vertices_50), (true, vertices_146), (true, vertices_530), (true, vertices_290), (true, vertices_386), (true, vertices_28), (true, vertices_140), (true, vertices_308), (true, vertices_84), (true, vertices_388), (true, vertices_112), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_333) then 18 else
  if p.val = (false, vertices_665) then 21 else
  if p.val = (false, vertices_617) then 22 else
  if p.val = (false, vertices_393) then 0 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_140) then 10 else
  if p.val = (true, vertices_308) then 19 else
  if p.val = (true, vertices_84) then 11 else
  if p.val = (true, vertices_388) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_592) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_393), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_308), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
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
cert_row_2 0 1 3 4 7 308
cert_row_4 1 0 1 2 3 6 158 22 2
cert_row_4 2 0 3 4 5 8 626 50 3
cert_row_4 3 1 2 3 5 8 604 28 3
cert_rows
cert_pivot_2 7 6 0 1
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 1 0 1 2 3 22 158 2
cert_coverFacet 1 310
cert_cover_5 1 0 0 1 3 4 22 310 3
cert_coverFacet 2 390
cert_cover_2 2 1 0 6 7 134 390 3
cert_coverFacet 3 626
cert_cover_5 3 2 0 3 4 5 50 626 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 604
cert_cover_5 6 3 1 2 3 5 28 604 3
cert_coverFacet 7 396
cert_cover_2 7 2 1 6 7 140 396 3
cert_coverFacet 8 372
cert_cover_5 8 0 1 3 4 5 308 372 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0529

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e10q1_0530.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0530

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 557, 789, 229, 389, 865, 398, 186, 282, 242, 850, 284, 540, 172, 632, 37, 133, 261, 517, 97, 545, 193, 321, 385, 769, 26, 138, 266, 178, 82, 274, 194, 322, 386, 28, 44, 140, 268, 524, 276, 532, 164, 388, 56, 280, 536, 168, 552, 112, 592, 784, 224, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_557, vertices_789, vertices_229, vertices_389, vertices_865, vertices_398, vertices_186, vertices_282, vertices_242, vertices_850, vertices_284, vertices_540, vertices_172, vertices_632] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_517, vertices_97, vertices_545, vertices_193, vertices_321, vertices_385, vertices_769, vertices_26, vertices_138, vertices_266, vertices_178, vertices_82, vertices_274, vertices_194, vertices_322, vertices_386, vertices_28, vertices_44, vertices_140, vertices_268, vertices_524, vertices_276, vertices_532, vertices_164, vertices_388, vertices_56, vertices_280, vertices_536, vertices_168, vertices_552, vertices_112, vertices_592, vertices_784, vertices_224, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_557), (false, vertices_789), (false, vertices_229), (false, vertices_389), (false, vertices_865), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_178), (true, vertices_82), (true, vertices_274), (true, vertices_28), (true, vertices_140), (true, vertices_268), (true, vertices_56), (true, vertices_280), (true, vertices_536), (true, vertices_168), (true, vertices_112), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 16 else
  if p.val = (false, vertices_557) then 19 else
  if p.val = (false, vertices_789) then 20 else
  if p.val = (false, vertices_229) then 21 else
  if p.val = (false, vertices_389) then 0 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_178) then 17 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_592) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_178), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 22 => Sum.inl 2
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
cert_row_4 0 0 1 2 6 7 398 138 1
cert_row_2 1 0 3 4 6 178
cert_row_4 2 0 3 5 7 8 850 82 3
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 138 398 1
cert_coverFacet 1 186
cert_cover_5 1 1 0 2 3 4 26 186 3
cert_coverFacet 2 282
cert_cover_2 2 2 0 3 7 26 282 3
cert_coverFacet 3 242
cert_cover_5 3 1 0 3 4 5 178 242 3
cert_coverFacet 4 850
cert_cover_5 4 2 0 3 5 7 82 850 3
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 540
cert_cover_2 6 2 1 3 8 28 540 3
cert_coverFacet 7 172
cert_cover_2 7 2 1 4 6 44 172 3
cert_coverFacet 8 632
cert_cover_5 8 3 2 3 4 5 56 632 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0530

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e10q1_0531.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0531

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 301, 57, 601, 689, 865, 206, 270, 390, 722, 930, 834, 60, 220, 436, 25, 41, 73, 265, 49, 529, 289, 545, 321, 577, 14, 134, 262, 74, 266, 194, 322, 578, 386, 642, 770, 28, 44, 204, 268, 52, 148, 292, 388, 56, 88, 176, 208, 592, 656, 416, 672, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_301, vertices_57, vertices_601, vertices_689, vertices_865, vertices_206, vertices_270, vertices_390, vertices_722, vertices_930, vertices_834, vertices_60, vertices_220, vertices_436] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_73, vertices_265, vertices_49, vertices_529, vertices_289, vertices_545, vertices_321, vertices_577, vertices_14, vertices_134, vertices_262, vertices_74, vertices_266, vertices_194, vertices_322, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_204, vertices_268, vertices_52, vertices_148, vertices_292, vertices_388, vertices_56, vertices_88, vertices_176, vertices_208, vertices_592, vertices_656, vertices_416, vertices_672, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_301), (false, vertices_57), (false, vertices_601), (false, vertices_689), (false, vertices_865), (true, vertices_14), (true, vertices_134), (true, vertices_262), (true, vertices_194), (true, vertices_578), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_28), (true, vertices_204), (true, vertices_52), (true, vertices_148), (true, vertices_388), (true, vertices_208), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 16 else
  if p.val = (false, vertices_301) then 18 else
  if p.val = (false, vertices_57) then 0 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_689) then 23 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_204) then 19 else
  if p.val = (true, vertices_52) then 10 else
  if p.val = (true, vertices_148) then 11 else
  if p.val = (true, vertices_388) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
cert_nodeAtPriority_9 0 57 1 14 134 262 194 578 386 642 770 28 52 148 388 208 416 331 301 204 601 689 865
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 5 6 204
cert_row_4 1 0 3 5 6 8 722 194 1
cert_row_4 2 0 4 6 7 8 930 386 1
cert_row_4 3 1 3 4 6 7 436 52 3
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 0 0 1 2 5 14 206 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 390
cert_cover_2 2 1 0 6 7 134 390 3
cert_coverFacet 3 722
cert_cover_5 3 1 0 3 5 6 194 722 1
cert_coverFacet 4 930
cert_cover_5 4 2 0 4 6 7 386 930 1
cert_coverFacet 5 834
cert_cover_2 5 5 0 7 8 322 834 3
cert_coverFacet 6 60
cert_cover_2 6 2 1 3 4 28 60 3
cert_coverFacet 7 220
cert_cover_5 7 0 1 2 3 5 28 220 3
cert_coverFacet 8 436
cert_cover_5 8 3 1 3 4 6 52 436 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0531

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e10q1_0532.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0532

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [179, 227, 541, 205, 149, 841, 625, 406, 458, 306, 866, 652, 820, 900, 904, 163, 13, 21, 133, 73, 521, 49, 145, 529, 97, 193, 577, 50, 146, 274, 98, 290, 194, 322, 386, 140, 524, 148, 276, 532, 388, 644, 772, 200, 328, 392, 648, 776, 304, 560, 608, 800, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_179, vertices_227, vertices_541, vertices_205, vertices_149, vertices_841, vertices_625, vertices_406, vertices_458, vertices_306, vertices_866, vertices_652, vertices_820, vertices_900, vertices_904] (by decide +kernel)
  polygons := literalFinset [vertices_163, vertices_13, vertices_21, vertices_133, vertices_73, vertices_521, vertices_49, vertices_145, vertices_529, vertices_97, vertices_193, vertices_577, vertices_50, vertices_146, vertices_274, vertices_98, vertices_290, vertices_194, vertices_322, vertices_386, vertices_140, vertices_524, vertices_148, vertices_276, vertices_532, vertices_388, vertices_644, vertices_772, vertices_200, vertices_328, vertices_392, vertices_648, vertices_776, vertices_304, vertices_560, vertices_608, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_179), (false, vertices_227), (false, vertices_541), (false, vertices_205), (false, vertices_149), (false, vertices_841), (false, vertices_625), (true, vertices_274), (true, vertices_290), (true, vertices_322), (true, vertices_386), (true, vertices_276), (true, vertices_388), (true, vertices_644), (true, vertices_772), (true, vertices_392), (true, vertices_648), (true, vertices_304), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_179) then 15 else
  if p.val = (false, vertices_227) then 16 else
  if p.val = (false, vertices_541) then 18 else
  if p.val = (false, vertices_205) then 19 else
  if p.val = (false, vertices_149) then 0 else
  if p.val = (false, vertices_841) then 21 else
  if p.val = (false, vertices_625) then 23 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_322) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_388) then 6 else
  if p.val = (true, vertices_644) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_800) then 12 else
  if p.val = (true, vertices_896) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_149), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
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
cert_row_4 0 0 2 5 6 7 458 194 1
cert_row_4 1 0 1 3 6 7 406 146 1
cert_row_4 2 0 4 5 7 8 866 98 3
cert_row_4 3 1 3 4 7 8 820 276 2
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 1 0 1 3 6 146 406 1
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 6 194 458 1
cert_coverFacet 2 306
cert_cover_2 2 3 0 4 7 50 306 3
cert_coverFacet 3 866
cert_cover_5 3 2 0 4 5 7 98 866 3
cert_coverFacet 4 652
cert_cover_2 4 2 1 6 8 140 652 3
cert_coverFacet 5 820
cert_cover_5 5 3 1 3 4 7 276 820 2
cert_coverFacet 6 900
cert_cover_2 6 6 1 7 8 388 900 3
cert_coverFacet 7 904
cert_cover_2 7 6 2 7 8 392 904 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0532

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m15e10q1_0533.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0533

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [55, 179, 29, 333, 421, 217, 961, 30, 526, 550, 538, 722, 930, 812, 856, 51, 13, 21, 37, 261, 25, 73, 145, 161, 193, 321, 385, 14, 22, 38, 518, 26, 522, 146, 530, 162, 546, 642, 28, 268, 524, 292, 548, 88, 536, 328, 776, 208, 592, 416, 800, 704, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_55, vertices_179, vertices_29, vertices_333, vertices_421, vertices_217, vertices_961, vertices_30, vertices_526, vertices_550, vertices_538, vertices_722, vertices_930, vertices_812, vertices_856] (by decide +kernel)
  polygons := literalFinset [vertices_51, vertices_13, vertices_21, vertices_37, vertices_261, vertices_25, vertices_73, vertices_145, vertices_161, vertices_193, vertices_321, vertices_385, vertices_14, vertices_22, vertices_38, vertices_518, vertices_26, vertices_522, vertices_146, vertices_530, vertices_162, vertices_546, vertices_642, vertices_28, vertices_268, vertices_524, vertices_292, vertices_548, vertices_88, vertices_536, vertices_328, vertices_776, vertices_208, vertices_592, vertices_416, vertices_800, vertices_704, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_55), (false, vertices_179), (false, vertices_29), (false, vertices_333), (false, vertices_421), (false, vertices_217), (false, vertices_961), (true, vertices_14), (true, vertices_518), (true, vertices_26), (true, vertices_522), (true, vertices_530), (true, vertices_546), (true, vertices_642), (true, vertices_524), (true, vertices_548), (true, vertices_536), (true, vertices_776), (true, vertices_592), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 23 24 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_55) then 15 else
  if p.val = (false, vertices_179) then 16 else
  if p.val = (false, vertices_29) then 0 else
  if p.val = (false, vertices_333) then 18 else
  if p.val = (false, vertices_421) then 19 else
  if p.val = (false, vertices_217) then 21 else
  if p.val = (false, vertices_961) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_800) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_29), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_55), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
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
cert_row_4 0 1 2 4 7 8 812 268 2
cert_row_4 1 0 4 6 7 8 930 162 3
cert_row_4 2 0 3 5 6 8 722 146 2
cert_row_4 3 2 3 5 7 8 856 88 3
cert_rows
cert_pivot_2 1 4 0 2
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 550
cert_cover_2 2 1 0 4 8 38 550 3
cert_coverFacet 3 538
cert_cover_2 3 2 0 3 8 26 538 3
cert_coverFacet 4 722
cert_cover_5 4 2 0 3 5 6 146 722 2
cert_coverFacet 5 930
cert_cover_5 5 1 0 4 6 7 162 930 3
cert_coverFacet 6 812
cert_cover_5 6 0 1 2 4 7 268 812 2
cert_coverFacet 7 856
cert_cover_5 7 3 2 3 5 7 88 856 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0533

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m15e10q1_0534.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0534

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 205, 269, 661, 345, 241, 785, 558, 270, 298, 370, 690, 786, 684, 488, 13, 133, 261, 517, 73, 265, 81, 145, 273, 529, 193, 769, 14, 262, 518, 42, 266, 50, 274, 530, 290, 546, 770, 556, 140, 268, 644, 168, 296, 200, 328, 112, 176, 336, 656, 784, 224, 352, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_205, vertices_269, vertices_661, vertices_345, vertices_241, vertices_785, vertices_558, vertices_270, vertices_298, vertices_370, vertices_690, vertices_786, vertices_684, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_261, vertices_517, vertices_73, vertices_265, vertices_81, vertices_145, vertices_273, vertices_529, vertices_193, vertices_769, vertices_14, vertices_262, vertices_518, vertices_42, vertices_266, vertices_50, vertices_274, vertices_530, vertices_290, vertices_546, vertices_770, vertices_556, vertices_140, vertices_268, vertices_644, vertices_168, vertices_296, vertices_200, vertices_328, vertices_112, vertices_176, vertices_336, vertices_656, vertices_784, vertices_224, vertices_352, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_205), (false, vertices_269), (false, vertices_661), (false, vertices_345), (false, vertices_241), (false, vertices_785), (true, vertices_14), (true, vertices_42), (true, vertices_266), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_546), (true, vertices_556), (true, vertices_168), (true, vertices_296), (true, vertices_352), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 15 else
  if p.val = (false, vertices_205) then 17 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_661) then 18 else
  if p.val = (false, vertices_345) then 21 else
  if p.val = (false, vertices_241) then 23 else
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
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_352) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
cert_nodeAtPriority_54 269 785 14 42 266 50 274 530 290 546 168 296 352 672 775 205 661 556 345 241
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 4 8 556
cert_row_4 1 0 3 4 6 8 690 50 3
cert_row_4 2 0 3 4 5 7 370 50 3
cert_row_4 3 2 4 5 6 7 488 168 2
cert_rows
cert_pivot_2 1 8 0 2
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 0 0 1 2 4 14 558 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 298
cert_cover_2 2 2 0 4 7 42 298 3
cert_coverFacet 3 370
cert_cover_5 3 2 0 3 4 5 50 370 3
cert_coverFacet 4 690
cert_cover_5 4 1 0 3 4 6 50 690 3
cert_coverFacet 5 786
cert_cover_2 5 3 0 7 8 274 786 3
cert_coverFacet 6 684
cert_cover_5 6 0 1 2 4 6 556 684 3
cert_coverFacet 7 488
cert_cover_5 7 3 2 4 5 6 168 488 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0534

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m15e10q1_0535.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0535

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 109, 269, 597, 773, 425, 737, 542, 314, 778, 434, 722, 60, 780, 244, 13, 69, 261, 517, 41, 265, 97, 161, 577, 385, 641, 769, 26, 266, 522, 306, 146, 530, 386, 642, 770, 28, 44, 268, 524, 52, 84, 532, 100, 772, 56, 296, 776, 176, 208, 592, 224, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_109, vertices_269, vertices_597, vertices_773, vertices_425, vertices_737, vertices_542, vertices_314, vertices_778, vertices_434, vertices_722, vertices_60, vertices_780, vertices_244] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_261, vertices_517, vertices_41, vertices_265, vertices_97, vertices_161, vertices_577, vertices_385, vertices_641, vertices_769, vertices_26, vertices_266, vertices_522, vertices_306, vertices_146, vertices_530, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_268, vertices_524, vertices_52, vertices_84, vertices_532, vertices_100, vertices_772, vertices_56, vertices_296, vertices_776, vertices_176, vertices_208, vertices_592, vertices_224, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_109), (false, vertices_269), (false, vertices_597), (false, vertices_773), (false, vertices_425), (false, vertices_737), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_306), (true, vertices_146), (true, vertices_530), (true, vertices_28), (true, vertices_524), (true, vertices_52), (true, vertices_56), (true, vertices_776), (true, vertices_176), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 15 else
  if p.val = (false, vertices_109) then 18 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_597) then 19 else
  if p.val = (false, vertices_773) then 1 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_737) then 24 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_306) then 16 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_208) then 13 else
  0
cert_priority
cert_nodeAtPriority_53 0 269 1 773 26 266 522 146 530 28 524 52 56 776 176 208 899 306 109 597 425 737
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 4 7 306
cert_row_4 1 0 1 2 3 8 542 26 1
cert_row_4 2 0 3 5 6 8 722 146 2
cert_row_4 3 1 3 4 5 6 244 52 3
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
cert_coverFacet 7 244
cert_cover_5 7 3 1 3 4 5 52 244 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0535

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m15e10q1_0536.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0536

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 661, 805, 389, 217, 841, 393, 678, 122, 186, 658, 866, 364, 172, 396, 133, 261, 517, 73, 137, 265, 81, 145, 529, 577, 385, 769, 58, 82, 146, 530, 98, 162, 546, 578, 642, 44, 140, 268, 164, 292, 548, 388, 644, 88, 152, 104, 168, 328, 392, 656, 352, 800, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_661, vertices_805, vertices_389, vertices_217, vertices_841, vertices_393, vertices_678, vertices_122, vertices_186, vertices_658, vertices_866, vertices_364, vertices_172, vertices_396] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_265, vertices_81, vertices_145, vertices_529, vertices_577, vertices_385, vertices_769, vertices_58, vertices_82, vertices_146, vertices_530, vertices_98, vertices_162, vertices_546, vertices_578, vertices_642, vertices_44, vertices_140, vertices_268, vertices_164, vertices_292, vertices_548, vertices_388, vertices_644, vertices_88, vertices_152, vertices_104, vertices_168, vertices_328, vertices_392, vertices_656, vertices_352, vertices_800, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_661), (false, vertices_805), (false, vertices_389), (false, vertices_217), (false, vertices_841), (false, vertices_393), (true, vertices_58), (true, vertices_146), (true, vertices_98), (true, vertices_162), (true, vertices_546), (true, vertices_642), (true, vertices_44), (true, vertices_140), (true, vertices_268), (true, vertices_164), (true, vertices_104), (true, vertices_168), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 15 else
  if p.val = (false, vertices_661) then 18 else
  if p.val = (false, vertices_805) then 19 else
  if p.val = (false, vertices_389) then 0 else
  if p.val = (false, vertices_217) then 21 else
  if p.val = (false, vertices_841) then 22 else
  if p.val = (false, vertices_393) then 1 else
  if p.val = (true, vertices_58) then 16 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_98) then 3 else
  if p.val = (true, vertices_162) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_44) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_164) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_352) then 13 else
  0
cert_priority
cert_nodeAtPriority_25 0 389 1 393 146 98 162 546 642 44 140 268 164 104 168 352 595 58 661 805 217 841
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 4 58
cert_row_4 1 0 1 4 6 8 678 162 1
cert_row_4 2 0 4 5 7 8 866 98 3
cert_row_4 3 1 2 4 5 7 364 44 3
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 678
cert_cover_5 0 1 0 1 4 6 162 678 1
cert_coverFacet 1 122
cert_cover_5 1 0 0 2 3 5 58 122 3
cert_coverFacet 2 186
cert_cover_5 2 0 0 2 3 6 58 186 3
cert_coverFacet 3 658
cert_cover_2 3 3 0 6 8 146 658 3
cert_coverFacet 4 866
cert_cover_5 4 2 0 4 5 7 98 866 3
cert_coverFacet 5 364
cert_cover_5 5 3 1 2 4 5 44 364 3
cert_coverFacet 6 172
cert_cover_2 6 2 1 4 6 44 172 3
cert_coverFacet 7 396
cert_cover_2 7 2 1 6 7 140 396 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0536

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m15e10q1_0537.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0537

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [527, 77, 357, 901, 665, 457, 94, 118, 294, 774, 538, 690, 802, 248, 992, 13, 69, 261, 517, 73, 137, 521, 321, 385, 641, 14, 86, 38, 262, 518, 26, 522, 50, 530, 290, 546, 770, 76, 100, 292, 772, 88, 152, 536, 200, 112, 176, 656, 224, 352, 672, 800, 448, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_527, vertices_77, vertices_357, vertices_901, vertices_665, vertices_457, vertices_94, vertices_118, vertices_294, vertices_774, vertices_538, vertices_690, vertices_802, vertices_248, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_261, vertices_517, vertices_73, vertices_137, vertices_521, vertices_321, vertices_385, vertices_641, vertices_14, vertices_86, vertices_38, vertices_262, vertices_518, vertices_26, vertices_522, vertices_50, vertices_530, vertices_290, vertices_546, vertices_770, vertices_76, vertices_100, vertices_292, vertices_772, vertices_88, vertices_152, vertices_536, vertices_200, vertices_112, vertices_176, vertices_656, vertices_224, vertices_352, vertices_672, vertices_800, vertices_448, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_527), (false, vertices_77), (false, vertices_357), (false, vertices_901), (false, vertices_665), (false, vertices_457), (true, vertices_86), (true, vertices_38), (true, vertices_262), (true, vertices_26), (true, vertices_50), (true, vertices_530), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_88), (true, vertices_112), (true, vertices_176), (true, vertices_224), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_527) then 16 else
  if p.val = (false, vertices_77) then 0 else
  if p.val = (false, vertices_357) then 19 else
  if p.val = (false, vertices_901) then 20 else
  if p.val = (false, vertices_665) then 22 else
  if p.val = (false, vertices_457) then 23 else
  if p.val = (true, vertices_86) then 17 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_672) then 13 else
  if p.val = (true, vertices_800) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_77), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_86), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
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
cert_row_2 0 0 1 3 5 86
cert_row_4 1 0 3 4 6 8 690 50 3
cert_row_4 2 2 3 4 5 6 248 88 2
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 1 0 2 4
cert_heightProof 4
cert_coverFacet 0 94
cert_cover_5 0 0 0 1 2 3 14 94 3
cert_coverFacet 1 118
cert_cover_5 1 0 0 1 3 4 86 118 3
cert_coverFacet 2 294
cert_cover_2 2 1 0 4 7 38 294 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 538
cert_cover_2 4 2 0 3 8 26 538 3
cert_coverFacet 5 690
cert_cover_5 5 1 0 3 4 6 50 690 3
cert_coverFacet 6 802
cert_cover_2 6 4 0 7 8 290 802 3
cert_coverFacet 7 248
cert_cover_5 7 2 2 3 4 5 88 248 2
cert_coverFacet 8 992
cert_cover_5 8 3 4 5 6 7 224 992 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0537

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m15e10q1_0538.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0538

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 781, 105, 713, 241, 929, 110, 270, 118, 534, 774, 434, 786, 604, 976, 41, 73, 265, 521, 97, 161, 289, 193, 641, 769, 14, 22, 102, 262, 518, 42, 266, 50, 274, 530, 290, 770, 76, 268, 524, 84, 532, 772, 104, 584, 112, 176, 208, 592, 400, 784, 416, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_781, vertices_105, vertices_713, vertices_241, vertices_929, vertices_110, vertices_270, vertices_118, vertices_534, vertices_774, vertices_434, vertices_786, vertices_604, vertices_976] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_265, vertices_521, vertices_97, vertices_161, vertices_289, vertices_193, vertices_641, vertices_769, vertices_14, vertices_22, vertices_102, vertices_262, vertices_518, vertices_42, vertices_266, vertices_50, vertices_274, vertices_530, vertices_290, vertices_770, vertices_76, vertices_268, vertices_524, vertices_84, vertices_532, vertices_772, vertices_104, vertices_584, vertices_112, vertices_176, vertices_208, vertices_592, vertices_400, vertices_784, vertices_416, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_781), (false, vertices_105), (false, vertices_713), (false, vertices_241), (false, vertices_929), (true, vertices_14), (true, vertices_22), (true, vertices_102), (true, vertices_262), (true, vertices_518), (true, vertices_50), (true, vertices_274), (true, vertices_530), (true, vertices_770), (true, vertices_76), (true, vertices_84), (true, vertices_532), (true, vertices_592), (true, vertices_400), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 16 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_105) then 0 else
  if p.val = (false, vertices_713) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (false, vertices_929) then 25 else
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
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_784) then 14 else
  0
cert_priority
cert_nodeAtPriority_13 105 14 22 262 518 50 274 530 770 76 84 532 592 400 784 299 102 781 713 241 929
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 5 8 604 76 2
cert_row_2 1 0 1 4 5 102
cert_row_4 2 0 3 4 6 7 434 50 3
cert_row_4 3 3 5 6 7 8 976 208 3
cert_rows
cert_pivot_2 2 1 0 3
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
cert_cover_5 5 2 0 3 4 6 50 434 3
cert_coverFacet 6 786
cert_cover_2 6 3 0 7 8 274 786 3
cert_coverFacet 7 604
cert_cover_5 7 0 1 2 3 5 76 604 2
cert_coverFacet 8 976
cert_cover_5 8 3 3 5 6 7 208 976 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0538

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m15e10q1_0539.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0539

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 557, 117, 709, 817, 465, 590, 218, 410, 810, 706, 92, 284, 300, 308, 37, 69, 517, 49, 81, 273, 545, 193, 385, 641, 769, 154, 74, 266, 522, 194, 578, 386, 642, 770, 28, 44, 76, 268, 524, 52, 84, 276, 292, 580, 88, 280, 296, 552, 304, 208, 400, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_557, vertices_117, vertices_709, vertices_817, vertices_465, vertices_590, vertices_218, vertices_410, vertices_810, vertices_706, vertices_92, vertices_284, vertices_300, vertices_308] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_517, vertices_49, vertices_81, vertices_273, vertices_545, vertices_193, vertices_385, vertices_641, vertices_769, vertices_154, vertices_74, vertices_266, vertices_522, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_76, vertices_268, vertices_524, vertices_52, vertices_84, vertices_276, vertices_292, vertices_580, vertices_88, vertices_280, vertices_296, vertices_552, vertices_304, vertices_208, vertices_400, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_557), (false, vertices_117), (false, vertices_709), (false, vertices_817), (false, vertices_465), (true, vertices_154), (true, vertices_74), (true, vertices_266), (true, vertices_522), (true, vertices_194), (true, vertices_578), (true, vertices_28), (true, vertices_76), (true, vertices_268), (true, vertices_276), (true, vertices_292), (true, vertices_88), (true, vertices_280), (true, vertices_296)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 21 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 14 else
  if p.val = (false, vertices_557) then 17 else
  if p.val = (false, vertices_117) then 18 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_817) then 22 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (true, vertices_154) then 15 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_578) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_88) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_296) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_154), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 6 154
cert_row_4 1 0 1 2 5 8 590 74 1
cert_row_4 2 0 2 4 7 8 810 266 2
cert_rows_3
cert_pivot_3 1 3 0
cert_heightProof 3
cert_coverFacet 0 590
cert_cover_5 0 1 0 1 2 5 74 590 1
cert_coverFacet 1 218
cert_cover_5 1 0 0 2 3 5 154 218 3
cert_coverFacet 2 410
cert_cover_5 2 0 0 2 3 7 154 410 3
cert_coverFacet 3 810
cert_cover_5 3 2 0 2 4 7 266 810 2
cert_coverFacet 4 706
cert_cover_2 4 5 0 6 8 194 706 3
cert_coverFacet 5 92
cert_cover_2 5 2 1 3 5 28 92 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 300
cert_cover_2 7 2 1 4 7 44 300 3
cert_coverFacet 8 308
cert_cover_2 8 3 1 4 7 52 308 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 3 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0539

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e10q1_0540.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0540

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 301, 405, 677, 617, 393, 662, 458, 586, 626, 466, 788, 804, 376, 816, 37, 133, 261, 41, 137, 265, 521, 545, 385, 641, 74, 138, 522, 82, 146, 530, 450, 578, 642, 148, 276, 532, 292, 548, 644, 772, 104, 296, 328, 584, 392, 112, 304, 560, 336, 400, 784, 608, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_301, vertices_405, vertices_677, vertices_617, vertices_393, vertices_662, vertices_458, vertices_586, vertices_626, vertices_466, vertices_788, vertices_804, vertices_376, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_41, vertices_137, vertices_265, vertices_521, vertices_545, vertices_385, vertices_641, vertices_74, vertices_138, vertices_522, vertices_82, vertices_146, vertices_530, vertices_450, vertices_578, vertices_642, vertices_148, vertices_276, vertices_532, vertices_292, vertices_548, vertices_644, vertices_772, vertices_104, vertices_296, vertices_328, vertices_584, vertices_392, vertices_112, vertices_304, vertices_560, vertices_336, vertices_400, vertices_784, vertices_608, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_301), (false, vertices_405), (false, vertices_677), (false, vertices_617), (false, vertices_393), (true, vertices_74), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_450), (true, vertices_578), (true, vertices_532), (true, vertices_772), (true, vertices_328), (true, vertices_112), (true, vertices_304), (true, vertices_560), (true, vertices_336), (true, vertices_784), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 16 else
  if p.val = (false, vertices_301) then 19 else
  if p.val = (false, vertices_405) then 20 else
  if p.val = (false, vertices_677) then 21 else
  if p.val = (false, vertices_617) then 23 else
  if p.val = (false, vertices_393) then 0 else
  if p.val = (true, vertices_74) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_450) then 17 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_772) then 7 else
  if p.val = (true, vertices_328) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_560) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_784) then 13 else
  if p.val = (true, vertices_800) then 14 else
  0
cert_priority
cert_nodeAtPriority_51 393 74 82 146 530 578 532 772 328 112 304 560 336 784 800 651 450 301 405 677 617
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 8 662 146 1
cert_row_2 1 0 5 6 7 450
cert_row_4 2 0 3 4 5 8 626 82 2
cert_row_4 3 2 3 4 5 7 376 104 1
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 146 662 1
cert_coverFacet 1 458
cert_cover_5 1 1 0 2 5 6 74 458 3
cert_coverFacet 2 586
cert_cover_2 2 2 0 5 8 74 586 3
cert_coverFacet 3 626
cert_cover_5 3 2 0 3 4 5 82 626 2
cert_coverFacet 4 466
cert_cover_5 4 1 0 3 5 6 82 466 3
cert_coverFacet 5 788
cert_cover_2 5 3 1 7 8 276 788 3
cert_coverFacet 6 804
cert_cover_2 6 4 1 7 8 292 804 3
cert_coverFacet 7 376
cert_cover_5 7 3 2 3 4 5 104 376 1
cert_coverFacet 8 816
cert_cover_2 8 4 3 7 8 304 816 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0540

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e10q1_0541.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0541

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 653, 213, 613, 393, 849, 401, 678, 186, 314, 650, 866, 372, 180, 408, 69, 133, 517, 137, 265, 521, 81, 145, 273, 577, 385, 769, 58, 138, 266, 522, 162, 290, 546, 642, 770, 52, 84, 148, 100, 164, 548, 644, 152, 280, 392, 648, 176, 304, 336, 400, 352, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_653, vertices_213, vertices_613, vertices_393, vertices_849, vertices_401, vertices_678, vertices_186, vertices_314, vertices_650, vertices_866, vertices_372, vertices_180, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_517, vertices_137, vertices_265, vertices_521, vertices_81, vertices_145, vertices_273, vertices_577, vertices_385, vertices_769, vertices_58, vertices_138, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_52, vertices_84, vertices_148, vertices_100, vertices_164, vertices_548, vertices_644, vertices_152, vertices_280, vertices_392, vertices_648, vertices_176, vertices_304, vertices_336, vertices_400, vertices_352, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_653), (false, vertices_213), (false, vertices_613), (false, vertices_393), (false, vertices_849), (false, vertices_401), (true, vertices_58), (true, vertices_138), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_642), (true, vertices_52), (true, vertices_164), (true, vertices_152), (true, vertices_280), (true, vertices_176), (true, vertices_304), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 15 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_213) then 19 else
  if p.val = (false, vertices_613) then 20 else
  if p.val = (false, vertices_393) then 0 else
  if p.val = (false, vertices_849) then 23 else
  if p.val = (false, vertices_401) then 1 else
  if p.val = (true, vertices_58) then 16 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_176) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_352) then 13 else
  0
cert_priority
cert_nodeAtPriority_15 0 393 1 401 138 162 290 546 642 52 164 152 280 176 304 352 779 58 653 213 613 849
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 4 58
cert_row_4 1 0 1 4 6 8 678 162 1
cert_row_4 2 0 4 5 7 8 866 290 2
cert_row_4 3 1 3 4 5 7 372 52 3
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
cert_coverFacet 5 372
cert_cover_5 5 3 1 3 4 5 52 372 3
cert_coverFacet 6 180
cert_cover_2 6 3 1 4 6 52 180 3
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0541

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e10q1_0542.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0542

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 597, 217, 425, 841, 689, 158, 286, 678, 838, 170, 298, 340, 660, 344, 73, 137, 265, 81, 145, 529, 161, 289, 545, 577, 769, 30, 134, 262, 518, 42, 138, 266, 162, 290, 546, 770, 84, 148, 276, 532, 324, 580, 644, 88, 152, 280, 168, 296, 328, 336, 656, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_597, vertices_217, vertices_425, vertices_841, vertices_689, vertices_158, vertices_286, vertices_678, vertices_838, vertices_170, vertices_298, vertices_340, vertices_660, vertices_344] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_265, vertices_81, vertices_145, vertices_529, vertices_161, vertices_289, vertices_545, vertices_577, vertices_769, vertices_30, vertices_134, vertices_262, vertices_518, vertices_42, vertices_138, vertices_266, vertices_162, vertices_290, vertices_546, vertices_770, vertices_84, vertices_148, vertices_276, vertices_532, vertices_324, vertices_580, vertices_644, vertices_88, vertices_152, vertices_280, vertices_168, vertices_296, vertices_328, vertices_336, vertices_656, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_597), (false, vertices_217), (false, vertices_425), (false, vertices_841), (false, vertices_689), (true, vertices_30), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_162), (true, vertices_148), (true, vertices_276), (true, vertices_324), (true, vertices_644), (true, vertices_280), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 18 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 14 else
  if p.val = (false, vertices_597) then 17 else
  if p.val = (false, vertices_217) then 19 else
  if p.val = (false, vertices_425) then 20 else
  if p.val = (false, vertices_841) then 21 else
  if p.val = (false, vertices_689) then 23 else
  if p.val = (true, vertices_30) then 15 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_336) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_30), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
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
cert_row_2 0 0 1 2 3 30
cert_row_4 1 0 1 4 6 8 678 134 2
cert_row_4 2 0 1 5 7 8 838 262 2
cert_rows_3
cert_pivot_3 4 2 0
cert_heightProof 3
cert_coverFacet 0 158
cert_cover_5 0 0 0 1 2 6 30 158 3
cert_coverFacet 1 286
cert_cover_5 1 0 0 1 2 7 30 286 3
cert_coverFacet 2 678
cert_cover_5 2 1 0 1 4 6 134 678 2
cert_coverFacet 3 838
cert_cover_5 3 2 0 1 5 7 262 838 2
cert_coverFacet 4 170
cert_cover_2 4 2 0 4 6 42 170 3
cert_coverFacet 5 298
cert_cover_2 5 2 0 4 7 42 298 3
cert_coverFacet 6 340
cert_cover_2 6 3 1 5 7 84 340 3
cert_coverFacet 7 660
cert_cover_2 7 3 1 6 8 148 660 3
cert_coverFacet 8 344
cert_cover_2 8 3 2 5 7 88 344 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 3 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0542

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e10q1_0543.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0543

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [151, 535, 395, 803, 653, 841, 370, 562, 402, 244, 564, 868, 708, 472, 712, 23, 131, 259, 515, 133, 517, 137, 265, 521, 769, 50, 146, 274, 530, 290, 546, 386, 52, 148, 532, 100, 548, 196, 580, 644, 200, 328, 584, 392, 648, 112, 560, 208, 336, 400, 352, 800, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_151, vertices_535, vertices_395, vertices_803, vertices_653, vertices_841, vertices_370, vertices_562, vertices_402, vertices_244, vertices_564, vertices_868, vertices_708, vertices_472, vertices_712] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_131, vertices_259, vertices_515, vertices_133, vertices_517, vertices_137, vertices_265, vertices_521, vertices_769, vertices_50, vertices_146, vertices_274, vertices_530, vertices_290, vertices_546, vertices_386, vertices_52, vertices_148, vertices_532, vertices_100, vertices_548, vertices_196, vertices_580, vertices_644, vertices_200, vertices_328, vertices_584, vertices_392, vertices_648, vertices_112, vertices_560, vertices_208, vertices_336, vertices_400, vertices_352, vertices_800, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_151), (false, vertices_535), (false, vertices_395), (false, vertices_803), (false, vertices_653), (false, vertices_841), (true, vertices_50), (true, vertices_274), (true, vertices_52), (true, vertices_100), (true, vertices_548), (true, vertices_196), (true, vertices_580), (true, vertices_200), (true, vertices_112), (true, vertices_560), (true, vertices_208), (true, vertices_336), (true, vertices_400), (true, vertices_352), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 15 22 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_151) then 16 else
  if p.val = (false, vertices_535) then 17 else
  if p.val = (false, vertices_395) then 20 else
  if p.val = (false, vertices_803) then 21 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_841) then 23 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_274) then 1 else
  if p.val = (true, vertices_52) then 2 else
  if p.val = (true, vertices_100) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_580) then 6 else
  if p.val = (true, vertices_200) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_352) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_151), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 22 => Sum.inl 2
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
cert_row_4 0 0 3 4 5 7 370 50 3
cert_row_4 1 1 4 5 7 8 868 100 3
cert_row_4 2 1 3 4 5 6 244 52 3
cert_row_4 3 2 3 5 6 7 472 200 1
cert_rows
cert_pivot_2 0 8 1 2
cert_heightProof 4
cert_coverFacet 0 370
cert_cover_5 0 0 0 3 4 5 50 370 3
cert_coverFacet 1 562
cert_cover_2 1 3 0 4 8 50 562 3
cert_coverFacet 2 402
cert_cover_2 2 3 0 6 7 146 402 3
cert_coverFacet 3 244
cert_cover_5 3 2 1 3 4 5 52 244 3
cert_coverFacet 4 564
cert_cover_2 4 3 1 4 8 52 564 3
cert_coverFacet 5 868
cert_cover_5 5 1 1 4 5 7 100 868 3
cert_coverFacet 6 708
cert_cover_2 6 5 1 6 8 196 708 3
cert_coverFacet 7 472
cert_cover_5 7 3 2 3 5 6 200 472 1
cert_coverFacet 8 712
cert_cover_2 8 5 2 6 8 200 712 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0543

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e10q1_0544.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0544

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 563, 147, 355, 781, 665, 801, 342, 406, 114, 716, 396, 212, 868, 752, 19, 35, 131, 259, 137, 265, 521, 145, 529, 289, 545, 769, 278, 50, 82, 146, 98, 322, 386, 140, 268, 524, 84, 148, 196, 324, 580, 388, 772, 392, 648, 112, 560, 208, 656, 352, 608, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_563, vertices_147, vertices_355, vertices_781, vertices_665, vertices_801, vertices_342, vertices_406, vertices_114, vertices_716, vertices_396, vertices_212, vertices_868, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_131, vertices_259, vertices_137, vertices_265, vertices_521, vertices_145, vertices_529, vertices_289, vertices_545, vertices_769, vertices_278, vertices_50, vertices_82, vertices_146, vertices_98, vertices_322, vertices_386, vertices_140, vertices_268, vertices_524, vertices_84, vertices_148, vertices_196, vertices_324, vertices_580, vertices_388, vertices_772, vertices_392, vertices_648, vertices_112, vertices_560, vertices_208, vertices_656, vertices_352, vertices_608, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_563), (false, vertices_147), (false, vertices_355), (false, vertices_781), (false, vertices_665), (false, vertices_801), (true, vertices_278), (true, vertices_82), (true, vertices_140), (true, vertices_84), (true, vertices_148), (true, vertices_196), (true, vertices_324), (true, vertices_580), (true, vertices_388), (true, vertices_112), (true, vertices_208), (true, vertices_608), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 14 21 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 18 else
  if p.val = (false, vertices_563) then 19 else
  if p.val = (false, vertices_147) then 0 else
  if p.val = (false, vertices_355) then 20 else
  if p.val = (false, vertices_781) then 15 else
  if p.val = (false, vertices_665) then 22 else
  if p.val = (false, vertices_801) then 1 else
  if p.val = (true, vertices_278) then 16 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_148) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_580) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_608) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
cert_nodeAtPriority_4 1 147 0 801 82 140 84 148 196 324 580 388 112 208 608 704 781 278 395 563 355 665
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 7 278
cert_row_4 1 1 2 5 6 8 716 140 2
cert_row_4 2 1 4 5 7 8 868 324 1
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 0 0 1 3 5 278 342 3
cert_coverFacet 1 406
cert_cover_5 1 0 0 1 3 6 278 406 3
cert_coverFacet 2 114
cert_cover_2 2 3 0 4 5 50 114 3
cert_coverFacet 3 716
cert_cover_5 3 1 1 2 5 6 140 716 2
cert_coverFacet 4 396
cert_cover_2 4 2 1 6 7 140 396 3
cert_coverFacet 5 212
cert_cover_2 5 3 1 5 6 84 212 3
cert_coverFacet 6 868
cert_cover_5 6 2 1 4 5 7 324 868 1
cert_coverFacet 7 752
cert_cover_5 7 3 3 4 5 6 112 752 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0544

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m15e10q1_0545.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0545

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 557, 789, 229, 389, 865, 286, 186, 394, 242, 850, 540, 172, 396, 632, 37, 133, 261, 517, 97, 545, 193, 321, 385, 769, 26, 138, 266, 178, 82, 274, 194, 322, 386, 28, 44, 140, 268, 524, 276, 532, 164, 388, 56, 536, 168, 552, 392, 112, 592, 784, 224, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_557, vertices_789, vertices_229, vertices_389, vertices_865, vertices_286, vertices_186, vertices_394, vertices_242, vertices_850, vertices_540, vertices_172, vertices_396, vertices_632] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_133, vertices_261, vertices_517, vertices_97, vertices_545, vertices_193, vertices_321, vertices_385, vertices_769, vertices_26, vertices_138, vertices_266, vertices_178, vertices_82, vertices_274, vertices_194, vertices_322, vertices_386, vertices_28, vertices_44, vertices_140, vertices_268, vertices_524, vertices_276, vertices_532, vertices_164, vertices_388, vertices_56, vertices_536, vertices_168, vertices_552, vertices_392, vertices_112, vertices_592, vertices_784, vertices_224, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_557), (false, vertices_789), (false, vertices_229), (false, vertices_389), (false, vertices_865), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_178), (true, vertices_82), (true, vertices_274), (true, vertices_28), (true, vertices_140), (true, vertices_268), (true, vertices_56), (true, vertices_536), (true, vertices_168), (true, vertices_392), (true, vertices_112), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 16 else
  if p.val = (false, vertices_557) then 19 else
  if p.val = (false, vertices_789) then 20 else
  if p.val = (false, vertices_229) then 21 else
  if p.val = (false, vertices_389) then 0 else
  if p.val = (false, vertices_865) then 25 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_178) then 17 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_168) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_592) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_178), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 22 => Sum.inl 2
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
cert_row_2 0 0 3 4 6 178
cert_row_4 1 0 1 2 3 7 286 26 1
cert_row_4 2 0 3 5 7 8 850 82 3
cert_row_4 3 2 3 4 5 8 632 56 3
cert_rows
cert_pivot_2 6 1 0 2
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 1 0 1 2 3 26 286 1
cert_coverFacet 1 186
cert_cover_5 1 0 0 2 3 4 26 186 3
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 242
cert_cover_5 3 0 0 3 4 5 178 242 3
cert_coverFacet 4 850
cert_cover_5 4 2 0 3 5 7 82 850 3
cert_coverFacet 5 540
cert_cover_2 5 2 1 3 8 28 540 3
cert_coverFacet 6 172
cert_cover_2 6 2 1 4 6 44 172 3
cert_coverFacet 7 396
cert_cover_2 7 2 1 6 7 140 396 3
cert_coverFacet 8 632
cert_cover_5 8 3 2 3 4 5 56 632 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0545

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m15e10q1_0546.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0546

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 341, 665, 625, 401, 481, 302, 142, 406, 618, 650, 418, 604, 156, 364, 81, 145, 273, 529, 97, 161, 545, 321, 385, 641, 14, 134, 262, 42, 138, 522, 162, 290, 546, 386, 642, 28, 300, 76, 140, 84, 148, 276, 324, 152, 536, 104, 584, 648, 592, 400, 352, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_341, vertices_665, vertices_625, vertices_401, vertices_481, vertices_302, vertices_142, vertices_406, vertices_618, vertices_650, vertices_418, vertices_604, vertices_156, vertices_364] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_145, vertices_273, vertices_529, vertices_97, vertices_161, vertices_545, vertices_321, vertices_385, vertices_641, vertices_14, vertices_134, vertices_262, vertices_42, vertices_138, vertices_522, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_28, vertices_300, vertices_76, vertices_140, vertices_84, vertices_148, vertices_276, vertices_324, vertices_152, vertices_536, vertices_104, vertices_584, vertices_648, vertices_592, vertices_400, vertices_352, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_341), (false, vertices_665), (false, vertices_625), (false, vertices_401), (false, vertices_481), (true, vertices_14), (true, vertices_134), (true, vertices_262), (true, vertices_42), (true, vertices_138), (true, vertices_522), (true, vertices_290), (true, vertices_386), (true, vertices_28), (true, vertices_300), (true, vertices_76), (true, vertices_140), (true, vertices_148), (true, vertices_104), (true, vertices_584)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 16 else
  if p.val = (false, vertices_341) then 18 else
  if p.val = (false, vertices_665) then 21 else
  if p.val = (false, vertices_625) then 23 else
  if p.val = (false, vertices_401) then 0 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_300) then 19 else
  if p.val = (true, vertices_76) then 10 else
  if p.val = (true, vertices_140) then 11 else
  if p.val = (true, vertices_148) then 12 else
  if p.val = (true, vertices_104) then 13 else
  if p.val = (true, vertices_584) then 14 else
  0
cert_priority
cert_nodeAtPriority_9 0 401 1 14 134 262 42 138 522 290 386 28 76 140 148 104 584 675 341 300 665 625 481
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 7 406 134 2
cert_row_2 1 1 2 4 7 300
cert_row_4 2 0 2 4 5 8 618 42 3
cert_row_4 3 1 2 3 5 8 604 28 3
cert_rows
cert_pivot_2 6 7 0 1
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 1 0 1 2 4 14 302 3
cert_coverFacet 1 142
cert_cover_2 1 1 0 2 6 14 142 3
cert_coverFacet 2 406
cert_cover_5 2 0 0 1 3 6 134 406 2
cert_coverFacet 3 618
cert_cover_5 3 2 0 2 4 5 42 618 3
cert_coverFacet 4 650
cert_cover_2 4 2 0 6 8 138 650 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 604
cert_cover_5 6 3 1 2 3 5 28 604 3
cert_coverFacet 7 156
cert_cover_2 7 2 1 3 6 28 156 3
cert_coverFacet 8 364
cert_cover_5 8 1 1 2 4 5 300 364 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0546

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m15e10q1_0547.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0547

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 109, 269, 597, 773, 425, 737, 782, 314, 538, 434, 722, 60, 540, 244, 13, 69, 261, 517, 41, 265, 97, 161, 577, 385, 641, 769, 26, 266, 522, 306, 146, 530, 386, 642, 770, 28, 44, 268, 524, 52, 84, 532, 100, 772, 56, 536, 296, 176, 208, 592, 224, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_109, vertices_269, vertices_597, vertices_773, vertices_425, vertices_737, vertices_782, vertices_314, vertices_538, vertices_434, vertices_722, vertices_60, vertices_540, vertices_244] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_261, vertices_517, vertices_41, vertices_265, vertices_97, vertices_161, vertices_577, vertices_385, vertices_641, vertices_769, vertices_26, vertices_266, vertices_522, vertices_306, vertices_146, vertices_530, vertices_386, vertices_642, vertices_770, vertices_28, vertices_44, vertices_268, vertices_524, vertices_52, vertices_84, vertices_532, vertices_100, vertices_772, vertices_56, vertices_536, vertices_296, vertices_176, vertices_208, vertices_592, vertices_224, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_109), (false, vertices_269), (false, vertices_597), (false, vertices_773), (false, vertices_425), (false, vertices_737), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_306), (true, vertices_146), (true, vertices_530), (true, vertices_28), (true, vertices_524), (true, vertices_52), (true, vertices_56), (true, vertices_536), (true, vertices_176), (true, vertices_208)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 15 else
  if p.val = (false, vertices_109) then 18 else
  if p.val = (false, vertices_269) then 0 else
  if p.val = (false, vertices_597) then 19 else
  if p.val = (false, vertices_773) then 1 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_737) then 24 else
  if p.val = (true, vertices_26) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_306) then 16 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_208) then 13 else
  0
cert_priority
cert_nodeAtPriority_53 0 269 1 773 26 266 522 146 530 28 524 52 56 536 176 208 899 306 109 597 425 737
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 266 1
cert_row_2 1 0 3 4 7 306
cert_row_4 2 0 3 5 6 8 722 146 2
cert_row_4 3 1 3 4 5 6 244 52 3
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 266 782 1
cert_coverFacet 1 314
cert_cover_5 1 1 0 2 3 4 26 314 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 434
cert_cover_5 3 1 0 3 4 6 306 434 3
cert_coverFacet 4 722
cert_cover_5 4 2 0 3 5 6 146 722 2
cert_coverFacet 5 60
cert_cover_2 5 2 1 3 4 28 60 3
cert_coverFacet 6 540
cert_cover_2 6 2 1 3 8 28 540 3
cert_coverFacet 7 244
cert_cover_5 7 3 1 3 4 5 52 244 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0547

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m15e10q1_0548.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0548

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 653, 213, 773, 345, 233, 777, 566, 774, 362, 682, 778, 306, 692, 496, 21, 133, 261, 517, 73, 137, 265, 521, 81, 273, 193, 769, 22, 262, 518, 42, 266, 522, 50, 274, 290, 546, 770, 564, 148, 644, 772, 104, 168, 328, 648, 776, 176, 304, 208, 336, 224, 352, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_653, vertices_213, vertices_773, vertices_345, vertices_233, vertices_777, vertices_566, vertices_774, vertices_362, vertices_682, vertices_778, vertices_306, vertices_692, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_261, vertices_517, vertices_73, vertices_137, vertices_265, vertices_521, vertices_81, vertices_273, vertices_193, vertices_769, vertices_22, vertices_262, vertices_518, vertices_42, vertices_266, vertices_522, vertices_50, vertices_274, vertices_290, vertices_546, vertices_770, vertices_564, vertices_148, vertices_644, vertices_772, vertices_104, vertices_168, vertices_328, vertices_648, vertices_776, vertices_176, vertices_304, vertices_208, vertices_336, vertices_224, vertices_352, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_653), (false, vertices_213), (false, vertices_773), (false, vertices_345), (false, vertices_233), (false, vertices_777), (true, vertices_518), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_564), (true, vertices_176), (true, vertices_304), (true, vertices_352), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 20 23 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 15 else
  if p.val = (false, vertices_653) then 17 else
  if p.val = (false, vertices_213) then 18 else
  if p.val = (false, vertices_773) then 0 else
  if p.val = (false, vertices_345) then 21 else
  if p.val = (false, vertices_233) then 22 else
  if p.val = (false, vertices_777) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_50) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_770) then 9 else
  if p.val = (true, vertices_564) then 19 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_352) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_773), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_279), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_564), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
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
cert_row_2 0 1 3 4 8 564
cert_row_4 1 0 2 4 6 8 682 42 3
cert_row_4 2 0 2 4 5 7 362 42 3
cert_row_4 3 3 4 5 6 7 496 176 2
cert_rows
cert_pivot_2 1 8 0 3
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 0 0 1 3 4 22 566 3
cert_coverFacet 1 774
cert_cover_2 1 1 0 7 8 262 774 3
cert_coverFacet 2 362
cert_cover_5 2 2 0 2 4 5 42 362 3
cert_coverFacet 3 682
cert_cover_5 3 1 0 2 4 6 42 682 3
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 306
cert_cover_2 5 3 0 4 7 50 306 3
cert_coverFacet 6 692
cert_cover_5 6 0 1 3 4 6 564 692 3
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 176 496 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0548

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m15e10q1_0549.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0549

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 781, 185, 537, 721, 929, 110, 270, 598, 774, 354, 962, 124, 540, 496, 25, 41, 265, 521, 145, 529, 161, 289, 641, 769, 14, 70, 262, 518, 42, 266, 98, 290, 322, 578, 770, 28, 108, 268, 524, 84, 532, 772, 56, 536, 112, 176, 208, 592, 352, 416, 448, 704, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_781, vertices_185, vertices_537, vertices_721, vertices_929, vertices_110, vertices_270, vertices_598, vertices_774, vertices_354, vertices_962, vertices_124, vertices_540, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_265, vertices_521, vertices_145, vertices_529, vertices_161, vertices_289, vertices_641, vertices_769, vertices_14, vertices_70, vertices_262, vertices_518, vertices_42, vertices_266, vertices_98, vertices_290, vertices_322, vertices_578, vertices_770, vertices_28, vertices_108, vertices_268, vertices_524, vertices_84, vertices_532, vertices_772, vertices_56, vertices_536, vertices_112, vertices_176, vertices_208, vertices_592, vertices_352, vertices_416, vertices_448, vertices_704, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_781), (false, vertices_185), (false, vertices_537), (false, vertices_721), (false, vertices_929), (true, vertices_14), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_98), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_28), (true, vertices_108), (true, vertices_84), (true, vertices_532), (true, vertices_112), (true, vertices_352), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 16 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_185) then 21 else
  if p.val = (false, vertices_537) then 0 else
  if p.val = (false, vertices_721) then 23 else
  if p.val = (false, vertices_929) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_108) then 19 else
  if p.val = (true, vertices_84) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_352) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
cert_nodeAtPriority_9 0 537 1 14 70 262 518 98 322 578 770 28 84 532 112 352 448 299 781 108 185 721 929
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 4 5 108
cert_row_4 1 0 1 3 5 8 598 70 2
cert_row_4 2 0 5 6 7 8 962 322 2
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 2 1 0 3
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 0 0 1 2 4 14 110 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 598
cert_cover_5 2 1 0 1 3 5 70 598 2
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 354
cert_cover_2 4 4 0 5 7 98 354 3
cert_coverFacet 5 962
cert_cover_5 5 2 0 5 6 7 322 962 2
cert_coverFacet 6 124
cert_cover_5 6 0 1 2 3 4 28 124 3
cert_coverFacet 7 540
cert_cover_2 7 2 1 3 8 28 540 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 112 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0549

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m15e10q1_0550.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0550

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 355, 387, 643, 661, 457, 241, 654, 810, 394, 220, 844, 116, 564, 868, 35, 131, 259, 515, 49, 145, 529, 97, 193, 321, 385, 641, 138, 266, 522, 290, 546, 386, 642, 76, 140, 524, 52, 84, 148, 532, 100, 548, 836, 644, 200, 328, 392, 776, 112, 560, 208, 352, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_355, vertices_387, vertices_643, vertices_661, vertices_457, vertices_241, vertices_654, vertices_810, vertices_394, vertices_220, vertices_844, vertices_116, vertices_564, vertices_868] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_259, vertices_515, vertices_49, vertices_145, vertices_529, vertices_97, vertices_193, vertices_321, vertices_385, vertices_641, vertices_138, vertices_266, vertices_522, vertices_290, vertices_546, vertices_386, vertices_642, vertices_76, vertices_140, vertices_524, vertices_52, vertices_84, vertices_148, vertices_532, vertices_100, vertices_548, vertices_836, vertices_644, vertices_200, vertices_328, vertices_392, vertices_776, vertices_112, vertices_560, vertices_208, vertices_352, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_355), (false, vertices_387), (false, vertices_643), (false, vertices_661), (false, vertices_457), (false, vertices_241), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_76), (true, vertices_140), (true, vertices_524), (true, vertices_52), (true, vertices_84), (true, vertices_100), (true, vertices_548), (true, vertices_836), (true, vertices_776), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 15 else
  if p.val = (false, vertices_355) then 16 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_643) then 1 else
  if p.val = (false, vertices_661) then 18 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_84) then 9 else
  if p.val = (true, vertices_100) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_836) then 19 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_800) then 13 else
  0
cert_priority
cert_nodeAtPriority_44 387 643 138 266 522 76 140 524 52 84 100 548 776 800 563 355 661 836 457 241
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 7 8 810 266 2
cert_row_2 1 1 5 7 8 836
cert_row_4 2 0 1 2 6 8 654 138 1
cert_row_4 3 1 2 3 5 6 220 76 2
cert_rows
cert_pivot_2 4 7 0 1
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 2 0 1 2 6 138 654 1
cert_coverFacet 1 810
cert_cover_5 1 0 0 2 4 7 266 810 2
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 220
cert_cover_5 3 3 1 2 3 5 76 220 2
cert_coverFacet 4 844
cert_cover_5 4 1 1 2 5 7 76 844 3
cert_coverFacet 5 116
cert_cover_2 5 3 1 4 5 52 116 3
cert_coverFacet 6 564
cert_cover_2 6 3 1 4 8 52 564 3
cert_coverFacet 7 868
cert_cover_5 7 1 1 4 5 7 100 868 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0550

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e10q1_0551.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0551

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 453, 841, 433, 721, 801, 62, 78, 662, 710, 810, 586, 364, 308, 404, 49, 145, 529, 289, 545, 193, 321, 577, 385, 769, 14, 22, 70, 646, 42, 74, 522, 50, 530, 546, 578, 44, 76, 52, 148, 276, 292, 196, 324, 388, 296, 328, 584, 776, 304, 400, 656, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_453, vertices_841, vertices_433, vertices_721, vertices_801, vertices_62, vertices_78, vertices_662, vertices_710, vertices_810, vertices_586, vertices_364, vertices_308, vertices_404] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_145, vertices_529, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_385, vertices_769, vertices_14, vertices_22, vertices_70, vertices_646, vertices_42, vertices_74, vertices_522, vertices_50, vertices_530, vertices_546, vertices_578, vertices_44, vertices_76, vertices_52, vertices_148, vertices_276, vertices_292, vertices_196, vertices_324, vertices_388, vertices_296, vertices_328, vertices_584, vertices_776, vertices_304, vertices_400, vertices_656, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_453), (false, vertices_841), (false, vertices_433), (false, vertices_721), (false, vertices_801), (true, vertices_14), (true, vertices_22), (true, vertices_70), (true, vertices_646), (true, vertices_42), (true, vertices_74), (true, vertices_522), (true, vertices_578), (true, vertices_44), (true, vertices_76), (true, vertices_52), (true, vertices_148), (true, vertices_276), (true, vertices_292), (true, vertices_296)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 16 else
  if p.val = (false, vertices_453) then 19 else
  if p.val = (false, vertices_841) then 21 else
  if p.val = (false, vertices_433) then 23 else
  if p.val = (false, vertices_721) then 24 else
  if p.val = (false, vertices_801) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_70) then 3 else
  if p.val = (true, vertices_646) then 17 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_74) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_76) then 9 else
  if p.val = (true, vertices_52) then 10 else
  if p.val = (true, vertices_148) then 11 else
  if p.val = (true, vertices_276) then 12 else
  if p.val = (true, vertices_292) then 13 else
  if p.val = (true, vertices_296) then 14 else
  0
cert_priority
cert_nodeAtPriority_40 801 14 22 70 42 74 522 578 44 76 52 148 276 292 296 563 646 453 841 433 721
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 6 8 646
cert_row_4 1 0 1 2 3 4 62 14 3
cert_row_4 2 0 2 4 7 8 810 42 3
cert_row_4 3 1 2 4 5 7 364 44 3
cert_rows
cert_pivot_2 6 3 0 1
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 1 0 1 2 3 14 62 3
cert_coverFacet 1 78
cert_cover_2 1 1 0 2 5 14 78 3
cert_coverFacet 2 662
cert_cover_5 2 0 0 1 3 6 22 662 3
cert_coverFacet 3 710
cert_cover_5 3 0 0 1 5 6 70 710 3
cert_coverFacet 4 810
cert_cover_5 4 2 0 2 4 7 42 810 3
cert_coverFacet 5 586
cert_cover_2 5 2 0 5 8 74 586 3
cert_coverFacet 6 364
cert_cover_5 6 3 1 2 4 5 44 364 3
cert_coverFacet 7 308
cert_cover_2 7 3 1 4 7 52 308 3
cert_coverFacet 8 404
cert_cover_2 8 3 1 6 7 148 404 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0551

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e10q1_0552.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0552

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 211, 387, 771, 805, 457, 369, 782, 666, 394, 364, 716, 740, 240, 688, 19, 131, 259, 515, 49, 81, 289, 545, 193, 321, 385, 769, 138, 266, 522, 146, 530, 386, 770, 76, 268, 524, 100, 292, 548, 708, 772, 200, 328, 392, 648, 112, 176, 560, 208, 656, 224, 352, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_211, vertices_387, vertices_771, vertices_805, vertices_457, vertices_369, vertices_782, vertices_666, vertices_394, vertices_364, vertices_716, vertices_740, vertices_240, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_49, vertices_81, vertices_289, vertices_545, vertices_193, vertices_321, vertices_385, vertices_769, vertices_138, vertices_266, vertices_522, vertices_146, vertices_530, vertices_386, vertices_770, vertices_76, vertices_268, vertices_524, vertices_100, vertices_292, vertices_548, vertices_708, vertices_772, vertices_200, vertices_328, vertices_392, vertices_648, vertices_112, vertices_176, vertices_560, vertices_208, vertices_656, vertices_224, vertices_352, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_211), (false, vertices_387), (false, vertices_771), (false, vertices_805), (false, vertices_457), (false, vertices_369), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_100), (true, vertices_708), (true, vertices_648), (true, vertices_176), (true, vertices_656), (true, vertices_224), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 15 else
  if p.val = (false, vertices_211) then 16 else
  if p.val = (false, vertices_387) then 0 else
  if p.val = (false, vertices_771) then 1 else
  if p.val = (false, vertices_805) then 18 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (false, vertices_369) then 23 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_76) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_708) then 19 else
  if p.val = (true, vertices_648) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_656) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_672) then 13 else
  0
cert_priority
cert_nodeAtPriority_44 387 771 138 266 522 76 268 524 100 648 176 656 224 672 563 211 805 708 457 369
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 8 666 138 2
cert_row_2 1 1 5 6 8 708
cert_row_4 2 0 1 2 7 8 782 266 1
cert_row_4 3 1 2 4 5 7 364 76 2
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 2 0 1 2 7 266 782 1
cert_coverFacet 1 666
cert_cover_5 1 0 0 2 3 6 138 666 2
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 364
cert_cover_5 3 3 1 2 4 5 76 364 2
cert_coverFacet 4 716
cert_cover_5 4 1 1 2 5 6 76 716 3
cert_coverFacet 5 740
cert_cover_5 5 1 1 4 5 6 100 740 3
cert_coverFacet 6 240
cert_cover_2 6 4 3 5 6 112 240 3
cert_coverFacet 7 688
cert_cover_2 7 4 3 6 8 176 688 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0552

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e10q1_0553.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0553

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 285, 565, 357, 913, 833, 558, 654, 234, 962, 156, 300, 660, 472, 360, 21, 37, 261, 273, 529, 97, 545, 321, 577, 769, 526, 42, 138, 98, 546, 194, 578, 642, 28, 44, 140, 268, 148, 532, 292, 548, 644, 152, 280, 104, 296, 200, 328, 400, 656, 352, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_285, vertices_565, vertices_357, vertices_913, vertices_833, vertices_558, vertices_654, vertices_234, vertices_962, vertices_156, vertices_300, vertices_660, vertices_472, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_261, vertices_273, vertices_529, vertices_97, vertices_545, vertices_321, vertices_577, vertices_769, vertices_526, vertices_42, vertices_138, vertices_98, vertices_546, vertices_194, vertices_578, vertices_642, vertices_28, vertices_44, vertices_140, vertices_268, vertices_148, vertices_532, vertices_292, vertices_548, vertices_644, vertices_152, vertices_280, vertices_104, vertices_296, vertices_200, vertices_328, vertices_400, vertices_656, vertices_352, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_285), (false, vertices_565), (false, vertices_357), (false, vertices_913), (false, vertices_833), (true, vertices_526), (true, vertices_42), (true, vertices_138), (true, vertices_194), (true, vertices_642), (true, vertices_44), (true, vertices_140), (true, vertices_148), (true, vertices_644), (true, vertices_152), (true, vertices_104), (true, vertices_296), (true, vertices_200), (true, vertices_328), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 16 else
  if p.val = (false, vertices_285) then 19 else
  if p.val = (false, vertices_565) then 20 else
  if p.val = (false, vertices_357) then 21 else
  if p.val = (false, vertices_913) then 24 else
  if p.val = (false, vertices_833) then 0 else
  if p.val = (true, vertices_526) then 17 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_194) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_44) then 5 else
  if p.val = (true, vertices_140) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_200) then 12 else
  if p.val = (true, vertices_328) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
cert_nodeAtPriority_19 0 833 1 42 138 194 642 44 140 148 644 152 104 296 200 328 448 611 526 285 565 357 913
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 8 526
cert_row_4 1 0 2 4 5 6 234 42 3
cert_row_4 2 0 5 6 7 8 962 194 3
cert_row_4 3 2 3 5 6 7 472 152 2
cert_rows
cert_pivot_2 1 4 0 2
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 0 0 1 2 4 526 558 3
cert_coverFacet 1 654
cert_cover_5 1 0 0 1 2 6 526 654 3
cert_coverFacet 2 234
cert_cover_5 2 1 0 2 4 5 42 234 3
cert_coverFacet 3 962
cert_cover_5 3 2 0 5 6 7 194 962 3
cert_coverFacet 4 156
cert_cover_2 4 2 1 3 6 28 156 3
cert_coverFacet 5 300
cert_cover_2 5 2 1 4 7 44 300 3
cert_coverFacet 6 660
cert_cover_2 6 3 1 6 8 148 660 3
cert_coverFacet 7 472
cert_cover_5 7 3 2 3 5 6 152 472 2
cert_coverFacet 8 360
cert_cover_2 8 4 2 5 7 104 360 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0553

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_3123 : Certifies 3123 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0524.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3124 : Certifies 3124 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0525.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3125 : Certifies 3125 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0526.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3126 : Certifies 3126 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0527.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3127 : Certifies 3127 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0528.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3128 : Certifies 3128 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0529.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3129 : Certifies 3129 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0530.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3130 : Certifies 3130 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0531.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3131 : Certifies 3131 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0532.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3132 : Certifies 3132 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0533.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3133 : Certifies 3133 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0534.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3134 : Certifies 3134 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0535.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3135 : Certifies 3135 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0536.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3136 : Certifies 3136 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0537.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3137 : Certifies 3137 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0538.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3138 : Certifies 3138 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0539.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3139 : Certifies 3139 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0540.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3140 : Certifies 3140 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0541.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3141 : Certifies 3141 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0542.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3142 : Certifies 3142 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0543.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3143 : Certifies 3143 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0544.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3144 : Certifies 3144 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0545.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3145 : Certifies 3145 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0546.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3146 : Certifies 3146 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0547.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3147 : Certifies 3147 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0548.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3148 : Certifies 3148 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0549.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3149 : Certifies 3149 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0550.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3150 : Certifies 3150 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0551.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3151 : Certifies 3151 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0552.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3152 : Certifies 3152 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0553.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B103 (j : Fin 30) :
    Certifies (3123 + j.val) := by
  fin_cases j
  · exact projection_3123
  · exact projection_3124
  · exact projection_3125
  · exact projection_3126
  · exact projection_3127
  · exact projection_3128
  · exact projection_3129
  · exact projection_3130
  · exact projection_3131
  · exact projection_3132
  · exact projection_3133
  · exact projection_3134
  · exact projection_3135
  · exact projection_3136
  · exact projection_3137
  · exact projection_3138
  · exact projection_3139
  · exact projection_3140
  · exact projection_3141
  · exact projection_3142
  · exact projection_3143
  · exact projection_3144
  · exact projection_3145
  · exact projection_3146
  · exact projection_3147
  · exact projection_3148
  · exact projection_3149
  · exact projection_3150
  · exact projection_3151
  · exact projection_3152

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
