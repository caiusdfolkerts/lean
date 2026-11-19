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
/- Source: ProjectionCertificates/R_m14e10q1_0809.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0809

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 775, 181, 341, 841, 721, 174, 310, 362, 650, 778, 744, 240, 368, 519, 21, 133, 261, 81, 145, 321, 577, 641, 769, 38, 134, 262, 42, 138, 266, 522, 290, 642, 770, 52, 276, 164, 104, 168, 328, 584, 648, 776, 112, 176, 304, 208, 336, 224, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_775, vertices_181, vertices_341, vertices_841, vertices_721, vertices_174, vertices_310, vertices_362, vertices_650, vertices_778, vertices_744, vertices_240, vertices_368] (by decide +kernel)
  polygons := literalFinset [vertices_519, vertices_21, vertices_133, vertices_261, vertices_81, vertices_145, vertices_321, vertices_577, vertices_641, vertices_769, vertices_38, vertices_134, vertices_262, vertices_42, vertices_138, vertices_266, vertices_522, vertices_290, vertices_642, vertices_770, vertices_52, vertices_276, vertices_164, vertices_104, vertices_168, vertices_328, vertices_584, vertices_648, vertices_776, vertices_112, vertices_176, vertices_304, vertices_208, vertices_336, vertices_224, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_775), (false, vertices_181), (false, vertices_341), (false, vertices_841), (false, vertices_721), (true, vertices_38), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_290), (true, vertices_104), (true, vertices_168), (true, vertices_648), (true, vertices_112), (true, vertices_304), (true, vertices_224), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 14 else
  if p.val = (false, vertices_775) then 15 else
  if p.val = (false, vertices_181) then 17 else
  if p.val = (false, vertices_341) then 18 else
  if p.val = (false, vertices_841) then 20 else
  if p.val = (false, vertices_721) then 22 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_168) then 7 else
  if p.val = (true, vertices_648) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_224) then 11 else
  if p.val = (true, vertices_352) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 7 310 38 2
cert_row_4 1 0 1 2 4 6 174 38 2
cert_row_4 2 0 2 4 5 7 362 42 3
cert_row_4 3 2 4 5 6 8 744 104 3
cert_rows
cert_pivot_2 3 1 0 2
cert_heightProof 4
cert_coverFacet 0 174
cert_cover_5 0 1 0 1 2 4 38 174 2
cert_coverFacet 1 310
cert_cover_5 1 0 0 1 3 4 38 310 2
cert_coverFacet 2 362
cert_cover_5 2 2 0 2 4 5 42 362 3
cert_coverFacet 3 650
cert_cover_2 3 2 0 6 8 138 650 3
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 744
cert_cover_5 5 3 2 4 5 6 104 744 3
cert_coverFacet 6 240
cert_cover_2 6 4 3 5 6 112 240 3
cert_coverFacet 7 368
cert_cover_2 7 4 3 5 7 112 368 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0809

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m14e10q1_0810.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0810

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 535, 357, 709, 313, 625, 654, 454, 570, 282, 394, 424, 680, 992, 23, 69, 261, 517, 49, 273, 529, 97, 289, 577, 134, 262, 518, 26, 138, 266, 522, 274, 530, 386, 196, 324, 644, 56, 280, 168, 296, 552, 392, 648, 560, 352, 608, 416, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_535, vertices_357, vertices_709, vertices_313, vertices_625, vertices_654, vertices_454, vertices_570, vertices_282, vertices_394, vertices_424, vertices_680, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_69, vertices_261, vertices_517, vertices_49, vertices_273, vertices_529, vertices_97, vertices_289, vertices_577, vertices_134, vertices_262, vertices_518, vertices_26, vertices_138, vertices_266, vertices_522, vertices_274, vertices_530, vertices_386, vertices_196, vertices_324, vertices_644, vertices_56, vertices_280, vertices_168, vertices_296, vertices_552, vertices_392, vertices_648, vertices_560, vertices_352, vertices_608, vertices_416, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_535), (false, vertices_357), (false, vertices_709), (false, vertices_313), (false, vertices_625), (true, vertices_134), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_386), (true, vertices_168), (true, vertices_552), (true, vertices_392), (true, vertices_648), (true, vertices_416), (true, vertices_672), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 14 else
  if p.val = (false, vertices_535) then 15 else
  if p.val = (false, vertices_357) then 17 else
  if p.val = (false, vertices_709) then 18 else
  if p.val = (false, vertices_313) then 20 else
  if p.val = (false, vertices_625) then 22 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_392) then 8 else
  if p.val = (true, vertices_648) then 9 else
  if p.val = (true, vertices_416) then 10 else
  if p.val = (true, vertices_672) then 11 else
  if p.val = (true, vertices_448) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_279), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 8 570 26 3
cert_row_4 1 0 1 2 6 8 654 134 2
cert_row_4 2 0 1 5 6 7 454 134 2
cert_row_4 3 4 5 6 7 8 992 352 2
cert_rows
cert_pivot_2 3 2 0 4
cert_heightProof 4
cert_coverFacet 0 654
cert_cover_5 0 1 0 1 2 6 134 654 2
cert_coverFacet 1 454
cert_cover_5 1 2 0 1 5 6 134 454 2
cert_coverFacet 2 570
cert_cover_5 2 0 0 2 3 4 26 570 3
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 424
cert_cover_2 5 4 2 6 7 168 424 3
cert_coverFacet 6 680
cert_cover_2 6 4 2 6 8 168 680 3
cert_coverFacet 7 992
cert_cover_5 7 3 4 5 6 7 352 992 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0810

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m14e10q1_0812.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0812

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 397, 341, 709, 785, 929, 334, 590, 570, 426, 306, 338, 684, 816, 69, 133, 261, 81, 273, 529, 577, 385, 641, 769, 78, 42, 266, 522, 50, 82, 274, 530, 290, 322, 578, 140, 268, 524, 324, 580, 644, 168, 552, 392, 304, 560, 336, 784, 416, 672, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_397, vertices_341, vertices_709, vertices_785, vertices_929, vertices_334, vertices_590, vertices_570, vertices_426, vertices_306, vertices_338, vertices_684, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_81, vertices_273, vertices_529, vertices_577, vertices_385, vertices_641, vertices_769, vertices_78, vertices_42, vertices_266, vertices_522, vertices_50, vertices_82, vertices_274, vertices_530, vertices_290, vertices_322, vertices_578, vertices_140, vertices_268, vertices_524, vertices_324, vertices_580, vertices_644, vertices_168, vertices_552, vertices_392, vertices_304, vertices_560, vertices_336, vertices_784, vertices_416, vertices_672, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_397), (false, vertices_341), (false, vertices_709), (false, vertices_785), (false, vertices_929), (true, vertices_78), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_274), (true, vertices_290), (true, vertices_322), (true, vertices_524), (true, vertices_168), (true, vertices_552), (true, vertices_304), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 20 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 14 else
  if p.val = (false, vertices_397) then 17 else
  if p.val = (false, vertices_341) then 18 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_785) then 0 else
  if p.val = (false, vertices_929) then 23 else
  if p.val = (true, vertices_78) then 15 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_304) then 11 else
  if p.val = (true, vertices_560) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_785), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_78), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 2 3 4 8 570 42 2
cert_row_4 2 0 2 4 6 7 426 42 3
cert_row_4 3 1 2 4 6 8 684 140 2
cert_rows
cert_pivot_2 5 3 0 1
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 7 78 334 3
cert_coverFacet 1 590
cert_cover_5 1 0 0 1 2 8 78 590 3
cert_coverFacet 2 570
cert_cover_5 2 1 0 2 3 4 42 570 2
cert_coverFacet 3 426
cert_cover_5 3 2 0 2 4 6 42 426 3
cert_coverFacet 4 306
cert_cover_2 4 3 0 4 7 50 306 3
cert_coverFacet 5 338
cert_cover_2 5 3 0 5 7 82 338 3
cert_coverFacet 6 684
cert_cover_5 6 3 1 2 4 6 140 684 2
cert_coverFacet 7 816
cert_cover_2 7 4 3 7 8 304 816 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0812

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m14e10q1_0814.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0814

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [171, 301, 205, 341, 929, 961, 142, 270, 150, 278, 810, 690, 850, 724, 13, 69, 261, 41, 137, 161, 289, 193, 321, 897, 14, 22, 134, 262, 42, 138, 266, 146, 274, 530, 162, 546, 770, 140, 268, 84, 148, 276, 196, 296, 336, 592, 656, 672, 800, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_171, vertices_301, vertices_205, vertices_341, vertices_929, vertices_961, vertices_142, vertices_270, vertices_150, vertices_278, vertices_810, vertices_690, vertices_850, vertices_724] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_69, vertices_261, vertices_41, vertices_137, vertices_161, vertices_289, vertices_193, vertices_321, vertices_897, vertices_14, vertices_22, vertices_134, vertices_262, vertices_42, vertices_138, vertices_266, vertices_146, vertices_274, vertices_530, vertices_162, vertices_546, vertices_770, vertices_140, vertices_268, vertices_84, vertices_148, vertices_276, vertices_196, vertices_296, vertices_336, vertices_592, vertices_656, vertices_672, vertices_800, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_171), (false, vertices_301), (false, vertices_205), (false, vertices_341), (false, vertices_929), (false, vertices_961), (true, vertices_14), (true, vertices_22), (true, vertices_134), (true, vertices_262), (true, vertices_266), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_546), (true, vertices_770), (true, vertices_148), (true, vertices_592), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 15 19 20 21 22 23 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_171) then 14 else
  if p.val = (false, vertices_301) then 16 else
  if p.val = (false, vertices_205) then 17 else
  if p.val = (false, vertices_341) then 18 else
  if p.val = (false, vertices_929) then 24 else
  if p.val = (false, vertices_961) then 25 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_770) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_656) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_171), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_205), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inl 5
  | 23 => Sum.inl 6
  | 24 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 7 8 810 42 3
cert_row_4 1 0 3 4 6 8 690 146 2
cert_row_4 2 0 3 5 7 8 850 274 2
cert_row_4 3 1 3 5 6 8 724 84 3
cert_rows
cert_pivot_2 2 4 0 1
cert_heightProof 4
cert_coverFacet 0 142
cert_cover_2 0 1 0 2 6 14 142 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 150
cert_cover_2 2 1 0 3 6 22 150 3
cert_coverFacet 3 278
cert_cover_2 3 1 0 3 7 22 278 3
cert_coverFacet 4 810
cert_cover_5 4 0 0 2 4 7 42 810 3
cert_coverFacet 5 690
cert_cover_5 5 1 0 3 4 6 146 690 2
cert_coverFacet 6 850
cert_cover_5 6 2 0 3 5 7 274 850 2
cert_coverFacet 7 724
cert_cover_5 7 3 1 3 5 6 84 724 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0814

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m14e10q1_0815.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0815

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [583, 647, 93, 405, 665, 617, 342, 422, 682, 866, 344, 408, 360, 424, 519, 21, 69, 133, 25, 73, 521, 145, 577, 641, 70, 134, 262, 162, 290, 546, 322, 578, 642, 84, 276, 388, 88, 152, 280, 104, 168, 296, 552, 328, 392, 648, 336, 400, 352, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_583, vertices_647, vertices_93, vertices_405, vertices_665, vertices_617, vertices_342, vertices_422, vertices_682, vertices_866, vertices_344, vertices_408, vertices_360, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_519, vertices_21, vertices_69, vertices_133, vertices_25, vertices_73, vertices_521, vertices_145, vertices_577, vertices_641, vertices_70, vertices_134, vertices_262, vertices_162, vertices_290, vertices_546, vertices_322, vertices_578, vertices_642, vertices_84, vertices_276, vertices_388, vertices_88, vertices_152, vertices_280, vertices_104, vertices_168, vertices_296, vertices_552, vertices_328, vertices_392, vertices_648, vertices_336, vertices_400, vertices_352, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_583), (false, vertices_647), (false, vertices_93), (false, vertices_405), (false, vertices_665), (false, vertices_617), (true, vertices_262), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_322), (true, vertices_280), (true, vertices_168), (true, vertices_296), (true, vertices_328), (true, vertices_392), (true, vertices_336), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_583) then 14 else
  if p.val = (false, vertices_647) then 15 else
  if p.val = (false, vertices_93) then 17 else
  if p.val = (false, vertices_405) then 18 else
  if p.val = (false, vertices_665) then 20 else
  if p.val = (false, vertices_617) then 21 else
  if p.val = (true, vertices_262) then 0 else
  if p.val = (true, vertices_162) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_328) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_416) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_93), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_617), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 7 342 70 2
cert_row_4 1 0 1 4 6 7 422 134 2
cert_row_4 2 0 2 4 6 8 682 162 1
cert_row_4 3 0 4 5 7 8 866 290 2
cert_rows
cert_pivot_2 3 1 2 0
cert_heightProof 4
cert_coverFacet 0 342
cert_cover_5 0 0 0 1 3 5 70 342 2
cert_coverFacet 1 422
cert_cover_5 1 1 0 1 4 6 134 422 2
cert_coverFacet 2 682
cert_cover_5 2 2 0 2 4 6 162 682 1
cert_coverFacet 3 866
cert_cover_5 3 3 0 4 5 7 290 866 2
cert_coverFacet 4 344
cert_cover_2 4 3 2 5 7 88 344 3
cert_coverFacet 5 408
cert_cover_2 5 3 2 6 7 152 408 3
cert_coverFacet 6 360
cert_cover_2 6 4 2 5 7 104 360 3
cert_coverFacet 7 424
cert_cover_2 7 4 2 6 7 168 424 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0815

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m14e10q1_0816.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0816

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 775, 157, 341, 721, 865, 286, 174, 810, 738, 408, 424, 464, 480, 519, 21, 133, 261, 81, 145, 321, 577, 641, 769, 14, 134, 262, 42, 266, 162, 546, 642, 770, 28, 140, 276, 152, 280, 168, 296, 392, 208, 336, 400, 224, 352, 608, 416, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_775, vertices_157, vertices_341, vertices_721, vertices_865, vertices_286, vertices_174, vertices_810, vertices_738, vertices_408, vertices_424, vertices_464, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_519, vertices_21, vertices_133, vertices_261, vertices_81, vertices_145, vertices_321, vertices_577, vertices_641, vertices_769, vertices_14, vertices_134, vertices_262, vertices_42, vertices_266, vertices_162, vertices_546, vertices_642, vertices_770, vertices_28, vertices_140, vertices_276, vertices_152, vertices_280, vertices_168, vertices_296, vertices_392, vertices_208, vertices_336, vertices_400, vertices_224, vertices_352, vertices_608, vertices_416, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_775), (false, vertices_157), (false, vertices_341), (false, vertices_721), (false, vertices_865), (true, vertices_14), (true, vertices_42), (true, vertices_266), (true, vertices_162), (true, vertices_546), (true, vertices_280), (true, vertices_168), (true, vertices_296), (true, vertices_392), (true, vertices_400), (true, vertices_224), (true, vertices_416), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 16 19 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 14 else
  if p.val = (false, vertices_775) then 15 else
  if p.val = (false, vertices_157) then 17 else
  if p.val = (false, vertices_341) then 18 else
  if p.val = (false, vertices_721) then 21 else
  if p.val = (false, vertices_865) then 23 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_546) then 4 else
  if p.val = (true, vertices_280) then 5 else
  if p.val = (true, vertices_168) then 6 else
  if p.val = (true, vertices_296) then 7 else
  if p.val = (true, vertices_392) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_416) then 11 else
  if p.val = (true, vertices_448) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 7 286 14 3
cert_row_4 1 0 1 2 4 6 174 14 3
cert_row_4 2 0 2 4 7 8 810 42 3
cert_row_4 3 0 4 5 6 8 738 162 2
cert_rows
cert_pivot_2 3 1 2 0
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 3 14 286 3
cert_coverFacet 1 174
cert_cover_5 1 1 0 1 2 4 14 174 3
cert_coverFacet 2 810
cert_cover_5 2 2 0 2 4 7 42 810 3
cert_coverFacet 3 738
cert_cover_5 3 3 0 4 5 6 162 738 2
cert_coverFacet 4 408
cert_cover_2 4 3 2 6 7 152 408 3
cert_coverFacet 5 424
cert_cover_2 5 4 2 6 7 168 424 3
cert_coverFacet 6 464
cert_cover_2 6 5 3 6 7 208 464 3
cert_coverFacet 7 480
cert_cover_2 7 5 4 6 7 224 480 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0816

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m14e11q2_0018.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0018

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [535, 333, 589, 405, 689, 961, 62, 526, 362, 586, 562, 738, 316, 496, 77, 21, 261, 517, 145, 529, 321, 577, 385, 641, 14, 22, 518, 42, 74, 522, 50, 530, 98, 546, 578, 60, 268, 524, 276, 296, 328, 584, 176, 304, 560, 400, 224, 352, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_535, vertices_333, vertices_589, vertices_405, vertices_689, vertices_961, vertices_62, vertices_526, vertices_362, vertices_586, vertices_562, vertices_738, vertices_316, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_77, vertices_21, vertices_261, vertices_517, vertices_145, vertices_529, vertices_321, vertices_577, vertices_385, vertices_641, vertices_14, vertices_22, vertices_518, vertices_42, vertices_74, vertices_522, vertices_50, vertices_530, vertices_98, vertices_546, vertices_578, vertices_60, vertices_268, vertices_524, vertices_276, vertices_296, vertices_328, vertices_584, vertices_176, vertices_304, vertices_560, vertices_400, vertices_224, vertices_352, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_535), (false, vertices_333), (false, vertices_589), (false, vertices_405), (false, vertices_689), (false, vertices_961), (true, vertices_14), (true, vertices_42), (true, vertices_74), (true, vertices_522), (true, vertices_50), (true, vertices_98), (true, vertices_546), (true, vertices_578), (true, vertices_60), (true, vertices_296), (true, vertices_304), (true, vertices_224), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 18 21 14 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_535) then 13 else
  if p.val = (false, vertices_333) then 19 else
  if p.val = (false, vertices_589) then 20 else
  if p.val = (false, vertices_405) then 15 else
  if p.val = (false, vertices_689) then 16 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_60) then 17 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_224) then 10 else
  if p.val = (true, vertices_352) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_60), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 4 60
cert_row_4 1 0 2 4 5 7 362 42 3
cert_row_4 2 0 4 5 6 8 738 98 3
cert_row_4 3 3 4 5 6 7 496 176 2
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 62
cert_cover_5 0 0 0 1 2 3 14 62 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 362
cert_cover_5 2 1 0 2 4 5 42 362 3
cert_coverFacet 3 586
cert_cover_2 3 2 0 5 8 74 586 3
cert_coverFacet 4 562
cert_cover_2 4 3 0 4 8 50 562 3
cert_coverFacet 5 738
cert_cover_5 5 2 0 4 5 6 98 738 3
cert_coverFacet 6 316
cert_cover_5 6 0 1 2 3 7 60 316 3
cert_coverFacet 7 496
cert_cover_5 7 3 3 4 5 6 176 496 2
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0018

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m14e11q2_0019.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0019

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [611, 301, 557, 405, 709, 481, 662, 218, 538, 362, 554, 706, 796, 472, 45, 133, 261, 517, 97, 289, 545, 193, 577, 385, 26, 42, 74, 522, 146, 530, 98, 546, 194, 578, 642, 268, 524, 148, 276, 532, 644, 216, 280, 536, 296, 552, 328, 400, 352, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_611, vertices_301, vertices_557, vertices_405, vertices_709, vertices_481, vertices_662, vertices_218, vertices_538, vertices_362, vertices_554, vertices_706, vertices_796, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_45, vertices_133, vertices_261, vertices_517, vertices_97, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_26, vertices_42, vertices_74, vertices_522, vertices_146, vertices_530, vertices_98, vertices_546, vertices_194, vertices_578, vertices_642, vertices_268, vertices_524, vertices_148, vertices_276, vertices_532, vertices_644, vertices_216, vertices_280, vertices_536, vertices_296, vertices_552, vertices_328, vertices_400, vertices_352, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_611), (false, vertices_301), (false, vertices_557), (false, vertices_405), (false, vertices_709), (false, vertices_481), (true, vertices_26), (true, vertices_42), (true, vertices_74), (true, vertices_522), (true, vertices_146), (true, vertices_530), (true, vertices_194), (true, vertices_642), (true, vertices_532), (true, vertices_216), (true, vertices_280), (true, vertices_536), (true, vertices_328)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 17 21 14 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_611) then 13 else
  if p.val = (false, vertices_301) then 18 else
  if p.val = (false, vertices_557) then 19 else
  if p.val = (false, vertices_405) then 15 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_216) then 16 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_328) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_216), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 5 7 362 42 3
cert_row_2 1 2 3 5 6 216
cert_row_4 2 0 1 3 6 8 662 146 1
cert_row_4 3 1 2 3 7 8 796 268 2
cert_rows
cert_pivot_2 4 5 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 2 0 1 3 6 146 662 1
cert_coverFacet 1 218
cert_cover_5 1 1 0 2 3 5 26 218 3
cert_coverFacet 2 538
cert_cover_2 2 2 0 3 8 26 538 3
cert_coverFacet 3 362
cert_cover_5 3 0 0 2 4 5 42 362 3
cert_coverFacet 4 554
cert_cover_2 4 2 0 4 8 42 554 3
cert_coverFacet 5 706
cert_cover_2 5 5 0 6 8 194 706 3
cert_coverFacet 6 796
cert_cover_5 6 3 1 2 3 7 268 796 2
cert_coverFacet 7 472
cert_cover_5 7 1 2 3 5 7 216 472 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0019

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m14e11q2_0021.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0021

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [355, 803, 789, 677, 453, 233, 542, 90, 106, 682, 850, 412, 652, 472, 291, 133, 261, 517, 97, 161, 545, 193, 321, 769, 26, 42, 74, 522, 82, 530, 98, 546, 322, 770, 28, 140, 524, 276, 532, 388, 644, 88, 408, 104, 168, 200, 648, 336, 784, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_355, vertices_803, vertices_789, vertices_677, vertices_453, vertices_233, vertices_542, vertices_90, vertices_106, vertices_682, vertices_850, vertices_412, vertices_652, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_291, vertices_133, vertices_261, vertices_517, vertices_97, vertices_161, vertices_545, vertices_193, vertices_321, vertices_769, vertices_26, vertices_42, vertices_74, vertices_522, vertices_82, vertices_530, vertices_98, vertices_546, vertices_322, vertices_770, vertices_28, vertices_140, vertices_524, vertices_276, vertices_532, vertices_388, vertices_644, vertices_88, vertices_408, vertices_104, vertices_168, vertices_200, vertices_648, vertices_336, vertices_784, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_355), (false, vertices_803), (false, vertices_789), (false, vertices_677), (false, vertices_453), (false, vertices_233), (true, vertices_26), (true, vertices_42), (true, vertices_74), (true, vertices_522), (true, vertices_82), (true, vertices_530), (true, vertices_28), (true, vertices_140), (true, vertices_524), (true, vertices_88), (true, vertices_408), (true, vertices_648), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 19 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_355) then 13 else
  if p.val = (false, vertices_803) then 14 else
  if p.val = (false, vertices_789) then 16 else
  if p.val = (false, vertices_677) then 17 else
  if p.val = (false, vertices_453) then 18 else
  if p.val = (false, vertices_233) then 20 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_408) then 21 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_336) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 8 542 26 1
cert_row_4 1 0 2 4 6 8 682 42 3
cert_row_2 2 2 3 6 7 408
cert_row_4 3 0 3 5 7 8 850 82 3
cert_rows
cert_pivot_2 1 4 2 0
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 26 542 1
cert_coverFacet 1 90
cert_cover_2 1 2 0 3 5 26 90 3
cert_coverFacet 2 106
cert_cover_2 2 2 0 4 5 42 106 3
cert_coverFacet 3 682
cert_cover_5 3 1 0 2 4 6 42 682 3
cert_coverFacet 4 850
cert_cover_5 4 3 0 3 5 7 82 850 3
cert_coverFacet 5 412
cert_cover_5 5 2 1 2 3 6 28 412 3
cert_coverFacet 6 652
cert_cover_2 6 2 1 6 8 140 652 3
cert_coverFacet 7 472
cert_cover_5 7 2 2 3 5 6 88 472 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0021

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m14e11q2_0022.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0022

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 781, 405, 677, 713, 465, 566, 794, 234, 682, 114, 338, 244, 788, 133, 261, 517, 73, 265, 521, 401, 193, 321, 641, 170, 74, 266, 522, 50, 82, 274, 530, 98, 546, 322, 52, 148, 276, 532, 164, 548, 772, 200, 648, 776, 112, 208, 336, 784, 224, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_781, vertices_405, vertices_677, vertices_713, vertices_465, vertices_566, vertices_794, vertices_234, vertices_682, vertices_114, vertices_338, vertices_244, vertices_788] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_73, vertices_265, vertices_521, vertices_401, vertices_193, vertices_321, vertices_641, vertices_170, vertices_74, vertices_266, vertices_522, vertices_50, vertices_82, vertices_274, vertices_530, vertices_98, vertices_546, vertices_322, vertices_52, vertices_148, vertices_276, vertices_532, vertices_164, vertices_548, vertices_772, vertices_200, vertices_648, vertices_776, vertices_112, vertices_208, vertices_336, vertices_784, vertices_224, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_781), (false, vertices_405), (false, vertices_677), (false, vertices_713), (false, vertices_465), (true, vertices_170), (true, vertices_522), (true, vertices_50), (true, vertices_82), (true, vertices_274), (true, vertices_530), (true, vertices_98), (true, vertices_546), (true, vertices_52), (true, vertices_532), (true, vertices_112), (true, vertices_784), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 13 else
  if p.val = (false, vertices_781) then 16 else
  if p.val = (false, vertices_405) then 21 else
  if p.val = (false, vertices_677) then 17 else
  if p.val = (false, vertices_713) then 19 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (true, vertices_170) then 14 else
  if p.val = (true, vertices_522) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_784) then 10 else
  if p.val = (true, vertices_224) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_170), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 7 8 794 266 2
cert_row_2 1 0 2 4 6 170
cert_row_4 2 0 1 3 4 8 566 50 1
cert_row_4 3 1 3 4 5 6 244 52 3
cert_rows
cert_pivot_2 7 2 0 1
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 2 0 1 3 4 50 566 1
cert_coverFacet 1 794
cert_cover_5 1 0 0 2 3 7 266 794 2
cert_coverFacet 2 234
cert_cover_5 2 1 0 2 4 5 170 234 3
cert_coverFacet 3 682
cert_cover_5 3 1 0 2 4 8 170 682 3
cert_coverFacet 4 114
cert_cover_2 4 3 0 4 5 50 114 3
cert_coverFacet 5 338
cert_cover_2 5 3 0 5 7 82 338 3
cert_coverFacet 6 244
cert_cover_5 6 3 1 3 4 5 52 244 3
cert_coverFacet 7 788
cert_cover_2 7 3 1 7 8 276 788 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0022

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m14e11q2_0031.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0031

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [271, 59, 403, 45, 677, 901, 241, 218, 458, 60, 92, 844, 628, 992, 11, 19, 259, 13, 37, 645, 261, 41, 49, 145, 161, 385, 26, 202, 266, 146, 386, 28, 44, 76, 268, 52, 84, 548, 580, 772, 56, 88, 328, 112, 208, 224, 608, 672, 448, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_271, vertices_59, vertices_403, vertices_45, vertices_677, vertices_901, vertices_241, vertices_218, vertices_458, vertices_60, vertices_92, vertices_844, vertices_628, vertices_992] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_259, vertices_13, vertices_37, vertices_645, vertices_261, vertices_41, vertices_49, vertices_145, vertices_161, vertices_385, vertices_26, vertices_202, vertices_266, vertices_146, vertices_386, vertices_28, vertices_44, vertices_76, vertices_268, vertices_52, vertices_84, vertices_548, vertices_580, vertices_772, vertices_56, vertices_88, vertices_328, vertices_112, vertices_208, vertices_224, vertices_608, vertices_672, vertices_448, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_271), (false, vertices_59), (false, vertices_403), (false, vertices_45), (false, vertices_677), (false, vertices_901), (false, vertices_241), (true, vertices_202), (true, vertices_28), (true, vertices_76), (true, vertices_52), (true, vertices_84), (true, vertices_580), (true, vertices_88), (true, vertices_328), (true, vertices_608), (true, vertices_448), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 11 19 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_271) then 12 else
  if p.val = (false, vertices_59) then 16 else
  if p.val = (false, vertices_403) then 17 else
  if p.val = (false, vertices_45) then 0 else
  if p.val = (false, vertices_677) then 13 else
  if p.val = (false, vertices_901) then 14 else
  if p.val = (false, vertices_241) then 21 else
  if p.val = (true, vertices_202) then 18 else
  if p.val = (true, vertices_28) then 1 else
  if p.val = (true, vertices_76) then 2 else
  if p.val = (true, vertices_52) then 3 else
  if p.val = (true, vertices_84) then 4 else
  if p.val = (true, vertices_580) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_328) then 7 else
  if p.val = (true, vertices_608) then 8 else
  if p.val = (true, vertices_448) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_45), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_271), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_59), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_202), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 6 202
cert_row_4 1 1 2 5 7 8 844 76 3
cert_row_4 2 1 3 4 5 8 628 52 3
cert_row_4 3 4 5 6 7 8 992 224 3
cert_rows
cert_pivot_2 0 2 1 4
cert_heightProof 4
cert_coverFacet 0 218
cert_cover_5 0 0 0 2 3 5 26 218 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 7 202 458 3
cert_coverFacet 2 60
cert_cover_2 2 2 1 3 4 28 60 3
cert_coverFacet 3 92
cert_cover_2 3 2 1 3 5 28 92 3
cert_coverFacet 4 844
cert_cover_5 4 1 1 2 5 7 76 844 3
cert_coverFacet 5 628
cert_cover_5 5 2 1 3 4 5 52 628 3
cert_coverFacet 6 992
cert_cover_5 6 3 4 5 6 7 224 992 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0031

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m14e11q2_0035.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0035

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [103, 583, 787, 419, 905, 737, 542, 54, 306, 348, 716, 372, 792, 488, 71, 35, 259, 515, 97, 161, 577, 385, 641, 769, 22, 38, 518, 50, 274, 530, 290, 28, 76, 524, 52, 340, 100, 580, 280, 536, 200, 328, 392, 648, 776, 304, 784, 224, 352, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_103, vertices_583, vertices_787, vertices_419, vertices_905, vertices_737, vertices_542, vertices_54, vertices_306, vertices_348, vertices_716, vertices_372, vertices_792, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_71, vertices_35, vertices_259, vertices_515, vertices_97, vertices_161, vertices_577, vertices_385, vertices_641, vertices_769, vertices_22, vertices_38, vertices_518, vertices_50, vertices_274, vertices_530, vertices_290, vertices_28, vertices_76, vertices_524, vertices_52, vertices_340, vertices_100, vertices_580, vertices_280, vertices_536, vertices_200, vertices_328, vertices_392, vertices_648, vertices_776, vertices_304, vertices_784, vertices_224, vertices_352, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_103), (false, vertices_583), (false, vertices_787), (false, vertices_419), (false, vertices_905), (false, vertices_737), (true, vertices_22), (true, vertices_50), (true, vertices_28), (true, vertices_76), (true, vertices_524), (true, vertices_52), (true, vertices_340), (true, vertices_280), (true, vertices_536), (true, vertices_200), (true, vertices_328), (true, vertices_304), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 12 14 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_103) then 18 else
  if p.val = (false, vertices_583) then 19 else
  if p.val = (false, vertices_787) then 15 else
  if p.val = (false, vertices_419) then 20 else
  if p.val = (false, vertices_905) then 13 else
  if p.val = (false, vertices_737) then 23 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_52) then 5 else
  if p.val = (true, vertices_340) then 16 else
  if p.val = (true, vertices_280) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_328) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_352) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inl 2
  | 13 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_340), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_103), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 8 542 22 2
cert_row_2 1 1 3 5 7 340
cert_row_4 2 1 2 5 6 8 716 76 3
cert_row_4 3 2 4 5 6 7 488 200 1
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 22 542 2
cert_coverFacet 1 54
cert_cover_2 1 1 0 3 4 22 54 3
cert_coverFacet 2 306
cert_cover_2 2 3 0 4 7 50 306 3
cert_coverFacet 3 348
cert_cover_5 3 1 1 2 3 5 28 348 3
cert_coverFacet 4 716
cert_cover_5 4 2 1 2 5 6 76 716 3
cert_coverFacet 5 372
cert_cover_5 5 1 1 3 4 5 52 372 3
cert_coverFacet 6 792
cert_cover_2 6 3 2 7 8 280 792 3
cert_coverFacet 7 488
cert_cover_5 7 3 2 4 5 6 200 488 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0035

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m14e11q2_0046.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0046

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [107, 301, 805, 457, 913, 737, 30, 46, 214, 230, 346, 796, 692, 464, 293, 41, 73, 265, 97, 545, 193, 385, 641, 769, 14, 22, 38, 198, 26, 42, 74, 82, 98, 28, 44, 268, 148, 532, 164, 548, 772, 280, 328, 208, 336, 400, 656, 784, 224, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_107, vertices_301, vertices_805, vertices_457, vertices_913, vertices_737, vertices_30, vertices_46, vertices_214, vertices_230, vertices_346, vertices_796, vertices_692, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_293, vertices_41, vertices_73, vertices_265, vertices_97, vertices_545, vertices_193, vertices_385, vertices_641, vertices_769, vertices_14, vertices_22, vertices_38, vertices_198, vertices_26, vertices_42, vertices_74, vertices_82, vertices_98, vertices_28, vertices_44, vertices_268, vertices_148, vertices_532, vertices_164, vertices_548, vertices_772, vertices_280, vertices_328, vertices_208, vertices_336, vertices_400, vertices_656, vertices_784, vertices_224, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_107), (false, vertices_301), (false, vertices_805), (false, vertices_457), (false, vertices_913), (false, vertices_737), (true, vertices_14), (true, vertices_22), (true, vertices_38), (true, vertices_198), (true, vertices_26), (true, vertices_82), (true, vertices_28), (true, vertices_148), (true, vertices_532), (true, vertices_164), (true, vertices_280), (true, vertices_208), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_107) then 13 else
  if p.val = (false, vertices_301) then 16 else
  if p.val = (false, vertices_805) then 17 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (false, vertices_913) then 21 else
  if p.val = (false, vertices_737) then 23 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_198) then 14 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_336) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_107), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_198), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_913), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 3 4 6 8 692 148 2
cert_row_2 1 0 1 5 6 198
cert_row_4 2 0 2 3 5 7 346 26 3
cert_row_4 3 1 2 3 7 8 796 28 3
cert_rows
cert_pivot_2 4 6 0 1
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 46
cert_cover_2 1 1 0 2 4 14 46 3
cert_coverFacet 2 214
cert_cover_5 2 1 0 1 3 5 22 214 3
cert_coverFacet 3 230
cert_cover_5 3 1 0 1 4 5 38 230 3
cert_coverFacet 4 346
cert_cover_5 4 2 0 2 3 5 26 346 3
cert_coverFacet 5 796
cert_cover_5 5 3 1 2 3 7 28 796 3
cert_coverFacet 6 692
cert_cover_5 6 0 1 3 4 6 148 692 2
cert_coverFacet 7 464
cert_cover_2 7 5 3 6 7 208 464 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0046

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m14e11q2_0052.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0052

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [15, 199, 539, 403, 333, 793, 481, 526, 182, 566, 236, 556, 872, 944, 7, 11, 19, 131, 13, 69, 537, 265, 273, 193, 321, 385, 14, 54, 134, 518, 522, 146, 530, 44, 76, 524, 164, 548, 196, 104, 552, 328, 776, 176, 560, 400, 784, 224, 352, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_15, vertices_199, vertices_539, vertices_403, vertices_333, vertices_793, vertices_481, vertices_526, vertices_182, vertices_566, vertices_236, vertices_556, vertices_872, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_11, vertices_19, vertices_131, vertices_13, vertices_69, vertices_537, vertices_265, vertices_273, vertices_193, vertices_321, vertices_385, vertices_14, vertices_54, vertices_134, vertices_518, vertices_522, vertices_146, vertices_530, vertices_44, vertices_76, vertices_524, vertices_164, vertices_548, vertices_196, vertices_104, vertices_552, vertices_328, vertices_776, vertices_176, vertices_560, vertices_400, vertices_784, vertices_224, vertices_352, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_15), (false, vertices_199), (false, vertices_539), (false, vertices_403), (false, vertices_333), (false, vertices_793), (false, vertices_481), (true, vertices_54), (true, vertices_518), (true, vertices_44), (true, vertices_524), (true, vertices_164), (true, vertices_548), (true, vertices_104), (true, vertices_552), (true, vertices_176), (true, vertices_560), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 11 17 20 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_15) then 0 else
  if p.val = (false, vertices_199) then 12 else
  if p.val = (false, vertices_539) then 18 else
  if p.val = (false, vertices_403) then 16 else
  if p.val = (false, vertices_333) then 13 else
  if p.val = (false, vertices_793) then 19 else
  if p.val = (false, vertices_481) then 22 else
  if p.val = (true, vertices_54) then 14 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_44) then 2 else
  if p.val = (true, vertices_524) then 3 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_548) then 5 else
  if p.val = (true, vertices_104) then 6 else
  if p.val = (true, vertices_552) then 7 else
  if p.val = (true, vertices_176) then 8 else
  if p.val = (true, vertices_560) then 9 else
  if p.val = (true, vertices_800) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_15), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_199), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_54), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 4 54
cert_row_4 1 1 2 4 5 6 236 44 3
cert_row_4 2 2 4 5 7 8 872 104 3
cert_row_4 3 3 4 6 7 8 944 176 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 182
cert_cover_5 1 0 0 1 3 6 54 182 3
cert_coverFacet 2 566
cert_cover_5 2 0 0 1 3 8 54 566 3
cert_coverFacet 3 236
cert_cover_5 3 1 1 2 4 5 44 236 3
cert_coverFacet 4 556
cert_cover_2 4 2 1 4 8 44 556 3
cert_coverFacet 5 872
cert_cover_5 5 2 2 4 5 7 104 872 3
cert_coverFacet 6 944
cert_cover_5 6 3 3 4 6 7 176 944 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0052

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m14e11q2_0055.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0055

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [307, 901, 713, 625, 465, 801, 30, 654, 278, 806, 122, 618, 348, 460, 49, 81, 273, 289, 545, 193, 577, 385, 641, 769, 14, 22, 262, 518, 26, 106, 522, 50, 274, 290, 546, 28, 332, 140, 276, 388, 644, 772, 88, 200, 584, 648, 112, 336, 608, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_901, vertices_713, vertices_625, vertices_465, vertices_801, vertices_30, vertices_654, vertices_278, vertices_806, vertices_122, vertices_618, vertices_348, vertices_460] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_81, vertices_273, vertices_289, vertices_545, vertices_193, vertices_577, vertices_385, vertices_641, vertices_769, vertices_14, vertices_22, vertices_262, vertices_518, vertices_26, vertices_106, vertices_522, vertices_50, vertices_274, vertices_290, vertices_546, vertices_28, vertices_332, vertices_140, vertices_276, vertices_388, vertices_644, vertices_772, vertices_88, vertices_200, vertices_584, vertices_648, vertices_112, vertices_336, vertices_608, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_901), (false, vertices_713), (false, vertices_625), (false, vertices_465), (false, vertices_801), (true, vertices_14), (true, vertices_22), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_106), (true, vertices_522), (true, vertices_546), (true, vertices_28), (true, vertices_332), (true, vertices_140), (true, vertices_276), (true, vertices_88)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 13 else
  if p.val = (false, vertices_901) then 16 else
  if p.val = (false, vertices_713) then 19 else
  if p.val = (false, vertices_625) then 21 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (false, vertices_801) then 0 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_26) then 5 else
  if p.val = (true, vertices_106) then 14 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_332) then 17 else
  if p.val = (true, vertices_140) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_88) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_801), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_106), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_332), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 8 654 14 3
cert_row_4 1 0 1 4 7 8 806 262 2
cert_row_2 2 0 2 4 5 106
cert_row_2 3 1 2 5 7 332
cert_rows
cert_pivot_2 6 8 0 1
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 654
cert_cover_5 1 0 0 1 2 6 14 654 3
cert_coverFacet 2 278
cert_cover_2 2 1 0 3 7 22 278 3
cert_coverFacet 3 806
cert_cover_5 3 1 0 1 4 7 262 806 2
cert_coverFacet 4 122
cert_cover_5 4 2 0 2 3 4 26 122 3
cert_coverFacet 5 618
cert_cover_5 5 2 0 2 4 8 106 618 3
cert_coverFacet 6 348
cert_cover_5 6 3 1 2 3 5 28 348 3
cert_coverFacet 7 460
cert_cover_5 7 3 1 2 5 6 332 460 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0055

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m14e11q2_0057.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0057

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [167, 647, 51, 595, 841, 369, 929, 542, 54, 220, 908, 244, 600, 488, 135, 19, 35, 515, 49, 81, 161, 289, 321, 577, 641, 769, 22, 38, 518, 50, 530, 28, 140, 524, 52, 212, 164, 644, 88, 536, 200, 328, 584, 392, 776, 112, 592, 224, 352, 416, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_167, vertices_647, vertices_51, vertices_595, vertices_841, vertices_369, vertices_929, vertices_542, vertices_54, vertices_220, vertices_908, vertices_244, vertices_600, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_135, vertices_19, vertices_35, vertices_515, vertices_49, vertices_81, vertices_161, vertices_289, vertices_321, vertices_577, vertices_641, vertices_769, vertices_22, vertices_38, vertices_518, vertices_50, vertices_530, vertices_28, vertices_140, vertices_524, vertices_52, vertices_212, vertices_164, vertices_644, vertices_88, vertices_536, vertices_200, vertices_328, vertices_584, vertices_392, vertices_776, vertices_112, vertices_592, vertices_224, vertices_352, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_167), (false, vertices_647), (false, vertices_51), (false, vertices_595), (false, vertices_841), (false, vertices_369), (false, vertices_929), (true, vertices_22), (true, vertices_28), (true, vertices_140), (true, vertices_524), (true, vertices_52), (true, vertices_212), (true, vertices_88), (true, vertices_536), (true, vertices_200), (true, vertices_392), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 15 17 19 21 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_167) then 12 else
  if p.val = (false, vertices_647) then 13 else
  if p.val = (false, vertices_51) then 0 else
  if p.val = (false, vertices_595) then 14 else
  if p.val = (false, vertices_841) then 18 else
  if p.val = (false, vertices_369) then 20 else
  if p.val = (false, vertices_929) then 22 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_140) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_52) then 5 else
  if p.val = (true, vertices_212) then 16 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_536) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_224) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_51), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_167), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(true, vertices_212), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 21 => Sum.inl 4
  | 22 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 8 542 22 2
cert_row_2 1 1 3 5 6 212
cert_row_4 2 1 2 6 7 8 908 140 3
cert_row_4 3 2 4 5 6 7 488 200 1
cert_rows
cert_pivot_2 0 3 1 2
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 22 542 2
cert_coverFacet 1 54
cert_cover_2 1 1 0 3 4 22 54 3
cert_coverFacet 2 220
cert_cover_5 2 1 1 2 3 5 28 220 3
cert_coverFacet 3 908
cert_cover_5 3 2 1 2 6 7 140 908 3
cert_coverFacet 4 244
cert_cover_5 4 1 1 3 4 5 52 244 3
cert_coverFacet 5 600
cert_cover_2 5 3 2 5 8 88 600 3
cert_coverFacet 6 488
cert_cover_5 6 3 2 4 5 6 200 488 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0057

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m14e11q2_0059.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0059

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [87, 151, 707, 109, 301, 901, 841, 618, 114, 562, 914, 116, 436, 824, 23, 67, 131, 45, 69, 133, 261, 73, 265, 577, 641, 769, 50, 82, 146, 530, 98, 546, 578, 642, 52, 84, 148, 100, 292, 388, 104, 296, 552, 584, 776, 112, 304, 560, 400, 784, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_87, vertices_151, vertices_707, vertices_109, vertices_301, vertices_901, vertices_841, vertices_618, vertices_114, vertices_562, vertices_914, vertices_116, vertices_436, vertices_824] (by decide +kernel)
  polygons := literalFinset [vertices_23, vertices_67, vertices_131, vertices_45, vertices_69, vertices_133, vertices_261, vertices_73, vertices_265, vertices_577, vertices_641, vertices_769, vertices_50, vertices_82, vertices_146, vertices_530, vertices_98, vertices_546, vertices_578, vertices_642, vertices_52, vertices_84, vertices_148, vertices_100, vertices_292, vertices_388, vertices_104, vertices_296, vertices_552, vertices_584, vertices_776, vertices_112, vertices_304, vertices_560, vertices_400, vertices_784, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_87), (false, vertices_151), (false, vertices_707), (false, vertices_109), (false, vertices_301), (false, vertices_901), (false, vertices_841), (true, vertices_50), (true, vertices_530), (true, vertices_98), (true, vertices_546), (true, vertices_52), (true, vertices_552), (true, vertices_112), (true, vertices_304), (true, vertices_560), (true, vertices_400), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 15 19 21 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_87) then 12 else
  if p.val = (false, vertices_151) then 13 else
  if p.val = (false, vertices_707) then 14 else
  if p.val = (false, vertices_109) then 16 else
  if p.val = (false, vertices_301) then 17 else
  if p.val = (false, vertices_901) then 18 else
  if p.val = (false, vertices_841) then 20 else
  if p.val = (true, vertices_50) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_552) then 5 else
  if p.val = (true, vertices_112) then 6 else
  if p.val = (true, vertices_304) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_400) then 9 else
  if p.val = (true, vertices_784) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_87), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_151), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_901), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 5 8 618 98 1
cert_row_4 1 0 3 6 7 8 914 146 3
cert_row_4 2 1 3 4 6 7 436 52 3
cert_row_4 3 2 3 4 7 8 824 296 1
cert_rows
cert_pivot_2 5 0 1 2
cert_heightProof 4
cert_coverFacet 0 618
cert_cover_5 0 0 0 2 4 5 98 618 1
cert_coverFacet 1 114
cert_cover_2 1 3 0 4 5 50 114 3
cert_coverFacet 2 562
cert_cover_2 2 3 0 4 8 50 562 3
cert_coverFacet 3 914
cert_cover_5 3 1 0 3 6 7 146 914 3
cert_coverFacet 4 116
cert_cover_2 4 3 1 4 5 52 116 3
cert_coverFacet 5 436
cert_cover_5 5 2 1 3 4 6 52 436 3
cert_coverFacet 6 824
cert_cover_5 6 3 2 3 4 7 296 824 1
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0059

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m14e11q2_0063.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0063

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [171, 555, 453, 217, 841, 929, 566, 214, 422, 154, 538, 348, 820, 792, 43, 73, 137, 521, 161, 545, 193, 321, 385, 769, 22, 38, 134, 26, 138, 522, 146, 530, 162, 546, 564, 84, 276, 292, 196, 324, 388, 88, 152, 280, 536, 328, 776, 208, 784, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_171, vertices_555, vertices_453, vertices_217, vertices_841, vertices_929, vertices_566, vertices_214, vertices_422, vertices_154, vertices_538, vertices_348, vertices_820, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_43, vertices_73, vertices_137, vertices_521, vertices_161, vertices_545, vertices_193, vertices_321, vertices_385, vertices_769, vertices_22, vertices_38, vertices_134, vertices_26, vertices_138, vertices_522, vertices_146, vertices_530, vertices_162, vertices_546, vertices_564, vertices_84, vertices_276, vertices_292, vertices_196, vertices_324, vertices_388, vertices_88, vertices_152, vertices_280, vertices_536, vertices_328, vertices_776, vertices_208, vertices_784, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_171), (false, vertices_555), (false, vertices_453), (false, vertices_217), (false, vertices_841), (false, vertices_929), (true, vertices_22), (true, vertices_38), (true, vertices_134), (true, vertices_26), (true, vertices_146), (true, vertices_530), (true, vertices_564), (true, vertices_84), (true, vertices_276), (true, vertices_292), (true, vertices_280), (true, vertices_536), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 21 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_171) then 13 else
  if p.val = (false, vertices_555) then 14 else
  if p.val = (false, vertices_453) then 16 else
  if p.val = (false, vertices_217) then 19 else
  if p.val = (false, vertices_841) then 20 else
  if p.val = (false, vertices_929) then 23 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_564) then 17 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_784) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_171), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_564), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 4 8 564
cert_row_4 1 0 1 4 6 7 422 38 3
cert_row_4 2 0 1 3 5 6 214 22 3
cert_row_4 3 1 2 3 5 7 348 84 1
cert_rows
cert_pivot_2 8 4 0 1
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 0 0 1 3 4 22 566 3
cert_coverFacet 1 214
cert_cover_5 1 2 0 1 3 5 22 214 3
cert_coverFacet 2 422
cert_cover_5 2 1 0 1 4 6 38 422 3
cert_coverFacet 3 154
cert_cover_2 3 2 0 3 6 26 154 3
cert_coverFacet 4 538
cert_cover_2 4 2 0 3 8 26 538 3
cert_coverFacet 5 348
cert_cover_5 5 3 1 2 3 5 84 348 1
cert_coverFacet 6 820
cert_cover_5 6 0 1 3 4 7 564 820 3
cert_coverFacet 7 792
cert_cover_2 7 3 2 7 8 280 792 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0063

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m14e11q2_0064.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0064

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [59, 555, 781, 409, 689, 961, 30, 526, 118, 838, 738, 220, 460, 240, 43, 25, 265, 521, 49, 145, 545, 385, 641, 769, 14, 22, 70, 518, 26, 522, 50, 98, 546, 578, 28, 204, 268, 524, 84, 324, 772, 152, 392, 112, 176, 208, 224, 672, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_59, vertices_555, vertices_781, vertices_409, vertices_689, vertices_961, vertices_30, vertices_526, vertices_118, vertices_838, vertices_738, vertices_220, vertices_460, vertices_240] (by decide +kernel)
  polygons := literalFinset [vertices_43, vertices_25, vertices_265, vertices_521, vertices_49, vertices_145, vertices_545, vertices_385, vertices_641, vertices_769, vertices_14, vertices_22, vertices_70, vertices_518, vertices_26, vertices_522, vertices_50, vertices_98, vertices_546, vertices_578, vertices_28, vertices_204, vertices_268, vertices_524, vertices_84, vertices_324, vertices_772, vertices_152, vertices_392, vertices_112, vertices_176, vertices_208, vertices_224, vertices_672, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_59), (false, vertices_555), (false, vertices_781), (false, vertices_409), (false, vertices_689), (false, vertices_961), (true, vertices_14), (true, vertices_22), (true, vertices_70), (true, vertices_518), (true, vertices_98), (true, vertices_578), (true, vertices_28), (true, vertices_204), (true, vertices_84), (true, vertices_324), (true, vertices_112), (true, vertices_208), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 20 22 23 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_59) then 13 else
  if p.val = (false, vertices_555) then 14 else
  if p.val = (false, vertices_781) then 16 else
  if p.val = (false, vertices_409) then 19 else
  if p.val = (false, vertices_689) then 21 else
  if p.val = (false, vertices_961) then 24 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_204) then 17 else
  if p.val = (true, vertices_84) then 7 else
  if p.val = (true, vertices_324) then 8 else
  if p.val = (true, vertices_112) then 9 else
  if p.val = (true, vertices_208) then 10 else
  if p.val = (true, vertices_224) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_59), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inr ⟨(false, vertices_961), by decide +kernel⟩
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 5 6 204
cert_row_4 1 0 1 3 4 5 118 22 3
cert_row_4 2 0 1 5 7 8 838 70 3
cert_row_4 3 0 4 5 6 8 738 98 3
cert_rows
cert_pivot_2 2 3 1 0
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 118
cert_cover_5 2 1 0 1 3 4 22 118 3
cert_coverFacet 3 838
cert_cover_5 3 2 0 1 5 7 70 838 3
cert_coverFacet 4 738
cert_cover_5 4 3 0 4 5 6 98 738 3
cert_coverFacet 5 220
cert_cover_5 5 0 1 2 3 5 28 220 3
cert_coverFacet 6 460
cert_cover_5 6 0 1 2 5 7 204 460 3
cert_coverFacet 7 240
cert_cover_2 7 4 3 5 6 112 240 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0064

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m14e11q2_0071.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0071

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [535, 307, 675, 653, 85, 229, 369, 794, 866, 412, 540, 468, 968, 736, 19, 35, 515, 21, 69, 133, 517, 305, 81, 97, 161, 641, 274, 530, 290, 546, 770, 28, 140, 524, 84, 404, 532, 196, 280, 536, 392, 648, 776, 336, 224, 352, 608, 672, 448, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_535, vertices_307, vertices_675, vertices_653, vertices_85, vertices_229, vertices_369, vertices_794, vertices_866, vertices_412, vertices_540, vertices_468, vertices_968, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_515, vertices_21, vertices_69, vertices_133, vertices_517, vertices_305, vertices_81, vertices_97, vertices_161, vertices_641, vertices_274, vertices_530, vertices_290, vertices_546, vertices_770, vertices_28, vertices_140, vertices_524, vertices_84, vertices_404, vertices_532, vertices_196, vertices_280, vertices_536, vertices_392, vertices_648, vertices_776, vertices_336, vertices_224, vertices_352, vertices_608, vertices_672, vertices_448, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_535), (false, vertices_307), (false, vertices_675), (false, vertices_653), (false, vertices_85), (false, vertices_229), (false, vertices_369), (true, vertices_770), (true, vertices_28), (true, vertices_404), (true, vertices_280), (true, vertices_536), (true, vertices_392), (true, vertices_776), (true, vertices_608), (true, vertices_448), (true, vertices_704), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 11 16 14 19 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_535) then 12 else
  if p.val = (false, vertices_307) then 20 else
  if p.val = (false, vertices_675) then 13 else
  if p.val = (false, vertices_653) then 15 else
  if p.val = (false, vertices_85) then 0 else
  if p.val = (false, vertices_229) then 17 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (true, vertices_770) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_404) then 18 else
  if p.val = (true, vertices_280) then 3 else
  if p.val = (true, vertices_536) then 4 else
  if p.val = (true, vertices_392) then 5 else
  if p.val = (true, vertices_776) then 6 else
  if p.val = (true, vertices_608) then 7 else
  if p.val = (true, vertices_448) then 8 else
  if p.val = (true, vertices_704) then 9 else
  if p.val = (true, vertices_832) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_85), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 11 => Sum.inl 0
  | 12 => Sum.inr ⟨(false, vertices_535), by decide +kernel⟩
  | 13 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 14 => Sum.inl 2
  | 15 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_404), by decide +kernel⟩
  | 19 => Sum.inl 3
  | 20 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 6 7 404
cert_row_4 1 0 2 3 7 8 794 274 1
cert_row_4 2 0 4 5 7 8 866 290 2
cert_row_4 3 2 5 6 7 8 968 392 1
cert_rows
cert_pivot_2 1 3 0 2
cert_heightProof 4
cert_coverFacet 0 794
cert_cover_5 0 1 0 2 3 7 274 794 1
cert_coverFacet 1 866
cert_cover_5 1 2 0 4 5 7 290 866 2
cert_coverFacet 2 412
cert_cover_5 2 0 1 2 3 6 28 412 3
cert_coverFacet 3 540
cert_cover_2 3 2 1 3 8 28 540 3
cert_coverFacet 4 468
cert_cover_5 4 0 1 3 5 6 84 468 3
cert_coverFacet 5 968
cert_cover_5 5 3 2 5 6 7 392 968 1
cert_coverFacet 6 736
cert_cover_2 6 5 4 6 8 224 736 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0071

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m14e11q2_0085.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0085

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [59, 837, 793, 233, 585, 369, 206, 590, 902, 538, 170, 690, 484, 944, 25, 41, 73, 521, 49, 273, 97, 321, 577, 769, 78, 134, 518, 26, 42, 138, 522, 50, 530, 162, 642, 196, 324, 580, 388, 772, 536, 168, 200, 584, 688, 304, 784, 224, 352, 416, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_59, vertices_837, vertices_793, vertices_233, vertices_585, vertices_369, vertices_206, vertices_590, vertices_902, vertices_538, vertices_170, vertices_690, vertices_484, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_73, vertices_521, vertices_49, vertices_273, vertices_97, vertices_321, vertices_577, vertices_769, vertices_78, vertices_134, vertices_518, vertices_26, vertices_42, vertices_138, vertices_522, vertices_50, vertices_530, vertices_162, vertices_642, vertices_196, vertices_324, vertices_580, vertices_388, vertices_772, vertices_536, vertices_168, vertices_200, vertices_584, vertices_688, vertices_304, vertices_784, vertices_224, vertices_352, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_59), (false, vertices_837), (false, vertices_793), (false, vertices_233), (false, vertices_585), (false, vertices_369), (true, vertices_78), (true, vertices_134), (true, vertices_518), (true, vertices_138), (true, vertices_522), (true, vertices_530), (true, vertices_162), (true, vertices_642), (true, vertices_196), (true, vertices_388), (true, vertices_688), (true, vertices_416), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 20 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_59) then 13 else
  if p.val = (false, vertices_837) then 16 else
  if p.val = (false, vertices_793) then 18 else
  if p.val = (false, vertices_233) then 19 else
  if p.val = (false, vertices_585) then 0 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (true, vertices_78) then 14 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_196) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_688) then 22 else
  if p.val = (true, vertices_416) then 10 else
  if p.val = (true, vertices_896) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_585), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_59), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_78), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_688), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 3 4 6 8 688
cert_row_2 1 0 1 2 5 78
cert_row_4 2 0 1 6 7 8 902 134 3
cert_row_4 3 1 4 5 6 7 484 196 1
cert_rows
cert_pivot_2 3 2 0 1
cert_heightProof 4
cert_coverFacet 0 206
cert_cover_5 0 1 0 1 2 6 78 206 3
cert_coverFacet 1 590
cert_cover_5 1 1 0 1 2 8 78 590 3
cert_coverFacet 2 902
cert_cover_5 2 2 0 1 6 7 134 902 3
cert_coverFacet 3 538
cert_cover_2 3 2 0 3 8 26 538 3
cert_coverFacet 4 170
cert_cover_2 4 2 0 4 6 42 170 3
cert_coverFacet 5 690
cert_cover_5 5 0 0 3 4 6 50 690 3
cert_coverFacet 6 484
cert_cover_5 6 3 1 4 5 6 196 484 1
cert_coverFacet 7 944
cert_cover_5 7 0 3 4 6 7 688 944 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0085

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m14e11q2_0093.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0093

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [563, 661, 457, 369, 401, 737, 110, 398, 406, 534, 614, 314, 716, 360, 49, 145, 273, 529, 97, 545, 193, 321, 385, 641, 14, 22, 102, 390, 518, 42, 266, 50, 274, 530, 546, 76, 140, 148, 532, 580, 644, 104, 296, 200, 328, 392, 304, 400, 352, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_563, vertices_661, vertices_457, vertices_369, vertices_401, vertices_737, vertices_110, vertices_398, vertices_406, vertices_534, vertices_614, vertices_314, vertices_716, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_145, vertices_273, vertices_529, vertices_97, vertices_545, vertices_193, vertices_321, vertices_385, vertices_641, vertices_14, vertices_22, vertices_102, vertices_390, vertices_518, vertices_42, vertices_266, vertices_50, vertices_274, vertices_530, vertices_546, vertices_76, vertices_140, vertices_148, vertices_532, vertices_580, vertices_644, vertices_104, vertices_296, vertices_200, vertices_328, vertices_392, vertices_304, vertices_400, vertices_352, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_563), (false, vertices_661), (false, vertices_457), (false, vertices_369), (false, vertices_401), (false, vertices_737), (true, vertices_14), (true, vertices_22), (true, vertices_102), (true, vertices_390), (true, vertices_518), (true, vertices_42), (true, vertices_266), (true, vertices_274), (true, vertices_76), (true, vertices_140), (true, vertices_580), (true, vertices_104), (true, vertices_296)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 21 23 12 14 18 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_563) then 15 else
  if p.val = (false, vertices_661) then 16 else
  if p.val = (false, vertices_457) then 13 else
  if p.val = (false, vertices_369) then 17 else
  if p.val = (false, vertices_401) then 0 else
  if p.val = (false, vertices_737) then 19 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_22) then 2 else
  if p.val = (true, vertices_102) then 20 else
  if p.val = (true, vertices_390) then 22 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_42) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_274) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_580) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_296) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_401), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inl 2
  | 13 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 14 => Sum.inl 3
  | 15 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 18 => Sum.inl 4
  | 19 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_102), by decide +kernel⟩
  | 21 => Sum.inl 0
  | 22 => Sum.inr ⟨(true, vertices_390), by decide +kernel⟩
  | 23 => Sum.inl 1
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 4 7 314 42 2
cert_row_2 1 0 1 6 7 390
cert_row_2 2 0 1 4 5 102
cert_row_4 3 1 2 5 6 8 716 76 3
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 2 0 1 2 4 14 110 3
cert_coverFacet 1 398
cert_cover_5 1 1 0 1 2 6 14 398 3
cert_coverFacet 2 406
cert_cover_5 2 1 0 1 3 6 22 406 3
cert_coverFacet 3 534
cert_cover_2 3 1 0 3 8 22 534 3
cert_coverFacet 4 614
cert_cover_5 4 2 0 1 4 8 102 614 3
cert_coverFacet 5 314
cert_cover_5 5 0 0 2 3 4 42 314 2
cert_coverFacet 6 716
cert_cover_5 6 3 1 2 5 6 76 716 3
cert_coverFacet 7 360
cert_cover_2 7 4 2 5 7 104 360 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0093

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m14e11q2_0094.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0094

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [527, 91, 787, 397, 773, 457, 369, 714, 114, 562, 738, 684, 820, 484, 11, 19, 515, 13, 261, 517, 73, 393, 81, 273, 321, 769, 74, 522, 50, 82, 530, 98, 546, 706, 140, 524, 164, 292, 548, 388, 772, 200, 648, 112, 304, 560, 784, 224, 352, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_527, vertices_91, vertices_787, vertices_397, vertices_773, vertices_457, vertices_369, vertices_714, vertices_114, vertices_562, vertices_738, vertices_684, vertices_820, vertices_484] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_515, vertices_13, vertices_261, vertices_517, vertices_73, vertices_393, vertices_81, vertices_273, vertices_321, vertices_769, vertices_74, vertices_522, vertices_50, vertices_82, vertices_530, vertices_98, vertices_546, vertices_706, vertices_140, vertices_524, vertices_164, vertices_292, vertices_548, vertices_388, vertices_772, vertices_200, vertices_648, vertices_112, vertices_304, vertices_560, vertices_784, vertices_224, vertices_352, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_527), (false, vertices_91), (false, vertices_787), (false, vertices_397), (false, vertices_773), (false, vertices_457), (false, vertices_369), (true, vertices_50), (true, vertices_98), (true, vertices_546), (true, vertices_706), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_648), (true, vertices_560), (true, vertices_224), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 13 11 17 20 22 23 24 25 26
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_527) then 12 else
  if p.val = (false, vertices_91) then 14 else
  if p.val = (false, vertices_787) then 15 else
  if p.val = (false, vertices_397) then 18 else
  if p.val = (false, vertices_773) then 0 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (false, vertices_369) then 21 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_98) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_706) then 16 else
  if p.val = (true, vertices_164) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_648) then 7 else
  if p.val = (true, vertices_560) then 8 else
  if p.val = (true, vertices_224) then 9 else
  if p.val = (true, vertices_672) then 10 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_773), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 11 => Sum.inl 1
  | 12 => Sum.inr ⟨(false, vertices_527), by decide +kernel⟩
  | 13 => Sum.inl 0
  | 14 => Sum.inr ⟨(false, vertices_91), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_706), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inl 5
  | 24 => Sum.inl 6
  | 25 => Sum.inl 7
  | 26 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 5 6 8 706
cert_row_4 1 1 2 4 6 8 684 140 2
cert_row_4 2 1 3 4 7 8 820 292 1
cert_row_4 3 1 4 5 6 7 484 164 2
cert_rows
cert_pivot_2 0 2 3 1
cert_heightProof 4
cert_coverFacet 0 714
cert_cover_5 0 0 0 2 5 6 74 714 3
cert_coverFacet 1 114
cert_cover_2 1 3 0 4 5 50 114 3
cert_coverFacet 2 562
cert_cover_2 2 3 0 4 8 50 562 3
cert_coverFacet 3 738
cert_cover_5 3 0 0 4 5 6 98 738 3
cert_coverFacet 4 684
cert_cover_5 4 1 1 2 4 6 140 684 2
cert_coverFacet 5 820
cert_cover_5 5 2 1 3 4 7 292 820 1
cert_coverFacet 6 484
cert_cover_5 6 3 1 4 5 6 164 484 2
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0094

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m14e11q2_0095.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0095

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [327, 307, 563, 707, 665, 465, 590, 294, 550, 572, 236, 484, 440, 712, 51, 67, 259, 515, 145, 273, 529, 193, 321, 641, 38, 70, 262, 518, 290, 546, 578, 44, 76, 524, 228, 292, 548, 324, 56, 152, 536, 168, 200, 584, 648, 304, 560, 400, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_327, vertices_307, vertices_563, vertices_707, vertices_665, vertices_465, vertices_590, vertices_294, vertices_550, vertices_572, vertices_236, vertices_484, vertices_440, vertices_712] (by decide +kernel)
  polygons := literalFinset [vertices_51, vertices_67, vertices_259, vertices_515, vertices_145, vertices_273, vertices_529, vertices_193, vertices_321, vertices_641, vertices_38, vertices_70, vertices_262, vertices_518, vertices_290, vertices_546, vertices_578, vertices_44, vertices_76, vertices_524, vertices_228, vertices_292, vertices_548, vertices_324, vertices_56, vertices_152, vertices_536, vertices_168, vertices_200, vertices_584, vertices_648, vertices_304, vertices_560, vertices_400, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_327), (false, vertices_307), (false, vertices_563), (false, vertices_707), (false, vertices_665), (false, vertices_465), (true, vertices_38), (true, vertices_518), (true, vertices_44), (true, vertices_76), (true, vertices_524), (true, vertices_228), (true, vertices_292), (true, vertices_548), (true, vertices_56), (true, vertices_168), (true, vertices_200), (true, vertices_584), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 12 19 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_327) then 13 else
  if p.val = (false, vertices_307) then 16 else
  if p.val = (false, vertices_563) then 17 else
  if p.val = (false, vertices_707) then 18 else
  if p.val = (false, vertices_665) then 20 else
  if p.val = (false, vertices_465) then 22 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_44) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_228) then 14 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_168) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_416) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 12 => Sum.inl 1
  | 13 => Sum.inr ⟨(false, vertices_327), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_228), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_563), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 70 2
cert_row_2 1 1 4 5 6 228
cert_row_4 2 1 2 3 4 8 572 44 2
cert_row_4 3 2 3 4 6 7 440 56 3
cert_rows
cert_pivot_2 0 5 1 2
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 70 590 2
cert_coverFacet 1 294
cert_cover_2 1 1 0 4 7 38 294 3
cert_coverFacet 2 550
cert_cover_2 2 1 0 4 8 38 550 3
cert_coverFacet 3 572
cert_cover_5 3 2 1 2 3 4 44 572 2
cert_coverFacet 4 236
cert_cover_5 4 1 1 2 4 5 44 236 3
cert_coverFacet 5 484
cert_cover_5 5 1 1 4 5 7 228 484 3
cert_coverFacet 6 440
cert_cover_5 6 3 2 3 4 6 56 440 3
cert_coverFacet 7 712
cert_cover_2 7 5 2 6 8 200 712 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0095

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m14e11q2_0096.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0096

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [675, 803, 781, 361, 713, 241, 542, 182, 294, 774, 722, 348, 372, 600, 547, 73, 265, 521, 97, 161, 289, 193, 641, 769, 22, 38, 262, 518, 146, 530, 162, 290, 642, 770, 28, 268, 524, 52, 340, 292, 772, 88, 536, 328, 584, 112, 176, 208, 592, 352, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_675, vertices_803, vertices_781, vertices_361, vertices_713, vertices_241, vertices_542, vertices_182, vertices_294, vertices_774, vertices_722, vertices_348, vertices_372, vertices_600] (by decide +kernel)
  polygons := literalFinset [vertices_547, vertices_73, vertices_265, vertices_521, vertices_97, vertices_161, vertices_289, vertices_193, vertices_641, vertices_769, vertices_22, vertices_38, vertices_262, vertices_518, vertices_146, vertices_530, vertices_162, vertices_290, vertices_642, vertices_770, vertices_28, vertices_268, vertices_524, vertices_52, vertices_340, vertices_292, vertices_772, vertices_88, vertices_536, vertices_328, vertices_584, vertices_112, vertices_176, vertices_208, vertices_592, vertices_352, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_675), (false, vertices_803), (false, vertices_781), (false, vertices_361), (false, vertices_713), (false, vertices_241), (true, vertices_22), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_146), (true, vertices_530), (true, vertices_28), (true, vertices_52), (true, vertices_340), (true, vertices_292), (true, vertices_88), (true, vertices_536), (true, vertices_592)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 18 21 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_675) then 13 else
  if p.val = (false, vertices_803) then 14 else
  if p.val = (false, vertices_781) then 16 else
  if p.val = (false, vertices_361) then 19 else
  if p.val = (false, vertices_713) then 20 else
  if p.val = (false, vertices_241) then 22 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_340) then 17 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_592) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 14 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_340), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 5 7 340
cert_row_4 1 0 1 2 3 8 542 22 2
cert_row_4 2 0 1 3 4 6 182 22 3
cert_row_4 3 0 3 5 6 8 722 146 2
cert_rows
cert_pivot_2 7 2 1 0
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 1 0 1 2 3 22 542 2
cert_coverFacet 1 182
cert_cover_5 1 2 0 1 3 4 22 182 3
cert_coverFacet 2 294
cert_cover_2 2 1 0 4 7 38 294 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 722
cert_cover_5 4 3 0 3 5 6 146 722 2
cert_coverFacet 5 348
cert_cover_5 5 0 1 2 3 5 28 348 3
cert_coverFacet 6 372
cert_cover_5 6 0 1 3 4 5 52 372 3
cert_coverFacet 7 600
cert_cover_2 7 3 2 5 8 88 600 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0096

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m14e11q2_0098.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0098

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [179, 837, 665, 905, 625, 481, 110, 782, 566, 154, 538, 234, 460, 612, 649, 49, 145, 529, 97, 161, 321, 577, 385, 769, 14, 38, 518, 26, 106, 138, 522, 50, 146, 530, 162, 76, 268, 100, 548, 324, 580, 772, 152, 536, 200, 392, 776, 560, 224, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_179, vertices_837, vertices_665, vertices_905, vertices_625, vertices_481, vertices_110, vertices_782, vertices_566, vertices_154, vertices_538, vertices_234, vertices_460, vertices_612] (by decide +kernel)
  polygons := literalFinset [vertices_649, vertices_49, vertices_145, vertices_529, vertices_97, vertices_161, vertices_321, vertices_577, vertices_385, vertices_769, vertices_14, vertices_38, vertices_518, vertices_26, vertices_106, vertices_138, vertices_522, vertices_50, vertices_146, vertices_530, vertices_162, vertices_76, vertices_268, vertices_100, vertices_548, vertices_324, vertices_580, vertices_772, vertices_152, vertices_536, vertices_200, vertices_392, vertices_776, vertices_560, vertices_224, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_179), (false, vertices_837), (false, vertices_665), (false, vertices_905), (false, vertices_625), (false, vertices_481), (true, vertices_14), (true, vertices_38), (true, vertices_518), (true, vertices_26), (true, vertices_106), (true, vertices_138), (true, vertices_522), (true, vertices_530), (true, vertices_76), (true, vertices_268), (true, vertices_100), (true, vertices_548), (true, vertices_200)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 12 15 17 20 22 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_179) then 13 else
  if p.val = (false, vertices_837) then 16 else
  if p.val = (false, vertices_665) then 18 else
  if p.val = (false, vertices_905) then 19 else
  if p.val = (false, vertices_625) then 21 else
  if p.val = (false, vertices_481) then 23 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_106) then 14 else
  if p.val = (true, vertices_138) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_76) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_200) then 11 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 12 => Sum.inl 0
  | 13 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_106), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 17 => Sum.inl 2
  | 18 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_905), by decide +kernel⟩
  | 20 => Sum.inl 3
  | 21 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 22 => Sum.inl 4
  | 23 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 8 566 38 2
cert_row_2 1 0 2 4 5 106
cert_row_4 2 0 1 2 7 8 782 14 3
cert_row_4 3 1 2 5 6 7 460 76 3
cert_rows
cert_pivot_2 3 4 0 1
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 1 0 1 2 4 14 110 3
cert_coverFacet 1 782
cert_cover_5 1 2 0 1 2 7 14 782 3
cert_coverFacet 2 566
cert_cover_5 2 0 0 1 3 4 38 566 2
cert_coverFacet 3 154
cert_cover_2 3 2 0 3 6 26 154 3
cert_coverFacet 4 538
cert_cover_2 4 2 0 3 8 26 538 3
cert_coverFacet 5 234
cert_cover_5 5 1 0 2 4 6 106 234 3
cert_coverFacet 6 460
cert_cover_5 6 3 1 2 5 6 76 460 3
cert_coverFacet 7 612
cert_cover_2 7 4 1 5 8 100 612 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0098

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m14e11q2_0099.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0099

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [31, 557, 213, 101, 153, 233, 526, 342, 614, 666, 914, 866, 936, 496, 13, 21, 37, 69, 25, 41, 137, 145, 97, 193, 14, 22, 70, 518, 26, 522, 658, 274, 610, 322, 770, 524, 84, 100, 548, 152, 168, 552, 648, 208, 336, 400, 224, 352, 416, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_31, vertices_557, vertices_213, vertices_101, vertices_153, vertices_233, vertices_526, vertices_342, vertices_614, vertices_666, vertices_914, vertices_866, vertices_936, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_21, vertices_37, vertices_69, vertices_25, vertices_41, vertices_137, vertices_145, vertices_97, vertices_193, vertices_14, vertices_22, vertices_70, vertices_518, vertices_26, vertices_522, vertices_658, vertices_274, vertices_610, vertices_322, vertices_770, vertices_524, vertices_84, vertices_100, vertices_548, vertices_152, vertices_168, vertices_552, vertices_648, vertices_208, vertices_336, vertices_400, vertices_224, vertices_352, vertices_416, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_31), (false, vertices_557), (false, vertices_213), (false, vertices_101), (false, vertices_153), (false, vertices_233), (true, vertices_70), (true, vertices_518), (true, vertices_522), (true, vertices_658), (true, vertices_274), (true, vertices_610), (true, vertices_322), (true, vertices_770), (true, vertices_648), (true, vertices_336), (true, vertices_400), (true, vertices_352), (true, vertices_416), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 23 15 19 21 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_31) then 16 else
  if p.val = (false, vertices_557) then 17 else
  if p.val = (false, vertices_213) then 18 else
  if p.val = (false, vertices_101) then 0 else
  if p.val = (false, vertices_153) then 1 else
  if p.val = (false, vertices_233) then 20 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_658) then 22 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_610) then 24 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_648) then 8 else
  if p.val = (true, vertices_336) then 9 else
  if p.val = (true, vertices_400) then 10 else
  if p.val = (true, vertices_352) then 11 else
  if p.val = (true, vertices_416) then 12 else
  if p.val = (true, vertices_800) then 13 else
  if p.val = (true, vertices_896) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_101), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_153), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 15 => Sum.inl 1
  | 16 => Sum.inr ⟨(false, vertices_31), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 21 => Sum.inl 3
  | 22 => Sum.inr ⟨(true, vertices_658), by decide +kernel⟩
  | 23 => Sum.inl 0
  | 24 => Sum.inr ⟨(true, vertices_610), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 7 342 22 3
cert_row_4 1 2 4 6 7 8 936 168 3
cert_row_4 2 3 4 5 6 7 496 208 1
cert_row_2 3 0 3 6 8 658
cert_row_2 4 0 4 5 8 610
cert_rows_2
cert_pivot 1 2 7 3 0
cert_heightProof 5
cert_coverFacet 0 526
cert_cover_2 0 1 0 2 8 14 526 3
cert_coverFacet 1 342
cert_cover_5 1 0 0 1 3 5 22 342 3
cert_coverFacet 2 614
cert_cover_5 2 4 0 1 4 5 70 614 2
cert_coverFacet 3 666
cert_cover_5 3 3 0 2 3 6 26 666 3
cert_coverFacet 4 914
cert_cover_5 4 3 0 3 6 7 658 914 3
cert_coverFacet 5 866
cert_cover_5 5 4 0 4 5 7 610 866 3
cert_coverFacet 6 936
cert_cover_5 6 1 2 4 6 7 168 936 3
cert_coverFacet 7 496
cert_cover_5 7 2 3 4 5 6 208 496 1
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 5 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0099

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e10q0_0000.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0000

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [279, 107, 595, 419, 173, 589, 533, 389, 370, 668, 404, 616, 936, 976, 864, 19, 35, 67, 259, 13, 21, 133, 261, 517, 41, 73, 529, 161, 577, 385, 82, 274, 98, 290, 140, 524, 148, 276, 532, 388, 104, 168, 552, 584, 648, 336, 592, 400, 656, 352, 608, 416, 800, 832, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_279, vertices_107, vertices_595, vertices_419, vertices_173, vertices_589, vertices_533, vertices_389, vertices_370, vertices_668, vertices_404, vertices_616, vertices_936, vertices_976, vertices_864] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_35, vertices_67, vertices_259, vertices_13, vertices_21, vertices_133, vertices_261, vertices_517, vertices_41, vertices_73, vertices_529, vertices_161, vertices_577, vertices_385, vertices_82, vertices_274, vertices_98, vertices_290, vertices_140, vertices_524, vertices_148, vertices_276, vertices_532, vertices_388, vertices_104, vertices_168, vertices_552, vertices_584, vertices_648, vertices_336, vertices_592, vertices_400, vertices_656, vertices_352, vertices_608, vertices_416, vertices_800, vertices_832, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_279), (false, vertices_107), (false, vertices_595), (false, vertices_419), (false, vertices_173), (false, vertices_589), (false, vertices_533), (false, vertices_389), (true, vertices_148), (true, vertices_552), (true, vertices_648), (true, vertices_336), (true, vertices_400), (true, vertices_656), (true, vertices_352), (true, vertices_608), (true, vertices_800), (true, vertices_832), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 13 21 22 23 24 25 26 27
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_279) then 14 else
  if p.val = (false, vertices_107) then 18 else
  if p.val = (false, vertices_595) then 19 else
  if p.val = (false, vertices_419) then 20 else
  if p.val = (false, vertices_173) then 15 else
  if p.val = (false, vertices_589) then 16 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_389) then 1 else
  if p.val = (true, vertices_148) then 2 else
  if p.val = (true, vertices_552) then 3 else
  if p.val = (true, vertices_648) then 4 else
  if p.val = (true, vertices_336) then 5 else
  if p.val = (true, vertices_400) then 6 else
  if p.val = (true, vertices_656) then 7 else
  if p.val = (true, vertices_352) then 8 else
  if p.val = (true, vertices_608) then 9 else
  if p.val = (true, vertices_800) then 10 else
  if p.val = (true, vertices_832) then 11 else
  if p.val = (true, vertices_896) then 12 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_389), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 13 => Sum.inl 1
  | 14 => Sum.inr ⟨(false, vertices_279), by decide +kernel⟩
  | 15 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 16 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_107), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inl 3
  | 23 => Sum.inl 4
  | 24 => Sum.inl 5
  | 25 => Sum.inl 6
  | 26 => Sum.inl 7
  | 27 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 5 7 370 82 2
cert_row_4 1 1 2 3 6 8 668 140 2
cert_row_4 2 2 4 6 7 8 936 168 3
cert_row_4 3 3 5 6 7 8 976 336 2
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 370
cert_cover_5 0 0 0 3 4 5 82 370 2
cert_coverFacet 1 668
cert_cover_5 1 1 1 2 3 6 140 668 2
cert_coverFacet 2 404
cert_cover_2 2 3 1 6 7 148 404 3
cert_coverFacet 3 616
cert_cover_2 3 4 2 5 8 104 616 3
cert_coverFacet 4 936
cert_cover_5 4 2 2 4 6 7 168 936 3
cert_coverFacet 5 976
cert_cover_5 5 3 3 5 6 7 336 976 2
cert_coverFacet 6 864
cert_cover_2 6 5 4 7 8 352 864 3
cert_coveringFacets_4
cert_coveringProof_5
cert_certificate 4 7
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0000

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e10q0_0001.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0001

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 587, 675, 709, 457, 433, 806, 794, 604, 244, 308, 788, 676, 344, 464, 11, 35, 515, 73, 265, 161, 289, 193, 577, 385, 641, 266, 522, 290, 546, 770, 52, 84, 276, 532, 164, 292, 548, 196, 580, 644, 772, 88, 280, 536, 328, 584, 176, 304, 208, 336, 400, 784, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_587, vertices_675, vertices_709, vertices_457, vertices_433, vertices_806, vertices_794, vertices_604, vertices_244, vertices_308, vertices_788, vertices_676, vertices_344, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_515, vertices_73, vertices_265, vertices_161, vertices_289, vertices_193, vertices_577, vertices_385, vertices_641, vertices_266, vertices_522, vertices_290, vertices_546, vertices_770, vertices_52, vertices_84, vertices_276, vertices_532, vertices_164, vertices_292, vertices_548, vertices_196, vertices_580, vertices_644, vertices_772, vertices_88, vertices_280, vertices_536, vertices_328, vertices_584, vertices_176, vertices_304, vertices_208, vertices_336, vertices_400, vertices_784, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_587), (false, vertices_675), (false, vertices_709), (false, vertices_457), (false, vertices_433), (true, vertices_770), (true, vertices_52), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_772), (true, vertices_88), (true, vertices_280), (true, vertices_536), (true, vertices_208), (true, vertices_336), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 16 else
  if p.val = (false, vertices_587) then 17 else
  if p.val = (false, vertices_675) then 18 else
  if p.val = (false, vertices_709) then 20 else
  if p.val = (false, vertices_457) then 22 else
  if p.val = (false, vertices_433) then 24 else
  if p.val = (true, vertices_770) then 0 else
  if p.val = (true, vertices_52) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_548) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_784) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_675), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
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
cert_row_4 0 1 3 4 5 6 244 52 3
cert_row_4 1 0 1 4 7 8 806 290 1
cert_row_4 2 0 2 3 7 8 794 266 2
cert_row_4 3 1 2 3 5 8 604 84 1
cert_rows
cert_pivot_2 6 4 0 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 1 0 1 4 7 290 806 1
cert_coverFacet 1 794
cert_cover_5 1 2 0 2 3 7 266 794 2
cert_coverFacet 2 604
cert_cover_5 2 3 1 2 3 5 84 604 1
cert_coverFacet 3 244
cert_cover_5 3 0 1 3 4 5 52 244 3
cert_coverFacet 4 308
cert_cover_2 4 3 1 4 7 52 308 3
cert_coverFacet 5 788
cert_cover_2 5 3 1 7 8 276 788 3
cert_coverFacet 6 676
cert_cover_2 6 4 1 6 8 164 676 3
cert_coverFacet 7 344
cert_cover_2 7 3 2 5 7 88 344 3
cert_coverFacet 8 464
cert_cover_2 8 5 3 6 7 208 464 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0001

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e10q0_0002.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0002

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [555, 331, 419, 677, 713, 465, 806, 794, 604, 244, 308, 788, 708, 344, 432, 11, 35, 259, 73, 521, 161, 545, 193, 321, 385, 641, 266, 522, 290, 546, 770, 52, 84, 276, 532, 164, 292, 548, 196, 580, 644, 772, 88, 280, 536, 328, 584, 176, 304, 208, 336, 400, 784, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_555, vertices_331, vertices_419, vertices_677, vertices_713, vertices_465, vertices_806, vertices_794, vertices_604, vertices_244, vertices_308, vertices_788, vertices_708, vertices_344, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_35, vertices_259, vertices_73, vertices_521, vertices_161, vertices_545, vertices_193, vertices_321, vertices_385, vertices_641, vertices_266, vertices_522, vertices_290, vertices_546, vertices_770, vertices_52, vertices_84, vertices_276, vertices_532, vertices_164, vertices_292, vertices_548, vertices_196, vertices_580, vertices_644, vertices_772, vertices_88, vertices_280, vertices_536, vertices_328, vertices_584, vertices_176, vertices_304, vertices_208, vertices_336, vertices_400, vertices_784, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_555), (false, vertices_331), (false, vertices_419), (false, vertices_677), (false, vertices_713), (false, vertices_465), (true, vertices_770), (true, vertices_52), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_292), (true, vertices_196), (true, vertices_580), (true, vertices_772), (true, vertices_88), (true, vertices_280), (true, vertices_536), (true, vertices_176), (true, vertices_304), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 19 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_555) then 16 else
  if p.val = (false, vertices_331) then 17 else
  if p.val = (false, vertices_419) then 18 else
  if p.val = (false, vertices_677) then 20 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (true, vertices_770) then 0 else
  if p.val = (true, vertices_52) then 1 else
  if p.val = (true, vertices_84) then 2 else
  if p.val = (true, vertices_276) then 3 else
  if p.val = (true, vertices_532) then 4 else
  if p.val = (true, vertices_292) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_580) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_784) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_419), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
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
cert_row_4 0 1 3 4 5 6 244 52 3
cert_row_4 1 0 1 4 7 8 806 290 1
cert_row_4 2 0 2 3 7 8 794 266 2
cert_row_4 3 1 2 3 5 8 604 84 1
cert_rows
cert_pivot_2 6 4 0 1
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 1 0 1 4 7 290 806 1
cert_coverFacet 1 794
cert_cover_5 1 2 0 2 3 7 266 794 2
cert_coverFacet 2 604
cert_cover_5 2 3 1 2 3 5 84 604 1
cert_coverFacet 3 244
cert_cover_5 3 0 1 3 4 5 52 244 3
cert_coverFacet 4 308
cert_cover_2 4 3 1 4 7 52 308 3
cert_coverFacet 5 788
cert_cover_2 5 3 1 7 8 276 788 3
cert_coverFacet 6 708
cert_cover_2 6 5 1 6 8 196 708 3
cert_coverFacet 7 344
cert_cover_2 7 3 2 5 7 88 344 3
cert_coverFacet 8 432
cert_cover_2 8 4 3 6 7 176 432 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0002

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_2553 : Certifies 2553 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0809.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2554 : Certifies 2554 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0810.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2555 : Certifies 2555 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0812.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2556 : Certifies 2556 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0814.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2557 : Certifies 2557 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0815.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2558 : Certifies 2558 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e10q1_0816.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2559 : Certifies 2559 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0018.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2560 : Certifies 2560 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0019.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2561 : Certifies 2561 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0021.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2562 : Certifies 2562 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0022.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2563 : Certifies 2563 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0031.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2564 : Certifies 2564 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0035.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2565 : Certifies 2565 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0046.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2566 : Certifies 2566 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0052.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2567 : Certifies 2567 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0055.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2568 : Certifies 2568 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0057.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2569 : Certifies 2569 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0059.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2570 : Certifies 2570 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0063.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2571 : Certifies 2571 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0064.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2572 : Certifies 2572 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0071.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2573 : Certifies 2573 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0085.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2574 : Certifies 2574 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0093.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2575 : Certifies 2575 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0094.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2576 : Certifies 2576 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0095.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2577 : Certifies 2577 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0096.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2578 : Certifies 2578 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0098.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2579 : Certifies 2579 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m14e11q2_0099.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2580 : Certifies 2580 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0000.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2581 : Certifies 2581 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0001.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2582 : Certifies 2582 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q0_0002.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B084 (j : Fin 30) :
    Certifies (2553 + j.val) := by
  fin_cases j
  · exact projection_2553
  · exact projection_2554
  · exact projection_2555
  · exact projection_2556
  · exact projection_2557
  · exact projection_2558
  · exact projection_2559
  · exact projection_2560
  · exact projection_2561
  · exact projection_2562
  · exact projection_2563
  · exact projection_2564
  · exact projection_2565
  · exact projection_2566
  · exact projection_2567
  · exact projection_2568
  · exact projection_2569
  · exact projection_2570
  · exact projection_2571
  · exact projection_2572
  · exact projection_2573
  · exact projection_2574
  · exact projection_2575
  · exact projection_2576
  · exact projection_2577
  · exact projection_2578
  · exact projection_2579
  · exact projection_2580
  · exact projection_2581
  · exact projection_2582

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
