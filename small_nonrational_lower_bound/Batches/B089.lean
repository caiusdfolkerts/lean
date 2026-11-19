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
/- Source: ProjectionCertificates/R_m15e10q1_0089.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0089

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [59, 267, 595, 323, 837, 425, 817, 218, 458, 684, 724, 484, 804, 568, 664, 11, 19, 67, 259, 41, 265, 49, 529, 289, 321, 577, 769, 26, 202, 266, 82, 322, 164, 292, 548, 196, 324, 580, 644, 772, 56, 152, 536, 168, 552, 392, 648, 560, 208, 592, 656, 416, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_59, vertices_267, vertices_595, vertices_323, vertices_837, vertices_425, vertices_817, vertices_218, vertices_458, vertices_684, vertices_724, vertices_484, vertices_804, vertices_568, vertices_664] (by decide +kernel)
  polygons := literalFinset [vertices_11, vertices_19, vertices_67, vertices_259, vertices_41, vertices_265, vertices_49, vertices_529, vertices_289, vertices_321, vertices_577, vertices_769, vertices_26, vertices_202, vertices_266, vertices_82, vertices_322, vertices_164, vertices_292, vertices_548, vertices_196, vertices_324, vertices_580, vertices_644, vertices_772, vertices_56, vertices_152, vertices_536, vertices_168, vertices_552, vertices_392, vertices_648, vertices_560, vertices_208, vertices_592, vertices_656, vertices_416, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_59), (false, vertices_267), (false, vertices_595), (false, vertices_323), (false, vertices_837), (false, vertices_425), (false, vertices_817), (true, vertices_202), (true, vertices_164), (true, vertices_292), (true, vertices_548), (true, vertices_196), (true, vertices_644), (true, vertices_152), (true, vertices_536), (true, vertices_552), (true, vertices_648), (true, vertices_208), (true, vertices_656), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_59) then 15 else
  if p.val = (false, vertices_267) then 0 else
  if p.val = (false, vertices_595) then 16 else
  if p.val = (false, vertices_323) then 1 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_425) then 21 else
  if p.val = (false, vertices_817) then 23 else
  if p.val = (true, vertices_202) then 17 else
  if p.val = (true, vertices_164) then 2 else
  if p.val = (true, vertices_292) then 3 else
  if p.val = (true, vertices_548) then 4 else
  if p.val = (true, vertices_196) then 5 else
  if p.val = (true, vertices_644) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_552) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_448) then 13 else
  0
cert_priority
cert_nodeAtPriority_23 267 323 164 292 548 196 644 152 536 552 648 208 656 448 59 595 202 837 425 817
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 5 6 202
cert_row_4 1 1 2 4 6 8 684 164 1
cert_row_4 2 1 3 5 6 8 724 196 1
cert_row_4 3 1 4 5 6 7 484 164 2
cert_rows
cert_pivot_2 0 2 3 1
cert_heightProof 4
cert_coverFacet 0 218
cert_cover_5 0 0 0 2 3 5 26 218 3
cert_coverFacet 1 458
cert_cover_5 1 0 0 2 5 7 202 458 3
cert_coverFacet 2 684
cert_cover_5 2 1 1 2 4 6 164 684 1
cert_coverFacet 3 724
cert_cover_5 3 2 1 3 5 6 196 724 1
cert_coverFacet 4 484
cert_cover_5 4 3 1 4 5 6 164 484 2
cert_coverFacet 5 804
cert_cover_2 5 4 1 7 8 292 804 3
cert_coverFacet 6 568
cert_cover_2 6 3 2 4 8 56 568 3
cert_coverFacet 7 664
cert_cover_2 7 3 2 6 8 152 664 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0089

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m15e10q1_0090.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0090

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 157, 281, 681, 817, 721, 110, 270, 326, 850, 738, 802, 284, 236, 468, 25, 41, 137, 265, 145, 273, 529, 289, 545, 641, 14, 70, 262, 42, 266, 98, 290, 546, 322, 578, 770, 28, 108, 140, 268, 148, 276, 196, 324, 280, 168, 208, 336, 592, 784, 224, 672, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_157, vertices_281, vertices_681, vertices_817, vertices_721, vertices_110, vertices_270, vertices_326, vertices_850, vertices_738, vertices_802, vertices_284, vertices_236, vertices_468] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_41, vertices_137, vertices_265, vertices_145, vertices_273, vertices_529, vertices_289, vertices_545, vertices_641, vertices_14, vertices_70, vertices_262, vertices_42, vertices_266, vertices_98, vertices_290, vertices_546, vertices_322, vertices_578, vertices_770, vertices_28, vertices_108, vertices_140, vertices_268, vertices_148, vertices_276, vertices_196, vertices_324, vertices_280, vertices_168, vertices_208, vertices_336, vertices_592, vertices_784, vertices_224, vertices_672, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_157), (false, vertices_281), (false, vertices_681), (false, vertices_817), (false, vertices_721), (true, vertices_14), (true, vertices_70), (true, vertices_262), (true, vertices_98), (true, vertices_546), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_108), (true, vertices_268), (true, vertices_276), (true, vertices_196), (true, vertices_324), (true, vertices_336), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 16 else
  if p.val = (false, vertices_157) then 18 else
  if p.val = (false, vertices_281) then 0 else
  if p.val = (false, vertices_681) then 21 else
  if p.val = (false, vertices_817) then 23 else
  if p.val = (false, vertices_721) then 24 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_322) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_108) then 19 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_276) then 10 else
  if p.val = (true, vertices_196) then 11 else
  if p.val = (true, vertices_324) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_224) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_281), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_108), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 4 5 108
cert_row_4 1 0 4 5 6 8 738 98 3
cert_row_4 2 0 3 5 7 8 850 322 1
cert_row_4 3 1 3 5 6 7 468 148 2
cert_rows
cert_pivot_2 2 4 0 1
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 0 0 1 2 4 14 110 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 326
cert_cover_2 2 1 0 5 7 70 326 3
cert_coverFacet 3 850
cert_cover_5 3 2 0 3 5 7 322 850 1
cert_coverFacet 4 738
cert_cover_5 4 1 0 4 5 6 98 738 3
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 236
cert_cover_5 7 0 1 2 4 6 108 236 3
cert_coverFacet 8 468
cert_cover_5 8 3 1 3 5 6 148 468 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0090

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m15e10q1_0091.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0091

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 397, 601, 153, 809, 465, 302, 230, 390, 626, 802, 450, 572, 156, 244, 25, 137, 265, 521, 81, 145, 321, 577, 385, 769, 38, 134, 262, 98, 290, 546, 194, 322, 578, 386, 770, 28, 44, 140, 268, 52, 148, 228, 388, 152, 536, 296, 552, 112, 560, 208, 592, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_397, vertices_601, vertices_153, vertices_809, vertices_465, vertices_302, vertices_230, vertices_390, vertices_626, vertices_802, vertices_450, vertices_572, vertices_156, vertices_244] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_137, vertices_265, vertices_521, vertices_81, vertices_145, vertices_321, vertices_577, vertices_385, vertices_769, vertices_38, vertices_134, vertices_262, vertices_98, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_28, vertices_44, vertices_140, vertices_268, vertices_52, vertices_148, vertices_228, vertices_388, vertices_152, vertices_536, vertices_296, vertices_552, vertices_112, vertices_560, vertices_208, vertices_592, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_397), (false, vertices_601), (false, vertices_153), (false, vertices_809), (false, vertices_465), (true, vertices_38), (true, vertices_134), (true, vertices_262), (true, vertices_98), (true, vertices_290), (true, vertices_546), (true, vertices_194), (true, vertices_386), (true, vertices_28), (true, vertices_44), (true, vertices_52), (true, vertices_148), (true, vertices_228), (true, vertices_112), (true, vertices_560)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_397) then 18 else
  if p.val = (false, vertices_601) then 21 else
  if p.val = (false, vertices_153) then 0 else
  if p.val = (false, vertices_809) then 22 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_98) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_194) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_44) then 10 else
  if p.val = (true, vertices_52) then 11 else
  if p.val = (true, vertices_148) then 12 else
  if p.val = (true, vertices_228) then 19 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_560) then 14 else
  0
cert_priority
cert_nodeAtPriority_65 153 2 38 1 134 3 262 98 290 546 194 386 28 44 52 148 112 560 835 397 228 601 809 465
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 4 5 6 228
cert_row_4 1 0 1 2 4 7 302 38 2
cert_row_4 2 0 3 4 5 8 626 98 1
cert_row_4 3 1 2 3 4 8 572 28 3
cert_rows
cert_pivot_2 6 7 0 1
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 1 0 1 2 4 38 302 2
cert_coverFacet 1 230
cert_cover_5 1 0 0 1 4 5 38 230 3
cert_coverFacet 2 390
cert_cover_2 2 1 0 6 7 134 390 3
cert_coverFacet 3 626
cert_cover_5 3 2 0 3 4 5 98 626 1
cert_coverFacet 4 802
cert_cover_2 4 4 0 7 8 290 802 3
cert_coverFacet 5 450
cert_cover_2 5 5 0 6 7 194 450 3
cert_coverFacet 6 572
cert_cover_5 6 3 1 2 3 4 28 572 3
cert_coverFacet 7 156
cert_cover_2 7 2 1 3 6 28 156 3
cert_coverFacet 8 244
cert_cover_5 8 0 1 3 4 5 52 244 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0091

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m15e10q1_0092.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0092

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [295, 519, 707, 387, 613, 361, 465, 398, 654, 572, 300, 120, 344, 920, 752, 7, 131, 259, 515, 37, 517, 97, 289, 193, 321, 577, 385, 142, 262, 518, 386, 642, 44, 268, 524, 292, 548, 56, 88, 280, 536, 104, 296, 328, 392, 648, 112, 560, 208, 336, 400, 656, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_295, vertices_519, vertices_707, vertices_387, vertices_613, vertices_361, vertices_465, vertices_398, vertices_654, vertices_572, vertices_300, vertices_120, vertices_344, vertices_920, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_7, vertices_131, vertices_259, vertices_515, vertices_37, vertices_517, vertices_97, vertices_289, vertices_193, vertices_321, vertices_577, vertices_385, vertices_142, vertices_262, vertices_518, vertices_386, vertices_642, vertices_44, vertices_268, vertices_524, vertices_292, vertices_548, vertices_56, vertices_88, vertices_280, vertices_536, vertices_104, vertices_296, vertices_328, vertices_392, vertices_648, vertices_112, vertices_560, vertices_208, vertices_336, vertices_400, vertices_656, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_295), (false, vertices_519), (false, vertices_707), (false, vertices_387), (false, vertices_613), (false, vertices_361), (false, vertices_465), (true, vertices_142), (true, vertices_44), (true, vertices_268), (true, vertices_524), (true, vertices_56), (true, vertices_88), (true, vertices_280), (true, vertices_536), (true, vertices_392), (true, vertices_648), (true, vertices_112), (true, vertices_560), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 18 20 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_295) then 15 else
  if p.val = (false, vertices_519) then 0 else
  if p.val = (false, vertices_707) then 16 else
  if p.val = (false, vertices_387) then 1 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_465) then 23 else
  if p.val = (true, vertices_142) then 17 else
  if p.val = (true, vertices_44) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_56) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_648) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_560) then 12 else
  if p.val = (true, vertices_656) then 13 else
  0
cert_priority
cert_nodeAtPriority_23 519 387 44 268 524 56 88 280 536 392 648 112 560 656 295 707 142 613 361 465
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 6 142
cert_row_4 1 1 2 3 4 8 572 44 2
cert_row_4 2 2 3 6 7 8 920 280 2
cert_row_4 3 3 4 5 6 8 752 112 3
cert_rows
cert_pivot_2 0 1 2 3
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 7 142 398 3
cert_coverFacet 1 654
cert_cover_5 1 0 0 1 2 8 142 654 3
cert_coverFacet 2 572
cert_cover_5 2 1 1 2 3 4 44 572 2
cert_coverFacet 3 300
cert_cover_2 3 2 1 4 7 44 300 3
cert_coverFacet 4 120
cert_cover_2 4 3 2 4 5 56 120 3
cert_coverFacet 5 344
cert_cover_2 5 3 2 5 7 88 344 3
cert_coverFacet 6 920
cert_cover_5 6 2 2 3 6 7 280 920 2
cert_coverFacet 7 752
cert_cover_5 7 3 3 4 5 6 112 752 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0092

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m15e10q1_0093.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0093

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 397, 357, 709, 777, 849, 614, 678, 602, 154, 370, 178, 436, 408, 792, 69, 133, 261, 137, 265, 521, 321, 577, 641, 769, 550, 26, 138, 522, 50, 82, 146, 98, 162, 578, 642, 100, 164, 292, 580, 388, 644, 152, 280, 536, 392, 776, 176, 304, 336, 592, 400, 784, 352]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_397, vertices_357, vertices_709, vertices_777, vertices_849, vertices_614, vertices_678, vertices_602, vertices_154, vertices_370, vertices_178, vertices_436, vertices_408, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_137, vertices_265, vertices_521, vertices_321, vertices_577, vertices_641, vertices_769, vertices_550, vertices_26, vertices_138, vertices_522, vertices_50, vertices_82, vertices_146, vertices_98, vertices_162, vertices_578, vertices_642, vertices_100, vertices_164, vertices_292, vertices_580, vertices_388, vertices_644, vertices_152, vertices_280, vertices_536, vertices_392, vertices_776, vertices_176, vertices_304, vertices_336, vertices_592, vertices_400, vertices_784, vertices_352] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_397), (false, vertices_357), (false, vertices_709), (false, vertices_777), (false, vertices_849), (true, vertices_550), (true, vertices_26), (true, vertices_50), (true, vertices_82), (true, vertices_146), (true, vertices_98), (true, vertices_162), (true, vertices_578), (true, vertices_164), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_176), (true, vertices_304), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 16 else
  if p.val = (false, vertices_397) then 19 else
  if p.val = (false, vertices_357) then 20 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (false, vertices_849) then 24 else
  if p.val = (true, vertices_550) then 17 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_82) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
cert_nodeAtPriority_19 0 777 1 26 50 82 146 98 162 578 164 152 280 536 176 304 400 651 550 397 357 709 849
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 8 602 26 3
cert_row_2 1 0 1 4 8 550
cert_row_4 2 0 3 4 5 7 370 50 3
cert_row_4 3 1 3 4 6 7 436 164 1
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_5 0 1 0 1 4 5 550 614 3
cert_coverFacet 1 678
cert_cover_5 1 1 0 1 4 6 550 678 3
cert_coverFacet 2 602
cert_cover_5 2 0 0 2 3 5 26 602 3
cert_coverFacet 3 154
cert_cover_2 3 2 0 3 6 26 154 3
cert_coverFacet 4 370
cert_cover_5 4 2 0 3 4 5 50 370 3
cert_coverFacet 5 178
cert_cover_2 5 3 0 4 6 50 178 3
cert_coverFacet 6 436
cert_cover_5 6 3 1 3 4 6 164 436 1
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 792
cert_cover_2 8 3 2 7 8 280 792 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0093

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m15e10q1_0094.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0094

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [155, 651, 613, 121, 841, 689, 406, 678, 774, 346, 778, 484, 836, 368, 432, 139, 25, 73, 521, 49, 145, 97, 545, 577, 641, 134, 262, 518, 26, 266, 522, 146, 274, 642, 770, 100, 164, 548, 324, 580, 388, 772, 88, 328, 776, 112, 176, 304, 336, 400, 352, 416, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_155, vertices_651, vertices_613, vertices_121, vertices_841, vertices_689, vertices_406, vertices_678, vertices_774, vertices_346, vertices_778, vertices_484, vertices_836, vertices_368, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_139, vertices_25, vertices_73, vertices_521, vertices_49, vertices_145, vertices_97, vertices_545, vertices_577, vertices_641, vertices_134, vertices_262, vertices_518, vertices_26, vertices_266, vertices_522, vertices_146, vertices_274, vertices_642, vertices_770, vertices_100, vertices_164, vertices_548, vertices_324, vertices_580, vertices_388, vertices_772, vertices_88, vertices_328, vertices_776, vertices_112, vertices_176, vertices_304, vertices_336, vertices_400, vertices_352, vertices_416, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_155), (false, vertices_651), (false, vertices_613), (false, vertices_121), (false, vertices_841), (false, vertices_689), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_266), (true, vertices_274), (true, vertices_770), (true, vertices_164), (true, vertices_324), (true, vertices_388), (true, vertices_772), (true, vertices_304), (true, vertices_336), (true, vertices_400), (true, vertices_352), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_155) then 16 else
  if p.val = (false, vertices_651) then 17 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_121) then 21 else
  if p.val = (false, vertices_841) then 22 else
  if p.val = (false, vertices_689) then 24 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_274) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_400) then 12 else
  if p.val = (true, vertices_352) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_155), by decide +kernel⟩
  | 17 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
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
cert_row_4 0 0 1 4 6 8 678 134 2
cert_row_4 1 0 2 3 5 7 346 26 3
cert_row_4 2 0 1 3 6 7 406 134 2
cert_row_4 3 1 4 5 6 7 484 100 3
cert_rows
cert_pivot_2 8 2 0 1
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 2 0 1 3 6 134 406 2
cert_coverFacet 1 678
cert_cover_5 1 0 0 1 4 6 134 678 2
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 346
cert_cover_5 3 1 0 2 3 5 26 346 3
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 484
cert_cover_5 5 3 1 4 5 6 100 484 3
cert_coverFacet 6 836
cert_cover_2 6 5 1 7 8 324 836 3
cert_coverFacet 7 368
cert_cover_2 7 4 3 5 7 112 368 3
cert_coverFacet 8 432
cert_cover_2 8 4 3 6 7 176 432 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0094

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m15e10q1_0095.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0095

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 709, 665, 361, 585, 465, 110, 590, 678, 538, 298, 786, 802, 484, 944, 25, 73, 265, 521, 145, 273, 193, 321, 577, 641, 78, 38, 518, 26, 42, 266, 522, 274, 530, 290, 546, 770, 100, 164, 196, 580, 644, 536, 104, 296, 584, 400, 656, 784, 352, 416, 672, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_709, vertices_665, vertices_361, vertices_585, vertices_465, vertices_110, vertices_590, vertices_678, vertices_538, vertices_298, vertices_786, vertices_802, vertices_484, vertices_944] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_265, vertices_521, vertices_145, vertices_273, vertices_193, vertices_321, vertices_577, vertices_641, vertices_78, vertices_38, vertices_518, vertices_26, vertices_42, vertices_266, vertices_522, vertices_274, vertices_530, vertices_290, vertices_546, vertices_770, vertices_100, vertices_164, vertices_196, vertices_580, vertices_644, vertices_536, vertices_104, vertices_296, vertices_584, vertices_400, vertices_656, vertices_784, vertices_352, vertices_416, vertices_672, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_709), (false, vertices_665), (false, vertices_361), (false, vertices_585), (false, vertices_465), (true, vertices_78), (true, vertices_38), (true, vertices_518), (true, vertices_42), (true, vertices_522), (true, vertices_530), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_100), (true, vertices_164), (true, vertices_784), (true, vertices_416), (true, vertices_672), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 16 else
  if p.val = (false, vertices_709) then 19 else
  if p.val = (false, vertices_665) then 21 else
  if p.val = (false, vertices_361) then 22 else
  if p.val = (false, vertices_585) then 0 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_164) then 10 else
  if p.val = (true, vertices_784) then 11 else
  if p.val = (true, vertices_416) then 12 else
  if p.val = (true, vertices_672) then 13 else
  if p.val = (true, vertices_800) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 585 38 518 42 522 530 290 546 770 100 164 784 416 672 800 283 78 709 665 361 465
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 1 4 6 8 678 38 3
cert_row_4 2 1 4 5 6 7 484 100 3
cert_row_4 3 3 4 6 7 8 944 400 1
cert_rows
cert_pivot_2 2 0 1 3
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 0 0 1 2 4 78 110 3
cert_coverFacet 1 590
cert_cover_5 1 0 0 1 2 8 78 590 3
cert_coverFacet 2 678
cert_cover_5 2 1 0 1 4 6 38 678 3
cert_coverFacet 3 538
cert_cover_2 3 2 0 3 8 26 538 3
cert_coverFacet 4 298
cert_cover_2 4 2 0 4 7 42 298 3
cert_coverFacet 5 786
cert_cover_2 5 3 0 7 8 274 786 3
cert_coverFacet 6 802
cert_cover_2 6 4 0 7 8 290 802 3
cert_coverFacet 7 484
cert_cover_5 7 2 1 4 5 6 100 484 3
cert_coverFacet 8 944
cert_cover_5 8 3 3 4 6 7 400 944 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0095

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m15e10q1_0096.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0096

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [155, 613, 345, 681, 585, 241, 334, 590, 806, 282, 650, 914, 372, 432, 928, 25, 73, 137, 521, 81, 145, 97, 161, 545, 577, 78, 262, 518, 26, 138, 266, 522, 146, 274, 642, 770, 100, 292, 548, 324, 580, 280, 328, 584, 648, 112, 176, 304, 336, 400, 416, 672, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_155, vertices_613, vertices_345, vertices_681, vertices_585, vertices_241, vertices_334, vertices_590, vertices_806, vertices_282, vertices_650, vertices_914, vertices_372, vertices_432, vertices_928] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_137, vertices_521, vertices_81, vertices_145, vertices_97, vertices_161, vertices_545, vertices_577, vertices_78, vertices_262, vertices_518, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_642, vertices_770, vertices_100, vertices_292, vertices_548, vertices_324, vertices_580, vertices_280, vertices_328, vertices_584, vertices_648, vertices_112, vertices_176, vertices_304, vertices_336, vertices_400, vertices_416, vertices_672, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_155), (false, vertices_613), (false, vertices_345), (false, vertices_681), (false, vertices_585), (false, vertices_241), (true, vertices_78), (true, vertices_262), (true, vertices_518), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_642), (true, vertices_770), (true, vertices_292), (true, vertices_324), (true, vertices_304), (true, vertices_400), (true, vertices_416), (true, vertices_800), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_155) then 16 else
  if p.val = (false, vertices_613) then 19 else
  if p.val = (false, vertices_345) then 21 else
  if p.val = (false, vertices_681) then 22 else
  if p.val = (false, vertices_585) then 0 else
  if p.val = (false, vertices_241) then 24 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_324) then 9 else
  if p.val = (true, vertices_304) then 10 else
  if p.val = (true, vertices_400) then 11 else
  if p.val = (true, vertices_416) then 12 else
  if p.val = (true, vertices_800) then 13 else
  if p.val = (true, vertices_896) then 14 else
  0
cert_priority
cert_nodeAtPriority_31 585 262 518 266 522 274 642 770 292 324 304 400 416 800 896 155 78 613 345 681 241
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 2 5 78
cert_row_4 1 0 3 6 7 8 914 146 3
cert_row_4 2 0 1 4 7 8 806 262 2
cert_row_4 3 1 3 4 5 7 372 100 1
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 334
cert_cover_5 0 0 0 1 2 7 78 334 3
cert_coverFacet 1 590
cert_cover_5 1 0 0 1 2 8 78 590 3
cert_coverFacet 2 806
cert_cover_5 2 2 0 1 4 7 262 806 2
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 650
cert_cover_2 4 2 0 6 8 138 650 3
cert_coverFacet 5 914
cert_cover_5 5 1 0 3 6 7 146 914 3
cert_coverFacet 6 372
cert_cover_5 6 3 1 3 4 5 100 372 1
cert_coverFacet 7 432
cert_cover_2 7 4 3 6 7 176 432 3
cert_coverFacet 8 928
cert_cover_2 8 6 4 7 8 416 928 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0096

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m15e10q1_0097.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0097

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 157, 789, 709, 401, 481, 286, 782, 58, 554, 370, 738, 684, 184, 432, 21, 133, 517, 145, 273, 193, 321, 577, 385, 769, 270, 26, 42, 522, 50, 274, 98, 546, 322, 578, 770, 28, 140, 524, 276, 644, 772, 56, 152, 168, 552, 176, 304, 400, 224, 352, 416, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_157, vertices_789, vertices_709, vertices_401, vertices_481, vertices_286, vertices_782, vertices_58, vertices_554, vertices_370, vertices_738, vertices_684, vertices_184, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_517, vertices_145, vertices_273, vertices_193, vertices_321, vertices_577, vertices_385, vertices_769, vertices_270, vertices_26, vertices_42, vertices_522, vertices_50, vertices_274, vertices_98, vertices_546, vertices_322, vertices_578, vertices_770, vertices_28, vertices_140, vertices_524, vertices_276, vertices_644, vertices_772, vertices_56, vertices_152, vertices_168, vertices_552, vertices_176, vertices_304, vertices_400, vertices_224, vertices_352, vertices_416, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_157), (false, vertices_789), (false, vertices_709), (false, vertices_401), (false, vertices_481), (true, vertices_270), (true, vertices_26), (true, vertices_42), (true, vertices_522), (true, vertices_50), (true, vertices_274), (true, vertices_98), (true, vertices_546), (true, vertices_524), (true, vertices_56), (true, vertices_168), (true, vertices_552), (true, vertices_176), (true, vertices_304), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 16 else
  if p.val = (false, vertices_157) then 19 else
  if p.val = (false, vertices_789) then 20 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_401) then 0 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_270) then 17 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_98) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_672) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_401), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_270), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
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
cert_row_4 0 0 3 4 5 7 370 50 3
cert_row_2 1 0 1 2 7 270
cert_row_4 2 0 4 5 6 8 738 98 3
cert_row_4 3 1 2 4 6 8 684 140 2
cert_rows
cert_pivot_2 3 7 0 1
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 1 0 1 2 3 270 286 3
cert_coverFacet 1 782
cert_cover_5 1 1 0 1 2 8 270 782 3
cert_coverFacet 2 58
cert_cover_2 2 2 0 3 4 26 58 3
cert_coverFacet 3 554
cert_cover_2 3 2 0 4 8 42 554 3
cert_coverFacet 4 370
cert_cover_5 4 0 0 3 4 5 50 370 3
cert_coverFacet 5 738
cert_cover_5 5 2 0 4 5 6 98 738 3
cert_coverFacet 6 684
cert_cover_5 6 3 1 2 4 6 140 684 2
cert_coverFacet 7 184
cert_cover_2 7 3 2 4 6 56 184 3
cert_coverFacet 8 432
cert_cover_2 8 4 3 6 7 176 432 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0097

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m15e10q1_0098.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0098

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 109, 597, 677, 337, 401, 481, 174, 654, 298, 778, 434, 850, 844, 360, 37, 69, 517, 81, 145, 273, 529, 97, 161, 321, 385, 641, 142, 42, 266, 522, 146, 274, 530, 162, 290, 642, 770, 44, 76, 524, 164, 580, 644, 104, 296, 328, 776, 336, 592, 400, 352, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_109, vertices_597, vertices_677, vertices_337, vertices_401, vertices_481, vertices_174, vertices_654, vertices_298, vertices_778, vertices_434, vertices_850, vertices_844, vertices_360] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_517, vertices_81, vertices_145, vertices_273, vertices_529, vertices_97, vertices_161, vertices_321, vertices_385, vertices_641, vertices_142, vertices_42, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_642, vertices_770, vertices_44, vertices_76, vertices_524, vertices_164, vertices_580, vertices_644, vertices_104, vertices_296, vertices_328, vertices_776, vertices_336, vertices_592, vertices_400, vertices_352, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_109), (false, vertices_597), (false, vertices_677), (false, vertices_337), (false, vertices_401), (false, vertices_481), (true, vertices_142), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_274), (true, vertices_162), (true, vertices_290), (true, vertices_770), (true, vertices_524), (true, vertices_296), (true, vertices_328), (true, vertices_776), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 22 23 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 15 else
  if p.val = (false, vertices_109) then 18 else
  if p.val = (false, vertices_597) then 19 else
  if p.val = (false, vertices_677) then 20 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (false, vertices_401) then 1 else
  if p.val = (false, vertices_481) then 24 else
  if p.val = (true, vertices_142) then 16 else
  if p.val = (true, vertices_42) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_290) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_832) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_337), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_401), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_142), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_109), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
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
cert_row_4 0 0 3 4 6 7 434 146 2
cert_row_2 1 0 1 2 6 142
cert_row_4 2 0 3 5 7 8 850 274 2
cert_row_4 3 1 2 5 7 8 844 76 3
cert_rows
cert_pivot_2 4 6 0 1
cert_heightProof 4
cert_coverFacet 0 174
cert_cover_5 0 1 0 1 2 4 142 174 3
cert_coverFacet 1 654
cert_cover_5 1 1 0 1 2 8 142 654 3
cert_coverFacet 2 298
cert_cover_2 2 2 0 4 7 42 298 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 434
cert_cover_5 4 0 0 3 4 6 146 434 2
cert_coverFacet 5 850
cert_cover_5 5 2 0 3 5 7 274 850 2
cert_coverFacet 6 844
cert_cover_5 6 3 1 2 5 7 76 844 3
cert_coverFacet 7 360
cert_cover_2 7 4 2 5 7 104 360 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0098

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m15e10q1_0099.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0099

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [539, 173, 525, 661, 345, 361, 241, 782, 282, 722, 338, 866, 300, 740, 804, 13, 133, 517, 25, 41, 329, 521, 81, 145, 529, 97, 161, 26, 266, 522, 82, 274, 530, 322, 578, 770, 44, 268, 524, 164, 292, 548, 644, 772, 280, 296, 208, 336, 656, 224, 352, 608, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_539, vertices_173, vertices_525, vertices_661, vertices_345, vertices_361, vertices_241, vertices_782, vertices_282, vertices_722, vertices_338, vertices_866, vertices_300, vertices_740, vertices_804] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_517, vertices_25, vertices_41, vertices_329, vertices_521, vertices_81, vertices_145, vertices_529, vertices_97, vertices_161, vertices_26, vertices_266, vertices_522, vertices_82, vertices_274, vertices_530, vertices_322, vertices_578, vertices_770, vertices_44, vertices_268, vertices_524, vertices_164, vertices_292, vertices_548, vertices_644, vertices_772, vertices_280, vertices_296, vertices_208, vertices_336, vertices_656, vertices_224, vertices_352, vertices_608, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_539), (false, vertices_173), (false, vertices_525), (false, vertices_661), (false, vertices_345), (false, vertices_361), (false, vertices_241), (true, vertices_266), (true, vertices_82), (true, vertices_274), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_268), (true, vertices_292), (true, vertices_548), (true, vertices_772), (true, vertices_608), (true, vertices_800), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 16 19 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_539) then 15 else
  if p.val = (false, vertices_173) then 17 else
  if p.val = (false, vertices_525) then 0 else
  if p.val = (false, vertices_661) then 18 else
  if p.val = (false, vertices_345) then 20 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_241) then 23 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_322) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_770) then 6 else
  if p.val = (true, vertices_268) then 7 else
  if p.val = (true, vertices_292) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_772) then 10 else
  if p.val = (true, vertices_608) then 11 else
  if p.val = (true, vertices_800) then 12 else
  if p.val = (true, vertices_704) then 13 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_525), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 14 => Sum.inl 0
  | 15 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 16 => Sum.inl 1
  | 17 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 22 => Sum.inl 3
  | 23 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 24 => Sum.inl 4
  | 25 => Sum.inl 5
  | 26 => Sum.inl 6
  | 27 => Sum.inl 7
  | 28 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 266 1
cert_row_4 1 0 3 5 6 8 722 82 3
cert_row_4 2 0 4 5 7 8 866 322 1
cert_row_4 3 1 4 5 6 8 740 164 2
cert_rows
cert_pivot_2 2 3 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 266 782 1
cert_coverFacet 1 282
cert_cover_2 1 2 0 3 7 26 282 3
cert_coverFacet 2 722
cert_cover_5 2 1 0 3 5 6 82 722 3
cert_coverFacet 3 338
cert_cover_2 3 3 0 5 7 82 338 3
cert_coverFacet 4 866
cert_cover_5 4 2 0 4 5 7 322 866 1
cert_coverFacet 5 300
cert_cover_2 5 2 1 4 7 44 300 3
cert_coverFacet 6 740
cert_cover_5 6 3 1 4 5 6 164 740 2
cert_coverFacet 7 804
cert_cover_2 7 4 1 7 8 292 804 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0099

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m15e10q1_0100.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0100

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 661, 841, 465, 737, 30, 46, 534, 678, 282, 618, 778, 316, 436, 488, 145, 273, 529, 193, 321, 577, 641, 769, 14, 22, 38, 518, 26, 42, 266, 522, 274, 530, 546, 770, 28, 44, 308, 148, 532, 164, 644, 280, 104, 296, 328, 584, 776, 400, 224, 608, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_661, vertices_841, vertices_465, vertices_737, vertices_30, vertices_46, vertices_534, vertices_678, vertices_282, vertices_618, vertices_778, vertices_316, vertices_436, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_145, vertices_273, vertices_529, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_14, vertices_22, vertices_38, vertices_518, vertices_26, vertices_42, vertices_266, vertices_522, vertices_274, vertices_530, vertices_546, vertices_770, vertices_28, vertices_44, vertices_308, vertices_148, vertices_532, vertices_164, vertices_644, vertices_280, vertices_104, vertices_296, vertices_328, vertices_584, vertices_776, vertices_400, vertices_224, vertices_608, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_661), (false, vertices_841), (false, vertices_465), (false, vertices_737), (true, vertices_14), (true, vertices_22), (true, vertices_38), (true, vertices_518), (true, vertices_26), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_546), (true, vertices_28), (true, vertices_44), (true, vertices_308), (true, vertices_164), (true, vertices_280), (true, vertices_104), (true, vertices_296), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 21 23 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 17 else
  if p.val = (false, vertices_661) then 19 else
  if p.val = (false, vertices_841) then 22 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (false, vertices_737) then 26 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_42) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_522) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_44) then 10 else
  if p.val = (true, vertices_308) then 20 else
  if p.val = (true, vertices_164) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_104) then 13 else
  if p.val = (true, vertices_296) then 14 else
  if p.val = (true, vertices_416) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_308), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_841), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 3 4 7 308
cert_row_4 1 0 1 4 6 8 678 38 3
cert_row_4 2 0 2 4 5 8 618 42 3
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 3 1 0 2
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 46
cert_cover_2 1 1 0 2 4 14 46 3
cert_coverFacet 2 534
cert_cover_2 2 1 0 3 8 22 534 3
cert_coverFacet 3 678
cert_cover_5 3 1 0 1 4 6 38 678 3
cert_coverFacet 4 282
cert_cover_2 4 2 0 3 7 26 282 3
cert_coverFacet 5 618
cert_cover_5 5 2 0 2 4 5 42 618 3
cert_coverFacet 6 778
cert_cover_2 6 2 0 7 8 266 778 3
cert_coverFacet 7 316
cert_cover_5 7 0 1 2 3 4 28 316 3
cert_coverFacet 8 436
cert_cover_5 8 0 1 3 4 6 308 436 3
cert_coverFacet 9 488
cert_cover_5 9 3 2 4 5 6 104 488 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0100

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m15e10q1_0101.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0101

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [787, 837, 569, 369, 737, 286, 142, 710, 774, 538, 682, 412, 484, 184, 432, 49, 273, 529, 97, 545, 321, 577, 769, 14, 134, 262, 518, 26, 138, 522, 274, 530, 642, 770, 284, 140, 196, 324, 580, 388, 772, 56, 152, 536, 168, 552, 176, 304, 400, 224, 352, 416, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_787, vertices_837, vertices_569, vertices_369, vertices_737, vertices_286, vertices_142, vertices_710, vertices_774, vertices_538, vertices_682, vertices_412, vertices_484, vertices_184, vertices_432] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_273, vertices_529, vertices_97, vertices_545, vertices_321, vertices_577, vertices_769, vertices_14, vertices_134, vertices_262, vertices_518, vertices_26, vertices_138, vertices_522, vertices_274, vertices_530, vertices_642, vertices_770, vertices_284, vertices_140, vertices_196, vertices_324, vertices_580, vertices_388, vertices_772, vertices_56, vertices_152, vertices_536, vertices_168, vertices_552, vertices_176, vertices_304, vertices_400, vertices_224, vertices_352, vertices_416, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_787), (false, vertices_837), (false, vertices_569), (false, vertices_369), (false, vertices_737), (true, vertices_14), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_26), (true, vertices_138), (true, vertices_522), (true, vertices_642), (true, vertices_284), (true, vertices_140), (true, vertices_196), (true, vertices_388), (true, vertices_152), (true, vertices_168), (true, vertices_176), (true, vertices_400), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 21 23 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_787) then 17 else
  if p.val = (false, vertices_837) then 19 else
  if p.val = (false, vertices_569) then 22 else
  if p.val = (false, vertices_369) then 24 else
  if p.val = (false, vertices_737) then 26 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_138) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_284) then 20 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_388) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_416) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_787), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_284), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_569), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_369), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 3 7 284
cert_row_4 1 0 2 4 6 8 682 138 2
cert_row_4 2 0 1 5 6 8 710 134 2
cert_row_4 3 1 4 5 6 7 484 196 1
cert_rows
cert_pivot_2 3 2 0 1
cert_heightProof 4
cert_coverFacet 0 286
cert_cover_5 0 0 0 1 2 3 14 286 3
cert_coverFacet 1 142
cert_cover_2 1 1 0 2 6 14 142 3
cert_coverFacet 2 710
cert_cover_5 2 2 0 1 5 6 134 710 2
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 538
cert_cover_2 4 2 0 3 8 26 538 3
cert_coverFacet 5 682
cert_cover_5 5 1 0 2 4 6 138 682 2
cert_coverFacet 6 412
cert_cover_5 6 0 1 2 3 6 284 412 3
cert_coverFacet 7 484
cert_cover_5 7 3 1 4 5 6 196 484 1
cert_coverFacet 8 184
cert_cover_2 8 3 2 4 6 56 184 3
cert_coverFacet 9 432
cert_cover_2 9 4 3 6 7 176 432 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0101

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m15e10q1_0102.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0102

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 661, 217, 369, 785, 737, 110, 270, 678, 774, 346, 354, 412, 236, 788, 81, 145, 273, 529, 97, 289, 545, 193, 641, 769, 14, 38, 262, 518, 74, 266, 98, 290, 546, 322, 770, 108, 140, 268, 148, 276, 532, 164, 644, 772, 88, 152, 280, 200, 336, 784, 224, 352, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_661, vertices_217, vertices_369, vertices_785, vertices_737, vertices_110, vertices_270, vertices_678, vertices_774, vertices_346, vertices_354, vertices_412, vertices_236, vertices_788] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_145, vertices_273, vertices_529, vertices_97, vertices_289, vertices_545, vertices_193, vertices_641, vertices_769, vertices_14, vertices_38, vertices_262, vertices_518, vertices_74, vertices_266, vertices_98, vertices_290, vertices_546, vertices_322, vertices_770, vertices_108, vertices_140, vertices_268, vertices_148, vertices_276, vertices_532, vertices_164, vertices_644, vertices_772, vertices_88, vertices_152, vertices_280, vertices_200, vertices_336, vertices_784, vertices_224, vertices_352, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_661), (false, vertices_217), (false, vertices_369), (false, vertices_785), (false, vertices_737), (true, vertices_14), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_74), (true, vertices_266), (true, vertices_98), (true, vertices_322), (true, vertices_108), (true, vertices_140), (true, vertices_268), (true, vertices_276), (true, vertices_164), (true, vertices_772), (true, vertices_280)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 16 else
  if p.val = (false, vertices_661) then 18 else
  if p.val = (false, vertices_217) then 21 else
  if p.val = (false, vertices_369) then 23 else
  if p.val = (false, vertices_785) then 0 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_74) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_98) then 7 else
  if p.val = (true, vertices_322) then 8 else
  if p.val = (true, vertices_108) then 19 else
  if p.val = (true, vertices_140) then 9 else
  if p.val = (true, vertices_268) then 10 else
  if p.val = (true, vertices_276) then 11 else
  if p.val = (true, vertices_164) then 12 else
  if p.val = (true, vertices_772) then 13 else
  if p.val = (true, vertices_280) then 14 else
  0
cert_priority
cert_nodeAtPriority_9 0 785 1 14 38 262 518 74 266 98 322 140 268 276 164 772 280 803 661 108 217 369 737
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 38 3
cert_row_2 1 1 2 4 5 108
cert_row_4 2 0 2 3 5 7 346 74 2
cert_row_4 3 1 2 3 6 7 412 140 2
cert_rows
cert_pivot_2 8 4 0 1
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 1 0 1 2 4 14 110 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 678
cert_cover_5 2 0 0 1 4 6 38 678 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 346
cert_cover_5 4 2 0 2 3 5 74 346 2
cert_coverFacet 5 354
cert_cover_2 5 4 0 5 7 98 354 3
cert_coverFacet 6 412
cert_cover_5 6 3 1 2 3 6 140 412 2
cert_coverFacet 7 236
cert_cover_5 7 1 1 2 4 6 108 236 3
cert_coverFacet 8 788
cert_cover_2 8 3 1 7 8 276 788 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0102

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m15e10q1_0103.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0103

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 805, 121, 793, 305, 737, 406, 678, 774, 458, 778, 706, 244, 308, 472, 25, 73, 521, 49, 273, 97, 289, 545, 577, 769, 134, 262, 518, 74, 266, 522, 194, 578, 386, 642, 770, 52, 148, 276, 164, 292, 548, 772, 88, 280, 456, 776, 112, 304, 208, 400, 224, 672, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_805, vertices_121, vertices_793, vertices_305, vertices_737, vertices_406, vertices_678, vertices_774, vertices_458, vertices_778, vertices_706, vertices_244, vertices_308, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_521, vertices_49, vertices_273, vertices_97, vertices_289, vertices_545, vertices_577, vertices_769, vertices_134, vertices_262, vertices_518, vertices_74, vertices_266, vertices_522, vertices_194, vertices_578, vertices_386, vertices_642, vertices_770, vertices_52, vertices_148, vertices_276, vertices_164, vertices_292, vertices_548, vertices_772, vertices_88, vertices_280, vertices_456, vertices_776, vertices_112, vertices_304, vertices_208, vertices_400, vertices_224, vertices_672, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_805), (false, vertices_121), (false, vertices_793), (false, vertices_305), (false, vertices_737), (true, vertices_134), (true, vertices_262), (true, vertices_518), (true, vertices_266), (true, vertices_194), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_52), (true, vertices_148), (true, vertices_276), (true, vertices_164), (true, vertices_456), (true, vertices_208), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 19 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 16 else
  if p.val = (false, vertices_805) then 18 else
  if p.val = (false, vertices_121) then 20 else
  if p.val = (false, vertices_793) then 21 else
  if p.val = (false, vertices_305) then 0 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_134) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_194) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_148) then 10 else
  if p.val = (true, vertices_276) then 11 else
  if p.val = (true, vertices_164) then 12 else
  if p.val = (true, vertices_456) then 22 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_305), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_121), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_456), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inl 4
  | 25 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 26 => Sum.inl 5
  | 27 => Sum.inl 6
  | 28 => Sum.inl 7
  | 29 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 5 6 7 456
cert_row_4 1 0 1 3 6 7 406 134 2
cert_row_4 2 0 1 4 6 8 678 134 2
cert_row_4 3 1 3 4 5 6 244 52 3
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 1 0 1 3 6 134 406 2
cert_coverFacet 1 678
cert_cover_5 1 2 0 1 4 6 134 678 2
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 458
cert_cover_5 3 0 0 2 5 6 74 458 3
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 706
cert_cover_2 5 5 0 6 8 194 706 3
cert_coverFacet 6 244
cert_cover_5 6 3 1 3 4 5 52 244 3
cert_coverFacet 7 308
cert_cover_2 7 3 1 4 7 52 308 3
cert_coverFacet 8 472
cert_cover_5 8 0 2 3 5 6 88 472 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0103

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m15e10q1_0104.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0104

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [283, 173, 301, 217, 849, 481, 270, 526, 678, 294, 538, 786, 866, 668, 752, 45, 25, 137, 265, 81, 273, 161, 289, 193, 321, 14, 38, 262, 518, 26, 266, 522, 274, 530, 290, 546, 770, 140, 268, 524, 164, 292, 644, 152, 536, 208, 592, 656, 784, 224, 352, 608, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_283, vertices_173, vertices_301, vertices_217, vertices_849, vertices_481, vertices_270, vertices_526, vertices_678, vertices_294, vertices_538, vertices_786, vertices_866, vertices_668, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_45, vertices_25, vertices_137, vertices_265, vertices_81, vertices_273, vertices_161, vertices_289, vertices_193, vertices_321, vertices_14, vertices_38, vertices_262, vertices_518, vertices_26, vertices_266, vertices_522, vertices_274, vertices_530, vertices_290, vertices_546, vertices_770, vertices_140, vertices_268, vertices_524, vertices_164, vertices_292, vertices_644, vertices_152, vertices_536, vertices_208, vertices_592, vertices_656, vertices_784, vertices_224, vertices_352, vertices_608, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_283), (false, vertices_173), (false, vertices_301), (false, vertices_217), (false, vertices_849), (false, vertices_481), (true, vertices_14), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_522), (true, vertices_530), (true, vertices_290), (true, vertices_546), (true, vertices_770), (true, vertices_524), (true, vertices_644), (true, vertices_536), (true, vertices_656), (true, vertices_608), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_283) then 16 else
  if p.val = (false, vertices_173) then 18 else
  if p.val = (false, vertices_301) then 19 else
  if p.val = (false, vertices_217) then 21 else
  if p.val = (false, vertices_849) then 23 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_536) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_608) then 13 else
  if p.val = (true, vertices_672) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_283), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
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
cert_row_4 0 0 4 5 7 8 866 290 2
cert_row_4 1 0 1 4 6 8 678 38 3
cert_row_4 2 1 2 3 6 8 668 140 2
cert_row_4 3 3 4 5 6 8 752 208 1
cert_rows
cert_pivot_2 7 0 1 3
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 678
cert_cover_5 2 1 0 1 4 6 38 678 3
cert_coverFacet 3 294
cert_cover_2 3 1 0 4 7 38 294 3
cert_coverFacet 4 538
cert_cover_2 4 2 0 3 8 26 538 3
cert_coverFacet 5 786
cert_cover_2 5 3 0 7 8 274 786 3
cert_coverFacet 6 866
cert_cover_5 6 0 0 4 5 7 290 866 2
cert_coverFacet 7 668
cert_cover_5 7 2 1 2 3 6 140 668 2
cert_coverFacet 8 752
cert_cover_5 8 3 3 4 5 6 208 752 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0104

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m15e10q1_0105.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0105

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 181, 341, 677, 841, 625, 398, 646, 186, 618, 778, 674, 404, 376, 408, 21, 165, 261, 517, 49, 81, 545, 321, 577, 769, 134, 262, 518, 42, 138, 266, 522, 162, 546, 642, 770, 148, 276, 388, 644, 56, 152, 280, 104, 328, 584, 392, 776, 112, 176, 336, 400, 608, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_181, vertices_341, vertices_677, vertices_841, vertices_625, vertices_398, vertices_646, vertices_186, vertices_618, vertices_778, vertices_674, vertices_404, vertices_376, vertices_408] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_165, vertices_261, vertices_517, vertices_49, vertices_81, vertices_545, vertices_321, vertices_577, vertices_769, vertices_134, vertices_262, vertices_518, vertices_42, vertices_138, vertices_266, vertices_522, vertices_162, vertices_546, vertices_642, vertices_770, vertices_148, vertices_276, vertices_388, vertices_644, vertices_56, vertices_152, vertices_280, vertices_104, vertices_328, vertices_584, vertices_392, vertices_776, vertices_112, vertices_176, vertices_336, vertices_400, vertices_608, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_181), (false, vertices_341), (false, vertices_677), (false, vertices_841), (false, vertices_625), (true, vertices_134), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_162), (true, vertices_546), (true, vertices_642), (true, vertices_388), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_104), (true, vertices_392), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 16 else
  if p.val = (false, vertices_181) then 18 else
  if p.val = (false, vertices_341) then 19 else
  if p.val = (false, vertices_677) then 20 else
  if p.val = (false, vertices_841) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_388) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_104) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
cert_nodeAtPriority_68 0 134 1 42 138 266 522 162 546 642 388 56 152 280 104 392 400 775 181 341 677 841 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 6 7 398 134 2
cert_row_4 1 0 2 3 4 6 186 42 2
cert_row_4 2 0 2 4 5 8 618 42 3
cert_row_4 3 2 3 4 5 7 376 56 3
cert_rows
cert_pivot_2 1 6 0 2
cert_heightProof 4
cert_coverFacet 0 398
cert_cover_5 0 0 0 1 2 6 134 398 2
cert_coverFacet 1 646
cert_cover_2 1 1 0 6 8 134 646 3
cert_coverFacet 2 186
cert_cover_5 2 1 0 2 3 4 42 186 2
cert_coverFacet 3 618
cert_cover_5 3 2 0 2 4 5 42 618 3
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 674
cert_cover_2 5 4 0 6 8 162 674 3
cert_coverFacet 6 404
cert_cover_2 6 3 1 6 7 148 404 3
cert_coverFacet 7 376
cert_cover_5 7 3 2 3 4 5 56 376 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0105

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m15e10q1_0106.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0106

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 781, 613, 453, 721, 558, 58, 154, 394, 778, 626, 658, 316, 372, 472, 69, 261, 517, 193, 577, 385, 641, 769, 26, 42, 138, 266, 522, 50, 146, 530, 546, 386, 642, 770, 44, 268, 524, 308, 100, 548, 324, 56, 152, 280, 392, 776, 112, 208, 336, 592, 656, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_781, vertices_613, vertices_453, vertices_721, vertices_558, vertices_58, vertices_154, vertices_394, vertices_778, vertices_626, vertices_658, vertices_316, vertices_372, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_193, vertices_577, vertices_385, vertices_641, vertices_769, vertices_26, vertices_42, vertices_138, vertices_266, vertices_522, vertices_50, vertices_146, vertices_530, vertices_546, vertices_386, vertices_642, vertices_770, vertices_44, vertices_268, vertices_524, vertices_308, vertices_100, vertices_548, vertices_324, vertices_56, vertices_152, vertices_280, vertices_392, vertices_776, vertices_112, vertices_208, vertices_336, vertices_592, vertices_656, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_781), (false, vertices_613), (false, vertices_453), (false, vertices_721), (true, vertices_26), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_146), (true, vertices_530), (true, vertices_546), (true, vertices_44), (true, vertices_308), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_392), (true, vertices_112), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 18 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 17 else
  if p.val = (false, vertices_781) then 19 else
  if p.val = (false, vertices_613) then 21 else
  if p.val = (false, vertices_453) then 22 else
  if p.val = (false, vertices_721) then 25 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_50) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_530) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_308) then 23 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_280) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_112) then 14 else
  if p.val = (true, vertices_336) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 18 => Sum.inl 2
  | 19 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_613), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 23 => Sum.inr ⟨(true, vertices_308), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 3 5 6 7 472 152 2
cert_row_2 1 1 3 4 7 308
cert_row_4 2 0 1 2 4 8 558 42 1
cert_row_4 3 0 3 4 5 8 626 50 3
cert_rows
cert_pivot_2 6 7 1 0
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 2 0 1 2 4 42 558 1
cert_coverFacet 1 58
cert_cover_2 1 2 0 3 4 26 58 3
cert_coverFacet 2 154
cert_cover_2 2 2 0 3 6 26 154 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 626
cert_cover_5 5 3 0 3 4 5 50 626 3
cert_coverFacet 6 658
cert_cover_2 6 3 0 6 8 146 658 3
cert_coverFacet 7 316
cert_cover_5 7 1 1 2 3 4 44 316 2
cert_coverFacet 8 372
cert_cover_5 8 1 1 3 4 5 308 372 3
cert_coverFacet 9 472
cert_cover_5 9 0 2 3 5 6 152 472 2
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0106

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m15e10q1_0107.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0107

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [355, 661, 217, 817, 337, 737, 110, 270, 678, 774, 346, 802, 412, 236, 788, 81, 145, 273, 529, 97, 289, 545, 193, 321, 641, 14, 38, 262, 518, 74, 266, 98, 290, 546, 322, 770, 108, 140, 268, 148, 276, 532, 164, 644, 772, 88, 152, 280, 200, 336, 784, 224, 672, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_355, vertices_661, vertices_217, vertices_817, vertices_337, vertices_737, vertices_110, vertices_270, vertices_678, vertices_774, vertices_346, vertices_802, vertices_412, vertices_236, vertices_788] (by decide +kernel)
  polygons := literalFinset [vertices_81, vertices_145, vertices_273, vertices_529, vertices_97, vertices_289, vertices_545, vertices_193, vertices_321, vertices_641, vertices_14, vertices_38, vertices_262, vertices_518, vertices_74, vertices_266, vertices_98, vertices_290, vertices_546, vertices_322, vertices_770, vertices_108, vertices_140, vertices_268, vertices_148, vertices_276, vertices_532, vertices_164, vertices_644, vertices_772, vertices_88, vertices_152, vertices_280, vertices_200, vertices_336, vertices_784, vertices_224, vertices_672, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_355), (false, vertices_661), (false, vertices_217), (false, vertices_817), (false, vertices_337), (false, vertices_737), (true, vertices_14), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_74), (true, vertices_266), (true, vertices_546), (true, vertices_770), (true, vertices_108), (true, vertices_140), (true, vertices_268), (true, vertices_276), (true, vertices_164), (true, vertices_772), (true, vertices_280)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 22 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_355) then 16 else
  if p.val = (false, vertices_661) then 18 else
  if p.val = (false, vertices_217) then 21 else
  if p.val = (false, vertices_817) then 23 else
  if p.val = (false, vertices_337) then 0 else
  if p.val = (false, vertices_737) then 25 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_74) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_108) then 19 else
  if p.val = (true, vertices_140) then 9 else
  if p.val = (true, vertices_268) then 10 else
  if p.val = (true, vertices_276) then 11 else
  if p.val = (true, vertices_164) then 12 else
  if p.val = (true, vertices_772) then 13 else
  if p.val = (true, vertices_280) then 14 else
  0
cert_priority
cert_nodeAtPriority_9 0 337 1 14 38 262 518 74 266 546 770 140 268 276 164 772 280 355 661 108 217 817 737
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 8 678 38 3
cert_row_2 1 1 2 4 5 108
cert_row_4 2 0 2 3 5 7 346 74 2
cert_row_4 3 1 2 3 6 7 412 140 2
cert_rows
cert_pivot_2 8 4 0 1
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 1 0 1 2 4 14 110 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 678
cert_cover_5 2 0 0 1 4 6 38 678 3
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 346
cert_cover_5 4 2 0 2 3 5 74 346 2
cert_coverFacet 5 802
cert_cover_2 5 4 0 7 8 290 802 3
cert_coverFacet 6 412
cert_cover_5 6 3 1 2 3 6 140 412 2
cert_coverFacet 7 236
cert_cover_5 7 1 1 2 4 6 108 236 3
cert_coverFacet 8 788
cert_cover_2 8 3 1 7 8 276 788 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0107

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m15e10q1_0108.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0108

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [403, 109, 301, 213, 789, 457, 806, 618, 298, 394, 650, 658, 786, 628, 728, 45, 21, 69, 261, 73, 265, 145, 273, 193, 385, 42, 138, 266, 522, 146, 274, 530, 290, 546, 386, 642, 770, 84, 532, 100, 292, 548, 772, 104, 296, 200, 584, 392, 648, 208, 592, 656, 784, 608]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_403, vertices_109, vertices_301, vertices_213, vertices_789, vertices_457, vertices_806, vertices_618, vertices_298, vertices_394, vertices_650, vertices_658, vertices_786, vertices_628, vertices_728] (by decide +kernel)
  polygons := literalFinset [vertices_45, vertices_21, vertices_69, vertices_261, vertices_73, vertices_265, vertices_145, vertices_273, vertices_193, vertices_385, vertices_42, vertices_138, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_290, vertices_546, vertices_386, vertices_642, vertices_770, vertices_84, vertices_532, vertices_100, vertices_292, vertices_548, vertices_772, vertices_104, vertices_296, vertices_200, vertices_584, vertices_392, vertices_648, vertices_208, vertices_592, vertices_656, vertices_784, vertices_608] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_403), (false, vertices_109), (false, vertices_301), (false, vertices_213), (false, vertices_789), (false, vertices_457), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_530), (true, vertices_290), (true, vertices_546), (true, vertices_642), (true, vertices_770), (true, vertices_548), (true, vertices_584), (true, vertices_648), (true, vertices_592), (true, vertices_656), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 21 17 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_403) then 16 else
  if p.val = (false, vertices_109) then 18 else
  if p.val = (false, vertices_301) then 19 else
  if p.val = (false, vertices_213) then 22 else
  if p.val = (false, vertices_789) then 23 else
  if p.val = (false, vertices_457) then 20 else
  if p.val = (true, vertices_42) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_290) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_648) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_656) then 13 else
  if p.val = (true, vertices_608) then 14 else
  0
cert_priority
cert_nodeAtPriority_36 0 42 2 138 1 266 522 530 290 546 642 770 548 584 648 592 656 608 403 109 301 457 213 789
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 7 8 806 290 1
cert_row_4 1 0 2 4 5 8 618 42 3
cert_row_4 2 1 3 4 5 8 628 84 2
cert_row_4 3 2 3 5 6 8 728 200 1
cert_rows
cert_pivot_2 7 0 1 2
cert_heightProof 4
cert_coverFacet 0 806
cert_cover_5 0 0 0 1 4 7 290 806 1
cert_coverFacet 1 618
cert_cover_5 1 1 0 2 4 5 42 618 3
cert_coverFacet 2 298
cert_cover_2 2 2 0 4 7 42 298 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 650
cert_cover_2 4 2 0 6 8 138 650 3
cert_coverFacet 5 658
cert_cover_2 5 3 0 6 8 146 658 3
cert_coverFacet 6 786
cert_cover_2 6 3 0 7 8 274 786 3
cert_coverFacet 7 628
cert_cover_5 7 2 1 3 4 5 84 628 2
cert_coverFacet 8 728
cert_cover_5 8 3 2 3 5 6 200 728 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0108

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m15e10q1_0109.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0109

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 589, 789, 229, 421, 457, 310, 666, 394, 242, 786, 418, 628, 712, 720, 165, 69, 261, 517, 73, 265, 521, 193, 385, 769, 138, 266, 522, 50, 146, 274, 530, 162, 290, 386, 770, 52, 276, 532, 100, 292, 580, 200, 584, 392, 648, 112, 208, 592, 656, 784, 224, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_589, vertices_789, vertices_229, vertices_421, vertices_457, vertices_310, vertices_666, vertices_394, vertices_242, vertices_786, vertices_418, vertices_628, vertices_712, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_165, vertices_69, vertices_261, vertices_517, vertices_73, vertices_265, vertices_521, vertices_193, vertices_385, vertices_769, vertices_138, vertices_266, vertices_522, vertices_50, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_386, vertices_770, vertices_52, vertices_276, vertices_532, vertices_100, vertices_292, vertices_580, vertices_200, vertices_584, vertices_392, vertices_648, vertices_112, vertices_208, vertices_592, vertices_656, vertices_784, vertices_224, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_589), (false, vertices_789), (false, vertices_229), (false, vertices_421), (false, vertices_457), (true, vertices_138), (true, vertices_50), (true, vertices_146), (true, vertices_274), (true, vertices_530), (true, vertices_162), (true, vertices_290), (true, vertices_386), (true, vertices_52), (true, vertices_648), (true, vertices_112), (true, vertices_208), (true, vertices_592), (true, vertices_656), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 20 17 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 16 else
  if p.val = (false, vertices_589) then 18 else
  if p.val = (false, vertices_789) then 21 else
  if p.val = (false, vertices_229) then 22 else
  if p.val = (false, vertices_421) then 23 else
  if p.val = (false, vertices_457) then 19 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_50) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_274) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_386) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_648) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_208) then 11 else
  if p.val = (true, vertices_592) then 12 else
  if p.val = (true, vertices_656) then 13 else
  if p.val = (true, vertices_704) then 14 else
  0
cert_priority
cert_nodeAtPriority_42 138 1 50 2 146 274 530 162 290 386 52 648 112 208 592 656 704 779 589 457 789 229 421
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 7 310 50 1
cert_row_4 1 0 2 3 6 8 666 138 2
cert_row_4 2 0 3 4 5 6 242 50 3
cert_row_4 3 1 3 4 5 8 628 52 3
cert_rows
cert_pivot_2 7 2 0 1
cert_heightProof 4
cert_coverFacet 0 310
cert_cover_5 0 0 0 1 3 4 50 310 1
cert_coverFacet 1 666
cert_cover_5 1 1 0 2 3 6 138 666 2
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 242
cert_cover_5 3 2 0 3 4 5 50 242 3
cert_coverFacet 4 786
cert_cover_2 4 3 0 7 8 274 786 3
cert_coverFacet 5 418
cert_cover_2 5 4 0 6 7 162 418 3
cert_coverFacet 6 628
cert_cover_5 6 3 1 3 4 5 52 628 3
cert_coverFacet 7 712
cert_cover_2 7 5 2 6 8 200 712 3
cert_coverFacet 8 720
cert_cover_2 8 5 3 6 8 208 720 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0109

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m15e10q1_0110.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0110

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [539, 557, 597, 357, 217, 233, 902, 154, 682, 850, 402, 420, 676, 836, 496, 37, 69, 517, 25, 41, 201, 521, 81, 529, 97, 26, 138, 522, 146, 274, 530, 386, 642, 770, 164, 292, 548, 324, 580, 388, 644, 772, 152, 168, 552, 208, 336, 592, 400, 224, 352, 416, 672, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_539, vertices_557, vertices_597, vertices_357, vertices_217, vertices_233, vertices_902, vertices_154, vertices_682, vertices_850, vertices_402, vertices_420, vertices_676, vertices_836, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_517, vertices_25, vertices_41, vertices_201, vertices_521, vertices_81, vertices_529, vertices_97, vertices_26, vertices_138, vertices_522, vertices_146, vertices_274, vertices_530, vertices_386, vertices_642, vertices_770, vertices_164, vertices_292, vertices_548, vertices_324, vertices_580, vertices_388, vertices_644, vertices_772, vertices_152, vertices_168, vertices_552, vertices_208, vertices_336, vertices_592, vertices_400, vertices_224, vertices_352, vertices_416, vertices_672, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_539), (false, vertices_557), (false, vertices_597), (false, vertices_357), (false, vertices_217), (false, vertices_233), (true, vertices_138), (true, vertices_146), (true, vertices_274), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_164), (true, vertices_388), (true, vertices_644), (true, vertices_772), (true, vertices_336), (true, vertices_400), (true, vertices_416), (true, vertices_672), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 21 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_539) then 16 else
  if p.val = (false, vertices_557) then 18 else
  if p.val = (false, vertices_597) then 19 else
  if p.val = (false, vertices_357) then 20 else
  if p.val = (false, vertices_217) then 22 else
  if p.val = (false, vertices_233) then 23 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_146) then 1 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_164) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_400) then 11 else
  if p.val = (true, vertices_416) then 12 else
  if p.val = (true, vertices_672) then 13 else
  if p.val = (true, vertices_832) then 14 else
  0
cert_priority
cert_nodeAtPriority_36 0 138 1 146 2 274 386 642 770 164 388 644 772 336 400 416 672 832 539 557 597 357 217 233
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 8 902 386 1
cert_row_4 1 0 2 4 6 8 682 138 2
cert_row_4 2 0 3 5 7 8 850 274 2
cert_row_4 3 3 4 5 6 7 496 208 1
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 0 0 1 6 7 386 902 1
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 682
cert_cover_5 2 1 0 2 4 6 138 682 2
cert_coverFacet 3 850
cert_cover_5 3 2 0 3 5 7 274 850 2
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 420
cert_cover_2 5 4 1 6 7 164 420 3
cert_coverFacet 6 676
cert_cover_2 6 4 1 6 8 164 676 3
cert_coverFacet 7 836
cert_cover_2 7 5 1 7 8 324 836 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 208 496 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0110

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m15e10q1_0111.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0111

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [271, 527, 357, 677, 841, 625, 662, 422, 602, 154, 394, 248, 456, 688, 480, 15, 37, 261, 517, 265, 521, 97, 545, 321, 577, 134, 262, 518, 26, 138, 266, 522, 146, 530, 386, 164, 292, 644, 88, 152, 200, 328, 584, 392, 112, 176, 560, 592, 656, 224, 352, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_271, vertices_527, vertices_357, vertices_677, vertices_841, vertices_625, vertices_662, vertices_422, vertices_602, vertices_154, vertices_394, vertices_248, vertices_456, vertices_688, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_15, vertices_37, vertices_261, vertices_517, vertices_265, vertices_521, vertices_97, vertices_545, vertices_321, vertices_577, vertices_134, vertices_262, vertices_518, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_530, vertices_386, vertices_164, vertices_292, vertices_644, vertices_88, vertices_152, vertices_200, vertices_328, vertices_584, vertices_392, vertices_112, vertices_176, vertices_560, vertices_592, vertices_656, vertices_224, vertices_352, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_271), (false, vertices_527), (false, vertices_357), (false, vertices_677), (false, vertices_841), (false, vertices_625), (true, vertices_134), (true, vertices_26), (true, vertices_138), (true, vertices_146), (true, vertices_530), (true, vertices_386), (true, vertices_88), (true, vertices_152), (true, vertices_200), (true, vertices_392), (true, vertices_176), (true, vertices_656), (true, vertices_224), (true, vertices_416), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 21 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_271) then 16 else
  if p.val = (false, vertices_527) then 17 else
  if p.val = (false, vertices_357) then 19 else
  if p.val = (false, vertices_677) then 20 else
  if p.val = (false, vertices_841) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (true, vertices_134) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_152) then 7 else
  if p.val = (true, vertices_200) then 8 else
  if p.val = (true, vertices_392) then 9 else
  if p.val = (true, vertices_176) then 10 else
  if p.val = (true, vertices_656) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_416) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
cert_nodeAtPriority_62 134 26 138 146 530 386 88 152 200 392 176 656 224 416 448 271 527 357 677 841 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 6 7 422 134 2
cert_row_4 1 0 1 3 6 8 662 134 2
cert_row_4 2 0 2 3 5 8 602 26 3
cert_row_4 3 2 3 4 5 6 248 88 2
cert_rows
cert_pivot_2 7 1 0 2
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 1 0 1 3 6 134 662 2
cert_coverFacet 1 422
cert_cover_5 1 0 0 1 4 6 134 422 2
cert_coverFacet 2 602
cert_cover_5 2 2 0 2 3 5 26 602 3
cert_coverFacet 3 154
cert_cover_2 3 2 0 3 6 26 154 3
cert_coverFacet 4 394
cert_cover_2 4 2 0 6 7 138 394 3
cert_coverFacet 5 248
cert_cover_5 5 3 2 3 4 5 88 248 2
cert_coverFacet 6 456
cert_cover_2 6 5 2 6 7 200 456 3
cert_coverFacet 7 688
cert_cover_2 7 4 3 6 8 176 688 3
cert_coverFacet 8 480
cert_cover_2 8 5 4 6 7 224 480 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0111

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m15e10q1_0112.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0112

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [595, 397, 661, 837, 209, 481, 334, 590, 570, 426, 114, 354, 684, 240, 688, 133, 261, 517, 81, 145, 529, 193, 321, 577, 385, 78, 42, 266, 522, 50, 82, 530, 98, 290, 322, 578, 140, 268, 524, 324, 580, 644, 168, 552, 392, 112, 176, 560, 208, 656, 224, 352, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_595, vertices_397, vertices_661, vertices_837, vertices_209, vertices_481, vertices_334, vertices_590, vertices_570, vertices_426, vertices_114, vertices_354, vertices_684, vertices_240, vertices_688] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_81, vertices_145, vertices_529, vertices_193, vertices_321, vertices_577, vertices_385, vertices_78, vertices_42, vertices_266, vertices_522, vertices_50, vertices_82, vertices_530, vertices_98, vertices_290, vertices_322, vertices_578, vertices_140, vertices_268, vertices_524, vertices_324, vertices_580, vertices_644, vertices_168, vertices_552, vertices_392, vertices_112, vertices_176, vertices_560, vertices_208, vertices_656, vertices_224, vertices_352, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_595), (false, vertices_397), (false, vertices_661), (false, vertices_837), (false, vertices_209), (false, vertices_481), (true, vertices_78), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_98), (true, vertices_290), (true, vertices_322), (true, vertices_524), (true, vertices_168), (true, vertices_552), (true, vertices_112), (true, vertices_176), (true, vertices_560), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 18 22 23 24 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_595) then 16 else
  if p.val = (false, vertices_397) then 19 else
  if p.val = (false, vertices_661) then 20 else
  if p.val = (false, vertices_837) then 21 else
  if p.val = (false, vertices_209) then 0 else
  if p.val = (false, vertices_481) then 25 else
  if p.val = (true, vertices_78) then 17 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_98) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_322) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_168) then 9 else
  if p.val = (true, vertices_552) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_672) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_209), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_672), by decide +kernel⟩
  | 15 => Sum.inl 0
  | 16 => Sum.inr ⟨(false, vertices_595), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_78), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_397), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
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
cert_coverFacet 4 114
cert_cover_2 4 3 0 4 5 50 114 3
cert_coverFacet 5 354
cert_cover_2 5 4 0 5 7 98 354 3
cert_coverFacet 6 684
cert_cover_5 6 3 1 2 4 6 140 684 2
cert_coverFacet 7 240
cert_cover_2 7 4 3 5 6 112 240 3
cert_coverFacet 8 688
cert_cover_2 8 4 3 6 8 176 688 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0112

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m15e10q1_0113.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0113

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [835, 661, 793, 465, 737, 542, 46, 678, 362, 778, 610, 284, 236, 460, 404, 145, 273, 529, 193, 321, 577, 641, 769, 14, 38, 518, 42, 266, 522, 98, 546, 322, 578, 770, 28, 44, 204, 268, 148, 276, 532, 164, 388, 644, 280, 536, 104, 328, 776, 400, 224, 608, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_835, vertices_661, vertices_793, vertices_465, vertices_737, vertices_542, vertices_46, vertices_678, vertices_362, vertices_778, vertices_610, vertices_284, vertices_236, vertices_460, vertices_404] (by decide +kernel)
  polygons := literalFinset [vertices_145, vertices_273, vertices_529, vertices_193, vertices_321, vertices_577, vertices_641, vertices_769, vertices_14, vertices_38, vertices_518, vertices_42, vertices_266, vertices_522, vertices_98, vertices_546, vertices_322, vertices_578, vertices_770, vertices_28, vertices_44, vertices_204, vertices_268, vertices_148, vertices_276, vertices_532, vertices_164, vertices_388, vertices_644, vertices_280, vertices_536, vertices_104, vertices_328, vertices_776, vertices_400, vertices_224, vertices_608, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_835), (false, vertices_661), (false, vertices_793), (false, vertices_465), (false, vertices_737), (true, vertices_14), (true, vertices_38), (true, vertices_518), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_98), (true, vertices_546), (true, vertices_28), (true, vertices_44), (true, vertices_204), (true, vertices_268), (true, vertices_276), (true, vertices_164), (true, vertices_388), (true, vertices_104), (true, vertices_328)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 18 21 23 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_835) then 17 else
  if p.val = (false, vertices_661) then 19 else
  if p.val = (false, vertices_793) then 22 else
  if p.val = (false, vertices_465) then 24 else
  if p.val = (false, vertices_737) then 26 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_98) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_28) then 8 else
  if p.val = (true, vertices_44) then 9 else
  if p.val = (true, vertices_204) then 20 else
  if p.val = (true, vertices_268) then 10 else
  if p.val = (true, vertices_276) then 11 else
  if p.val = (true, vertices_164) then 12 else
  if p.val = (true, vertices_388) then 13 else
  if p.val = (true, vertices_104) then 14 else
  if p.val = (true, vertices_328) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_835), by decide +kernel⟩
  | 18 => Sum.inl 1
  | 19 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_465), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 8 542 14 3
cert_row_4 1 0 1 4 6 8 678 38 3
cert_row_2 2 1 2 5 6 204
cert_row_4 3 0 2 4 5 7 362 42 3
cert_rows
cert_pivot_2 3 8 1 0
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 0 0 1 2 3 14 542 3
cert_coverFacet 1 46
cert_cover_2 1 1 0 2 4 14 46 3
cert_coverFacet 2 678
cert_cover_5 2 1 0 1 4 6 38 678 3
cert_coverFacet 3 362
cert_cover_5 3 3 0 2 4 5 42 362 3
cert_coverFacet 4 778
cert_cover_2 4 2 0 7 8 266 778 3
cert_coverFacet 5 610
cert_cover_2 5 4 0 5 8 98 610 3
cert_coverFacet 6 284
cert_cover_2 6 2 1 3 7 28 284 3
cert_coverFacet 7 236
cert_cover_5 7 2 1 2 4 5 44 236 3
cert_coverFacet 8 460
cert_cover_5 8 2 1 2 5 7 204 460 3
cert_coverFacet 9 404
cert_cover_2 9 3 1 6 7 148 404 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0113

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m15e10q1_0114.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0114

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 397, 213, 837, 777, 625, 657, 422, 362, 618, 394, 690, 372, 180, 840, 69, 133, 261, 137, 265, 521, 81, 145, 529, 577, 641, 769, 106, 138, 266, 522, 162, 290, 546, 386, 642, 52, 84, 148, 164, 292, 324, 388, 328, 584, 392, 776, 112, 176, 560, 656, 352, 608, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_397, vertices_213, vertices_837, vertices_777, vertices_625, vertices_657, vertices_422, vertices_362, vertices_618, vertices_394, vertices_690, vertices_372, vertices_180, vertices_840] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_133, vertices_261, vertices_137, vertices_265, vertices_521, vertices_81, vertices_145, vertices_529, vertices_577, vertices_641, vertices_769, vertices_106, vertices_138, vertices_266, vertices_522, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_52, vertices_84, vertices_148, vertices_164, vertices_292, vertices_324, vertices_388, vertices_328, vertices_584, vertices_392, vertices_776, vertices_112, vertices_176, vertices_560, vertices_656, vertices_352, vertices_608, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_397), (false, vertices_213), (false, vertices_837), (false, vertices_777), (false, vertices_625), (false, vertices_657), (true, vertices_106), (true, vertices_266), (true, vertices_162), (true, vertices_290), (true, vertices_546), (true, vertices_386), (true, vertices_52), (true, vertices_164), (true, vertices_292), (true, vertices_328), (true, vertices_584), (true, vertices_176), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 14 17 21 22 24 25 26 27 28
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 15 else
  if p.val = (false, vertices_397) then 18 else
  if p.val = (false, vertices_213) then 19 else
  if p.val = (false, vertices_837) then 20 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (false, vertices_625) then 23 else
  if p.val = (false, vertices_657) then 1 else
  if p.val = (true, vertices_106) then 16 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_162) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_164) then 8 else
  if p.val = (true, vertices_292) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_176) then 12 else
  if p.val = (true, vertices_352) then 13 else
  0
cert_priority
cert_nodeAtPriority_15 0 777 1 657 266 162 290 546 386 52 164 292 328 584 176 352 651 106 397 213 837 625
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 4 5 106
cert_row_4 1 0 3 4 6 8 690 162 1
cert_row_4 2 0 1 4 6 7 422 162 1
cert_row_4 3 1 3 4 5 7 372 52 3
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 422
cert_cover_5 0 2 0 1 4 6 162 422 1
cert_coverFacet 1 362
cert_cover_5 1 0 0 2 4 7 106 362 3
cert_coverFacet 2 618
cert_cover_5 2 0 0 2 4 8 106 618 3
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 690
cert_cover_5 4 1 0 3 4 6 162 690 1
cert_coverFacet 5 372
cert_cover_5 5 3 1 3 4 5 52 372 3
cert_coverFacet 6 180
cert_cover_2 6 3 1 4 6 52 180 3
cert_coverFacet 7 840
cert_cover_2 7 5 2 7 8 328 840 3
cert_coveringFacets_7
cert_coveringProof_2
cert_certificate 4 8
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0114

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m15e10q1_0115.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0115

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [143, 527, 789, 421, 681, 865, 214, 534, 618, 202, 850, 404, 472, 360, 424, 15, 133, 261, 517, 137, 521, 161, 289, 545, 769, 22, 134, 518, 74, 138, 522, 82, 530, 194, 578, 148, 276, 532, 388, 104, 168, 296, 552, 200, 328, 392, 208, 336, 400, 784, 352, 608, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_143, vertices_527, vertices_789, vertices_421, vertices_681, vertices_865, vertices_214, vertices_534, vertices_618, vertices_202, vertices_850, vertices_404, vertices_472, vertices_360, vertices_424] (by decide +kernel)
  polygons := literalFinset [vertices_15, vertices_133, vertices_261, vertices_517, vertices_137, vertices_521, vertices_161, vertices_289, vertices_545, vertices_769, vertices_22, vertices_134, vertices_518, vertices_74, vertices_138, vertices_522, vertices_82, vertices_530, vertices_194, vertices_578, vertices_148, vertices_276, vertices_532, vertices_388, vertices_104, vertices_168, vertices_296, vertices_552, vertices_200, vertices_328, vertices_392, vertices_208, vertices_336, vertices_400, vertices_784, vertices_352, vertices_608, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_143), (false, vertices_527), (false, vertices_789), (false, vertices_421), (false, vertices_681), (false, vertices_865), (true, vertices_22), (true, vertices_74), (true, vertices_82), (true, vertices_530), (true, vertices_194), (true, vertices_578), (true, vertices_148), (true, vertices_104), (true, vertices_296), (true, vertices_200), (true, vertices_328), (true, vertices_392), (true, vertices_208), (true, vertices_336), (true, vertices_400)] (by decide +kernel)
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
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_578) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_104) then 7 else
  if p.val = (true, vertices_296) then 8 else
  if p.val = (true, vertices_200) then 9 else
  if p.val = (true, vertices_328) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_400) then 14 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
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
cert_row_4 0 0 1 3 5 6 214 22 3
cert_row_4 1 0 2 4 5 8 618 74 2
cert_row_4 2 0 3 5 7 8 850 82 3
cert_row_4 3 2 3 5 6 7 472 200 1
cert_rows
cert_pivot_2 1 4 0 2
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 5 22 214 3
cert_coverFacet 1 534
cert_cover_2 1 1 0 3 8 22 534 3
cert_coverFacet 2 618
cert_cover_5 2 1 0 2 4 5 74 618 2
cert_coverFacet 3 202
cert_cover_2 3 2 0 5 6 74 202 3
cert_coverFacet 4 850
cert_cover_5 4 2 0 3 5 7 82 850 3
cert_coverFacet 5 404
cert_cover_2 5 3 1 6 7 148 404 3
cert_coverFacet 6 472
cert_cover_5 6 3 2 3 5 6 200 472 1
cert_coverFacet 7 360
cert_cover_2 7 4 2 5 7 104 360 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0115

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m15e10q1_0116.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0116

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [307, 781, 789, 361, 713, 625, 406, 562, 658, 738, 418, 668, 204, 332, 484, 773, 73, 265, 521, 49, 273, 529, 97, 289, 577, 50, 146, 274, 530, 162, 290, 546, 386, 642, 76, 140, 268, 524, 148, 276, 532, 196, 324, 388, 200, 328, 648, 560, 656, 224, 352, 608, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_781, vertices_789, vertices_361, vertices_713, vertices_625, vertices_406, vertices_562, vertices_658, vertices_738, vertices_418, vertices_668, vertices_204, vertices_332, vertices_484] (by decide +kernel)
  polygons := literalFinset [vertices_773, vertices_73, vertices_265, vertices_521, vertices_49, vertices_273, vertices_529, vertices_97, vertices_289, vertices_577, vertices_50, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_546, vertices_386, vertices_642, vertices_76, vertices_140, vertices_268, vertices_524, vertices_148, vertices_276, vertices_532, vertices_196, vertices_324, vertices_388, vertices_200, vertices_328, vertices_648, vertices_560, vertices_656, vertices_224, vertices_352, vertices_608, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_781), (false, vertices_789), (false, vertices_361), (false, vertices_713), (false, vertices_625), (true, vertices_146), (true, vertices_530), (true, vertices_162), (true, vertices_546), (true, vertices_386), (true, vertices_642), (true, vertices_76), (true, vertices_140), (true, vertices_148), (true, vertices_196), (true, vertices_324), (true, vertices_388), (true, vertices_656), (true, vertices_224), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 17 20 23 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 16 else
  if p.val = (false, vertices_781) then 18 else
  if p.val = (false, vertices_789) then 19 else
  if p.val = (false, vertices_361) then 21 else
  if p.val = (false, vertices_713) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (true, vertices_146) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_386) then 4 else
  if p.val = (true, vertices_642) then 5 else
  if p.val = (true, vertices_76) then 6 else
  if p.val = (true, vertices_140) then 7 else
  if p.val = (true, vertices_148) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_324) then 10 else
  if p.val = (true, vertices_388) then 11 else
  if p.val = (true, vertices_656) then 12 else
  if p.val = (true, vertices_224) then 13 else
  if p.val = (true, vertices_416) then 14 else
  0
cert_priority
cert_nodeAtPriority_52 146 1 530 2 162 546 386 642 76 140 148 196 324 388 656 224 416 307 781 789 361 713 625
cert_priority_injective
cert_incidenceProof
cert_row_4 0 1 2 3 6 8 668 140 2
cert_row_4 1 0 1 3 6 7 406 146 1
cert_row_4 2 0 4 5 6 8 738 162 2
cert_row_4 3 1 4 5 6 7 484 196 1
cert_rows
cert_pivot_2 2 3 0 1
cert_heightProof 4
cert_coverFacet 0 406
cert_cover_5 0 1 0 1 3 6 146 406 1
cert_coverFacet 1 562
cert_cover_2 1 3 0 4 8 50 562 3
cert_coverFacet 2 658
cert_cover_2 2 3 0 6 8 146 658 3
cert_coverFacet 3 738
cert_cover_5 3 2 0 4 5 6 162 738 2
cert_coverFacet 4 418
cert_cover_2 4 4 0 6 7 162 418 3
cert_coverFacet 5 668
cert_cover_5 5 0 1 2 3 6 140 668 2
cert_coverFacet 6 204
cert_cover_2 6 2 1 5 6 76 204 3
cert_coverFacet 7 332
cert_cover_2 7 2 1 5 7 76 332 3
cert_coverFacet 8 484
cert_cover_5 8 3 1 4 5 6 196 484 1
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0116

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m15e10q1_0117.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0117

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 653, 309, 597, 421, 793, 614, 682, 778, 850, 226, 450, 116, 676, 496, 21, 293, 133, 517, 137, 265, 521, 273, 529, 385, 138, 266, 522, 98, 162, 546, 194, 322, 578, 386, 770, 52, 84, 100, 164, 548, 580, 644, 648, 776, 112, 304, 336, 592, 784, 224, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_653, vertices_309, vertices_597, vertices_421, vertices_793, vertices_614, vertices_682, vertices_778, vertices_850, vertices_226, vertices_450, vertices_116, vertices_676, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_293, vertices_133, vertices_517, vertices_137, vertices_265, vertices_521, vertices_273, vertices_529, vertices_385, vertices_138, vertices_266, vertices_522, vertices_98, vertices_162, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_770, vertices_52, vertices_84, vertices_100, vertices_164, vertices_548, vertices_580, vertices_644, vertices_648, vertices_776, vertices_112, vertices_304, vertices_336, vertices_592, vertices_784, vertices_224, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_653), (false, vertices_309), (false, vertices_597), (false, vertices_421), (false, vertices_793), (true, vertices_522), (true, vertices_98), (true, vertices_162), (true, vertices_546), (true, vertices_194), (true, vertices_322), (true, vertices_578), (true, vertices_770), (true, vertices_100), (true, vertices_548), (true, vertices_112), (true, vertices_336), (true, vertices_224), (true, vertices_672), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 15 20 17 24 25 26 27 28 29
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 16 else
  if p.val = (false, vertices_653) then 18 else
  if p.val = (false, vertices_309) then 21 else
  if p.val = (false, vertices_597) then 22 else
  if p.val = (false, vertices_421) then 23 else
  if p.val = (false, vertices_793) then 19 else
  if p.val = (true, vertices_522) then 0 else
  if p.val = (true, vertices_98) then 1 else
  if p.val = (true, vertices_162) then 2 else
  if p.val = (true, vertices_546) then 3 else
  if p.val = (true, vertices_194) then 4 else
  if p.val = (true, vertices_322) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_100) then 8 else
  if p.val = (true, vertices_548) then 9 else
  if p.val = (true, vertices_112) then 10 else
  if p.val = (true, vertices_336) then 11 else
  if p.val = (true, vertices_224) then 12 else
  if p.val = (true, vertices_672) then 13 else
  if p.val = (true, vertices_448) then 14 else
  0
cert_priority
cert_nodeAtPriority_42 522 1 98 2 162 546 194 322 578 770 100 548 112 336 224 672 448 395 653 793 309 597 421
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 5 8 614 98 1
cert_row_4 1 0 2 4 6 8 682 138 2
cert_row_4 2 0 3 5 7 8 850 322 1
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 614
cert_cover_5 0 0 0 1 4 5 98 614 1
cert_coverFacet 1 682
cert_cover_5 1 1 0 2 4 6 138 682 2
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 850
cert_cover_5 3 2 0 3 5 7 322 850 1
cert_coverFacet 4 226
cert_cover_2 4 4 0 5 6 98 226 3
cert_coverFacet 5 450
cert_cover_2 5 5 0 6 7 194 450 3
cert_coverFacet 6 116
cert_cover_2 6 3 1 4 5 52 116 3
cert_coverFacet 7 676
cert_cover_2 7 4 1 6 8 164 676 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 112 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0117

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m15e10q1_0118.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0118

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 421, 837, 809, 689, 590, 342, 406, 570, 90, 658, 184, 472, 424, 840, 133, 261, 517, 161, 289, 545, 641, 769, 278, 70, 134, 518, 26, 74, 522, 82, 146, 530, 642, 324, 580, 388, 56, 88, 152, 168, 296, 552, 328, 584, 392, 776, 176, 560, 336, 400, 656, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_421, vertices_837, vertices_809, vertices_689, vertices_590, vertices_342, vertices_406, vertices_570, vertices_90, vertices_658, vertices_184, vertices_472, vertices_424, vertices_840] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_161, vertices_289, vertices_545, vertices_641, vertices_769, vertices_278, vertices_70, vertices_134, vertices_518, vertices_26, vertices_74, vertices_522, vertices_82, vertices_146, vertices_530, vertices_642, vertices_324, vertices_580, vertices_388, vertices_56, vertices_88, vertices_152, vertices_168, vertices_296, vertices_552, vertices_328, vertices_584, vertices_392, vertices_776, vertices_176, vertices_560, vertices_336, vertices_400, vertices_656, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_421), (false, vertices_837), (false, vertices_809), (false, vertices_689), (true, vertices_278), (true, vertices_70), (true, vertices_26), (true, vertices_74), (true, vertices_522), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_56), (true, vertices_88), (true, vertices_152), (true, vertices_168), (true, vertices_328), (true, vertices_584), (true, vertices_392), (true, vertices_336), (true, vertices_400)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 17 else
  if p.val = (false, vertices_421) then 20 else
  if p.val = (false, vertices_837) then 21 else
  if p.val = (false, vertices_809) then 23 else
  if p.val = (false, vertices_689) then 25 else
  if p.val = (true, vertices_278) then 18 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_88) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_400) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_278), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
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
cert_row_4 0 0 2 3 4 8 570 26 3
cert_row_4 1 0 1 2 5 8 590 70 2
cert_row_2 2 0 1 3 7 278
cert_row_4 3 2 3 5 6 7 472 88 3
cert_rows
cert_pivot_2 4 8 0 2
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 1 0 1 2 5 70 590 2
cert_coverFacet 1 342
cert_cover_5 1 2 0 1 3 5 278 342 3
cert_coverFacet 2 406
cert_cover_5 2 2 0 1 3 6 278 406 3
cert_coverFacet 3 570
cert_cover_5 3 0 0 2 3 4 26 570 3
cert_coverFacet 4 90
cert_cover_2 4 2 0 3 5 26 90 3
cert_coverFacet 5 658
cert_cover_2 5 3 0 6 8 146 658 3
cert_coverFacet 6 184
cert_cover_2 6 3 2 4 6 56 184 3
cert_coverFacet 7 472
cert_cover_5 7 3 2 3 5 6 88 472 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coverFacet 9 840
cert_cover_2 9 5 2 7 8 328 840 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0118

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_2703 : Certifies 2703 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0089.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2704 : Certifies 2704 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0090.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2705 : Certifies 2705 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0091.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2706 : Certifies 2706 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0092.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2707 : Certifies 2707 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0093.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2708 : Certifies 2708 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0094.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2709 : Certifies 2709 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0095.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2710 : Certifies 2710 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0096.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2711 : Certifies 2711 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0097.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2712 : Certifies 2712 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0098.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2713 : Certifies 2713 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0099.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2714 : Certifies 2714 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0100.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2715 : Certifies 2715 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0101.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2716 : Certifies 2716 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0102.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2717 : Certifies 2717 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0103.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2718 : Certifies 2718 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0104.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2719 : Certifies 2719 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0105.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2720 : Certifies 2720 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0106.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2721 : Certifies 2721 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0107.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2722 : Certifies 2722 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0108.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2723 : Certifies 2723 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0109.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2724 : Certifies 2724 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0110.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2725 : Certifies 2725 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0111.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2726 : Certifies 2726 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0112.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2727 : Certifies 2727 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0113.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2728 : Certifies 2728 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0114.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2729 : Certifies 2729 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0115.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2730 : Certifies 2730 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0116.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2731 : Certifies 2731 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0117.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_2732 : Certifies 2732 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m15e10q1_0118.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B089 (j : Fin 30) :
    Certifies (2703 + j.val) := by
  fin_cases j
  · exact projection_2703
  · exact projection_2704
  · exact projection_2705
  · exact projection_2706
  · exact projection_2707
  · exact projection_2708
  · exact projection_2709
  · exact projection_2710
  · exact projection_2711
  · exact projection_2712
  · exact projection_2713
  · exact projection_2714
  · exact projection_2715
  · exact projection_2716
  · exact projection_2717
  · exact projection_2718
  · exact projection_2719
  · exact projection_2720
  · exact projection_2721
  · exact projection_2722
  · exact projection_2723
  · exact projection_2724
  · exact projection_2725
  · exact projection_2726
  · exact projection_2727
  · exact projection_2728
  · exact projection_2729
  · exact projection_2730
  · exact projection_2731
  · exact projection_2732

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
