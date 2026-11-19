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
/- Source: ProjectionCertificates/R_m16e10q1_0073.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0073

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [587, 789, 421, 709, 217, 537, 401, 302, 678, 774, 794, 106, 738, 120, 312, 496, 133, 261, 517, 25, 73, 521, 145, 273, 529, 193, 577, 385, 38, 262, 518, 42, 74, 266, 522, 98, 674, 578, 770, 164, 292, 644, 772, 56, 88, 280, 536, 104, 296, 112, 304, 208, 400, 784, 224, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_587, vertices_789, vertices_421, vertices_709, vertices_217, vertices_537, vertices_401, vertices_302, vertices_678, vertices_774, vertices_794, vertices_106, vertices_738, vertices_120, vertices_312, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_25, vertices_73, vertices_521, vertices_145, vertices_273, vertices_529, vertices_193, vertices_577, vertices_385, vertices_38, vertices_262, vertices_518, vertices_42, vertices_74, vertices_266, vertices_522, vertices_98, vertices_674, vertices_578, vertices_770, vertices_164, vertices_292, vertices_644, vertices_772, vertices_56, vertices_88, vertices_280, vertices_536, vertices_104, vertices_296, vertices_112, vertices_304, vertices_208, vertices_400, vertices_784, vertices_224, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_587), (false, vertices_789), (false, vertices_421), (false, vertices_709), (false, vertices_217), (false, vertices_537), (false, vertices_401), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_42), (true, vertices_266), (true, vertices_98), (true, vertices_674), (true, vertices_770), (true, vertices_56), (true, vertices_280), (true, vertices_104), (true, vertices_296), (true, vertices_112), (true, vertices_304), (true, vertices_224)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_587) then 17 else
  if p.val = (false, vertices_789) then 20 else
  if p.val = (false, vertices_421) then 21 else
  if p.val = (false, vertices_709) then 22 else
  if p.val = (false, vertices_217) then 24 else
  if p.val = (false, vertices_537) then 0 else
  if p.val = (false, vertices_401) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_42) then 5 else
  if p.val = (true, vertices_266) then 6 else
  if p.val = (true, vertices_98) then 7 else
  if p.val = (true, vertices_674) then 18 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_56) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_104) then 11 else
  if p.val = (true, vertices_296) then 12 else
  if p.val = (true, vertices_112) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_224) then 15 else
  0
cert_priority
cert_nodeAtPriority_5 0 537 1 401 38 262 518 42 266 98 770 56 280 104 296 112 304 224 587 674 789 421 709 217
cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 4 7 302 38 2
cert_row_4 1 0 2 3 7 8 794 266 2
cert_row_2 2 0 4 6 8 674
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 302
cert_cover_5 0 0 0 1 2 4 38 302 2
cert_coverFacet 1 678
cert_cover_5 1 2 0 1 4 6 38 678 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 794
cert_cover_5 3 1 0 2 3 7 266 794 2
cert_coverFacet 4 106
cert_cover_2 4 2 0 4 5 42 106 3
cert_coverFacet 5 738
cert_cover_5 5 2 0 4 5 6 98 738 3
cert_coverFacet 6 120
cert_cover_2 6 3 2 4 5 56 120 3
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 112 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0073

end
end BundlePart0

section BundlePart1
/- Source: ProjectionCertificates/R_m16e10q1_0074.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0074

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 779, 227, 323, 541, 141, 457, 850, 610, 674, 316, 428, 628, 676, 792, 496, 67, 131, 259, 515, 13, 133, 517, 137, 265, 521, 193, 321, 98, 162, 546, 322, 578, 642, 770, 28, 300, 140, 52, 532, 164, 548, 644, 280, 536, 392, 776, 112, 304, 336, 592, 784, 224, 608, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_779, vertices_227, vertices_323, vertices_541, vertices_141, vertices_457, vertices_850, vertices_610, vertices_674, vertices_316, vertices_428, vertices_628, vertices_676, vertices_792, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_13, vertices_133, vertices_517, vertices_137, vertices_265, vertices_521, vertices_193, vertices_321, vertices_98, vertices_162, vertices_546, vertices_322, vertices_578, vertices_642, vertices_770, vertices_28, vertices_300, vertices_140, vertices_52, vertices_532, vertices_164, vertices_548, vertices_644, vertices_280, vertices_536, vertices_392, vertices_776, vertices_112, vertices_304, vertices_336, vertices_592, vertices_784, vertices_224, vertices_608, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_779), (false, vertices_227), (false, vertices_323), (false, vertices_541), (false, vertices_141), (false, vertices_457), (true, vertices_546), (true, vertices_578), (true, vertices_300), (true, vertices_52), (true, vertices_164), (true, vertices_548), (true, vertices_280), (true, vertices_112), (true, vertices_304), (true, vertices_336), (true, vertices_592), (true, vertices_784), (true, vertices_608), (true, vertices_416), (true, vertices_672)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 20 23 25 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 17 else
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_227) then 19 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_541) then 21 else
  if p.val = (false, vertices_141) then 1 else
  if p.val = (false, vertices_457) then 24 else
  if p.val = (true, vertices_546) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_300) then 22 else
  if p.val = (true, vertices_52) then 4 else
  if p.val = (true, vertices_164) then 5 else
  if p.val = (true, vertices_548) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_112) then 8 else
  if p.val = (true, vertices_304) then 9 else
  if p.val = (true, vertices_336) then 10 else
  if p.val = (true, vertices_592) then 11 else
  if p.val = (true, vertices_784) then 12 else
  if p.val = (true, vertices_608) then 13 else
  if p.val = (true, vertices_416) then 14 else
  if p.val = (true, vertices_672) then 15 else
  0
cert_priority
cert_nodeAtPriority_60 323 141 546 578 52 164 548 280 112 304 336 592 784 608 416 672 647 779 227 541 300 457
cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 4 7 300
cert_row_4 1 0 3 5 7 8 850 322 1
cert_row_4 2 1 3 4 5 8 628 52 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 2 0 1 3
cert_heightProof 4
cert_coverFacet 0 850
cert_cover_5 0 1 0 3 5 7 322 850 1
cert_coverFacet 1 610
cert_cover_2 1 4 0 5 8 98 610 3
cert_coverFacet 2 674
cert_cover_2 2 4 0 6 8 162 674 3
cert_coverFacet 3 316
cert_cover_5 3 0 1 2 3 4 28 316 3
cert_coverFacet 4 428
cert_cover_5 4 0 1 2 4 6 300 428 3
cert_coverFacet 5 628
cert_cover_5 5 2 1 3 4 5 52 628 3
cert_coverFacet 6 676
cert_cover_2 6 4 1 6 8 164 676 3
cert_coverFacet 7 792
cert_cover_2 7 3 2 7 8 280 792 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 112 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0074

end
end BundlePart1

section BundlePart2
/- Source: ProjectionCertificates/R_m16e10q1_0075.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0075

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [87, 403, 323, 681, 241, 865, 897, 30, 782, 358, 282, 220, 236, 556, 804, 920, 19, 67, 259, 81, 145, 97, 161, 545, 321, 385, 641, 769, 14, 22, 70, 262, 26, 266, 274, 322, 28, 44, 204, 524, 84, 100, 292, 548, 772, 152, 280, 168, 552, 648, 776, 208, 400, 224, 352, 800, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_87, vertices_403, vertices_323, vertices_681, vertices_241, vertices_865, vertices_897, vertices_30, vertices_782, vertices_358, vertices_282, vertices_220, vertices_236, vertices_556, vertices_804, vertices_920] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_67, vertices_259, vertices_81, vertices_145, vertices_97, vertices_161, vertices_545, vertices_321, vertices_385, vertices_641, vertices_769, vertices_14, vertices_22, vertices_70, vertices_262, vertices_26, vertices_266, vertices_274, vertices_322, vertices_28, vertices_44, vertices_204, vertices_524, vertices_84, vertices_100, vertices_292, vertices_548, vertices_772, vertices_152, vertices_280, vertices_168, vertices_552, vertices_648, vertices_776, vertices_208, vertices_400, vertices_224, vertices_352, vertices_800, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_87), (false, vertices_403), (false, vertices_323), (false, vertices_681), (false, vertices_241), (false, vertices_865), (false, vertices_897), (true, vertices_14), (true, vertices_262), (true, vertices_26), (true, vertices_266), (true, vertices_28), (true, vertices_44), (true, vertices_204), (true, vertices_524), (true, vertices_100), (true, vertices_292), (true, vertices_548), (true, vertices_772), (true, vertices_152), (true, vertices_280), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 23 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_87) then 17 else
  if p.val = (false, vertices_403) then 18 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_681) then 22 else
  if p.val = (false, vertices_241) then 24 else
  if p.val = (false, vertices_865) then 26 else
  if p.val = (false, vertices_897) then 1 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_266) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_44) then 7 else
  if p.val = (true, vertices_204) then 20 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_772) then 12 else
  if p.val = (true, vertices_152) then 13 else
  if p.val = (true, vertices_280) then 14 else
  if p.val = (true, vertices_776) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_897), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_87), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(true, vertices_204), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_241), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_865), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 4 5 7 358 70 2
cert_row_2 1 1 2 5 6 204
cert_row_4 2 0 1 2 7 8 782 14 3
cert_row_4 3 2 3 6 7 8 920 152 3
cert_rows
cert_pivot_2 4 5 0 2
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 782
cert_cover_5 1 2 0 1 2 7 14 782 3
cert_coverFacet 2 358
cert_cover_5 2 0 0 1 4 5 70 358 2
cert_coverFacet 3 282
cert_cover_2 3 2 0 3 7 26 282 3
cert_coverFacet 4 220
cert_cover_5 4 1 1 2 3 5 28 220 3
cert_coverFacet 5 236
cert_cover_5 5 1 1 2 4 5 44 236 3
cert_coverFacet 6 556
cert_cover_2 6 2 1 4 8 44 556 3
cert_coverFacet 7 804
cert_cover_2 7 4 1 7 8 292 804 3
cert_coverFacet 8 920
cert_cover_5 8 3 2 3 6 7 152 920 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0075

end
end BundlePart2

section BundlePart3
/- Source: ProjectionCertificates/R_m16e10q1_0076.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0076

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 403, 803, 557, 357, 453, 282, 538, 778, 722, 124, 716, 312, 600, 808, 496, 131, 259, 515, 37, 325, 133, 517, 289, 545, 385, 26, 266, 522, 146, 274, 530, 642, 770, 44, 76, 524, 100, 196, 644, 56, 88, 280, 536, 296, 552, 584, 776, 112, 304, 208, 592, 400, 352, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_403, vertices_803, vertices_557, vertices_357, vertices_453, vertices_282, vertices_538, vertices_778, vertices_722, vertices_124, vertices_716, vertices_312, vertices_600, vertices_808, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_37, vertices_325, vertices_133, vertices_517, vertices_289, vertices_545, vertices_385, vertices_26, vertices_266, vertices_522, vertices_146, vertices_274, vertices_530, vertices_642, vertices_770, vertices_44, vertices_76, vertices_524, vertices_100, vertices_196, vertices_644, vertices_56, vertices_88, vertices_280, vertices_536, vertices_296, vertices_552, vertices_584, vertices_776, vertices_112, vertices_304, vertices_208, vertices_592, vertices_400, vertices_352, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_403), (false, vertices_803), (false, vertices_557), (false, vertices_357), (false, vertices_453), (true, vertices_26), (true, vertices_266), (true, vertices_522), (true, vertices_530), (true, vertices_76), (true, vertices_56), (true, vertices_88), (true, vertices_280), (true, vertices_536), (true, vertices_296), (true, vertices_584), (true, vertices_776), (true, vertices_112), (true, vertices_304), (true, vertices_208), (true, vertices_592), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 25 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 18 else
  if p.val = (false, vertices_403) then 19 else
  if p.val = (false, vertices_803) then 20 else
  if p.val = (false, vertices_557) then 22 else
  if p.val = (false, vertices_357) then 23 else
  if p.val = (false, vertices_453) then 24 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_76) then 4 else
  if p.val = (true, vertices_56) then 5 else
  if p.val = (true, vertices_88) then 6 else
  if p.val = (true, vertices_280) then 7 else
  if p.val = (true, vertices_536) then 8 else
  if p.val = (true, vertices_296) then 9 else
  if p.val = (true, vertices_584) then 10 else
  if p.val = (true, vertices_776) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_592) then 15 else
  if p.val = (true, vertices_704) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_403), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 25 => Sum.inl 2
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 5 6 8 722 146 2
cert_row_4 1 1 2 5 6 8 716 76 3
cert_row_4 2 1 2 3 4 5 124 44 2
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 8 1 3
cert_heightProof 4
cert_coverFacet 0 282
cert_cover_2 0 2 0 3 7 26 282 3
cert_coverFacet 1 538
cert_cover_2 1 2 0 3 8 26 538 3
cert_coverFacet 2 778
cert_cover_2 2 2 0 7 8 266 778 3
cert_coverFacet 3 722
cert_cover_5 3 0 0 3 5 6 146 722 2
cert_coverFacet 4 124
cert_cover_5 4 2 1 2 3 4 44 124 2
cert_coverFacet 5 716
cert_cover_5 5 1 1 2 5 6 76 716 3
cert_coverFacet 6 312
cert_cover_2 6 3 2 4 7 56 312 3
cert_coverFacet 7 600
cert_cover_2 7 3 2 5 8 88 600 3
cert_coverFacet 8 808
cert_cover_2 8 4 2 7 8 296 808 3
cert_coverFacet 9 496
cert_cover_5 9 3 3 4 5 6 112 496 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0076

end
end BundlePart3

section BundlePart4
/- Source: ProjectionCertificates/R_m16e10q1_0077.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0077

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 805, 793, 433, 737, 30, 110, 534, 710, 346, 466, 540, 300, 780, 612, 488, 145, 273, 529, 161, 289, 545, 641, 769, 14, 22, 70, 518, 26, 74, 338, 146, 530, 194, 642, 28, 44, 268, 524, 532, 100, 292, 548, 580, 772, 280, 536, 104, 296, 328, 776, 400, 224, 608, 416, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_805, vertices_793, vertices_433, vertices_737, vertices_30, vertices_110, vertices_534, vertices_710, vertices_346, vertices_466, vertices_540, vertices_300, vertices_780, vertices_612, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_145, vertices_273, vertices_529, vertices_161, vertices_289, vertices_545, vertices_641, vertices_769, vertices_14, vertices_22, vertices_70, vertices_518, vertices_26, vertices_74, vertices_338, vertices_146, vertices_530, vertices_194, vertices_642, vertices_28, vertices_44, vertices_268, vertices_524, vertices_532, vertices_100, vertices_292, vertices_548, vertices_580, vertices_772, vertices_280, vertices_536, vertices_104, vertices_296, vertices_328, vertices_776, vertices_400, vertices_224, vertices_608, vertices_416, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_805), (false, vertices_793), (false, vertices_433), (false, vertices_737), (true, vertices_14), (true, vertices_22), (true, vertices_70), (true, vertices_518), (true, vertices_26), (true, vertices_74), (true, vertices_338), (true, vertices_194), (true, vertices_28), (true, vertices_44), (true, vertices_268), (true, vertices_524), (true, vertices_532), (true, vertices_100), (true, vertices_580), (true, vertices_104), (true, vertices_296), (true, vertices_328), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 21 23 25 27 29 30 31 32
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 19 else
  if p.val = (false, vertices_805) then 22 else
  if p.val = (false, vertices_793) then 24 else
  if p.val = (false, vertices_433) then 26 else
  if p.val = (false, vertices_737) then 28 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_26) then 4 else
  if p.val = (true, vertices_74) then 5 else
  if p.val = (true, vertices_338) then 20 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_100) then 12 else
  if p.val = (true, vertices_580) then 13 else
  if p.val = (true, vertices_104) then 14 else
  if p.val = (true, vertices_296) then 15 else
  if p.val = (true, vertices_328) then 16 else
  if p.val = (true, vertices_448) then 17 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_338), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_793), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 29 => Sum.inl 5
  | 30 => Sum.inl 6
  | 31 => Sum.inl 7
  | 32 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 5 7 338
cert_row_4 1 0 1 5 6 8 710 70 3
cert_row_4 2 0 1 2 4 5 110 14 3
cert_row_4 3 2 4 5 6 7 488 104 3
cert_rows
cert_pivot_2 3 8 0 2
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 110
cert_cover_5 1 2 0 1 2 4 14 110 3
cert_coverFacet 2 534
cert_cover_2 2 1 0 3 8 22 534 3
cert_coverFacet 3 710
cert_cover_5 3 1 0 1 5 6 70 710 3
cert_coverFacet 4 346
cert_cover_5 4 0 0 2 3 5 26 346 3
cert_coverFacet 5 466
cert_cover_5 5 0 0 3 5 6 338 466 3
cert_coverFacet 6 540
cert_cover_2 6 2 1 3 8 28 540 3
cert_coverFacet 7 300
cert_cover_2 7 2 1 4 7 44 300 3
cert_coverFacet 8 780
cert_cover_2 8 2 1 7 8 268 780 3
cert_coverFacet 9 612
cert_cover_2 9 4 1 5 8 100 612 3
cert_coverFacet 10 488
cert_cover_5 10 3 2 4 5 6 104 488 3
cert_coveringFacets_6
cert_coveringProof_3
cert_certificate 4 11
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0077

end
end BundlePart4

section BundlePart5
/- Source: ProjectionCertificates/R_m16e10q1_0078.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0078

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [391, 779, 227, 611, 601, 457, 182, 550, 774, 60, 284, 812, 468, 568, 344, 752, 99, 131, 259, 515, 73, 265, 521, 193, 577, 385, 38, 134, 262, 518, 162, 546, 770, 28, 44, 268, 52, 148, 276, 548, 388, 772, 56, 88, 280, 536, 552, 328, 776, 176, 560, 208, 336, 592, 224, 608, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_391, vertices_779, vertices_227, vertices_611, vertices_601, vertices_457, vertices_182, vertices_550, vertices_774, vertices_60, vertices_284, vertices_812, vertices_468, vertices_568, vertices_344, vertices_752] (by decide +kernel)
  polygons := literalFinset [vertices_99, vertices_131, vertices_259, vertices_515, vertices_73, vertices_265, vertices_521, vertices_193, vertices_577, vertices_385, vertices_38, vertices_134, vertices_262, vertices_518, vertices_162, vertices_546, vertices_770, vertices_28, vertices_44, vertices_268, vertices_52, vertices_148, vertices_276, vertices_548, vertices_388, vertices_772, vertices_56, vertices_88, vertices_280, vertices_536, vertices_552, vertices_328, vertices_776, vertices_176, vertices_560, vertices_208, vertices_336, vertices_592, vertices_224, vertices_608, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_391), (false, vertices_779), (false, vertices_227), (false, vertices_611), (false, vertices_601), (false, vertices_457), (true, vertices_38), (true, vertices_518), (true, vertices_28), (true, vertices_44), (true, vertices_268), (true, vertices_52), (true, vertices_148), (true, vertices_276), (true, vertices_548), (true, vertices_772), (true, vertices_56), (true, vertices_280), (true, vertices_552), (true, vertices_176), (true, vertices_560), (true, vertices_208), (true, vertices_336)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 17 23 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_391) then 18 else
  if p.val = (false, vertices_779) then 20 else
  if p.val = (false, vertices_227) then 21 else
  if p.val = (false, vertices_611) then 22 else
  if p.val = (false, vertices_601) then 24 else
  if p.val = (false, vertices_457) then 25 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_518) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_44) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_52) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_560) then 14 else
  if p.val = (true, vertices_208) then 15 else
  if p.val = (true, vertices_336) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_391), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_227), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 6 182 38 2
cert_row_4 1 1 2 4 7 8 812 44 3
cert_row_4 2 1 3 5 6 7 468 148 2
cert_row_4 3 3 4 5 6 8 752 176 2
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 0 0 1 3 4 38 182 2
cert_coverFacet 1 550
cert_cover_2 1 1 0 4 8 38 550 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 60
cert_cover_2 3 2 1 3 4 28 60 3
cert_coverFacet 4 284
cert_cover_2 4 2 1 3 7 28 284 3
cert_coverFacet 5 812
cert_cover_5 5 1 1 2 4 7 44 812 3
cert_coverFacet 6 468
cert_cover_5 6 2 1 3 5 6 148 468 2
cert_coverFacet 7 568
cert_cover_2 7 3 2 4 8 56 568 3
cert_coverFacet 8 344
cert_cover_2 8 3 2 5 7 88 344 3
cert_coverFacet 9 752
cert_cover_5 9 3 3 4 5 6 176 752 2
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0078

end
end BundlePart5

section BundlePart6
/- Source: ProjectionCertificates/R_m16e10q1_0079.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0079

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [651, 179, 611, 589, 361, 425, 790, 562, 402, 898, 348, 396, 652, 628, 900, 496, 35, 131, 515, 297, 73, 137, 521, 97, 161, 577, 50, 146, 274, 530, 546, 386, 642, 770, 76, 140, 268, 524, 84, 276, 532, 580, 388, 644, 772, 328, 392, 648, 112, 176, 560, 336, 400, 352, 608, 416, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_651, vertices_179, vertices_611, vertices_589, vertices_361, vertices_425, vertices_790, vertices_562, vertices_402, vertices_898, vertices_348, vertices_396, vertices_652, vertices_628, vertices_900, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_515, vertices_297, vertices_73, vertices_137, vertices_521, vertices_97, vertices_161, vertices_577, vertices_50, vertices_146, vertices_274, vertices_530, vertices_546, vertices_386, vertices_642, vertices_770, vertices_76, vertices_140, vertices_268, vertices_524, vertices_84, vertices_276, vertices_532, vertices_580, vertices_388, vertices_644, vertices_772, vertices_328, vertices_392, vertices_648, vertices_112, vertices_176, vertices_560, vertices_336, vertices_400, vertices_352, vertices_608, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_651), (false, vertices_179), (false, vertices_611), (false, vertices_589), (false, vertices_361), (false, vertices_425), (true, vertices_274), (true, vertices_530), (true, vertices_386), (true, vertices_770), (true, vertices_140), (true, vertices_268), (true, vertices_84), (true, vertices_276), (true, vertices_532), (true, vertices_388), (true, vertices_644), (true, vertices_772), (true, vertices_112), (true, vertices_560), (true, vertices_336), (true, vertices_400), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 23 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_651) then 18 else
  if p.val = (false, vertices_179) then 19 else
  if p.val = (false, vertices_611) then 20 else
  if p.val = (false, vertices_589) then 22 else
  if p.val = (false, vertices_361) then 24 else
  if p.val = (false, vertices_425) then 25 else
  if p.val = (true, vertices_274) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_400) then 15 else
  if p.val = (true, vertices_896) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_651), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 7 8 790 274 1
cert_row_4 1 1 2 3 5 7 348 76 2
cert_row_4 2 1 3 4 5 8 628 84 2
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 562
cert_cover_2 1 3 0 4 8 50 562 3
cert_coverFacet 2 402
cert_cover_2 2 3 0 6 7 146 402 3
cert_coverFacet 3 898
cert_cover_2 3 6 0 7 8 386 898 3
cert_coverFacet 4 348
cert_cover_5 4 1 1 2 3 5 76 348 2
cert_coverFacet 5 396
cert_cover_2 5 2 1 6 7 140 396 3
cert_coverFacet 6 652
cert_cover_2 6 2 1 6 8 140 652 3
cert_coverFacet 7 628
cert_cover_5 7 2 1 3 4 5 84 628 2
cert_coverFacet 8 900
cert_cover_2 8 6 1 7 8 388 900 3
cert_coverFacet 9 496
cert_cover_5 9 3 3 4 5 6 112 496 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0079

end
end BundlePart6

section BundlePart7
/- Source: ProjectionCertificates/R_m16e10q1_0080.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0080

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [899, 781, 597, 453, 737, 542, 154, 394, 778, 626, 178, 674, 316, 372, 184, 488, 69, 261, 517, 193, 577, 385, 641, 769, 26, 138, 266, 522, 50, 146, 530, 162, 546, 386, 642, 770, 28, 268, 524, 308, 84, 532, 324, 56, 152, 168, 296, 392, 776, 112, 176, 592, 224, 352, 608, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_899, vertices_781, vertices_597, vertices_453, vertices_737, vertices_542, vertices_154, vertices_394, vertices_778, vertices_626, vertices_178, vertices_674, vertices_316, vertices_372, vertices_184, vertices_488] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_193, vertices_577, vertices_385, vertices_641, vertices_769, vertices_26, vertices_138, vertices_266, vertices_522, vertices_50, vertices_146, vertices_530, vertices_162, vertices_546, vertices_386, vertices_642, vertices_770, vertices_28, vertices_268, vertices_524, vertices_308, vertices_84, vertices_532, vertices_324, vertices_56, vertices_152, vertices_168, vertices_296, vertices_392, vertices_776, vertices_112, vertices_176, vertices_592, vertices_224, vertices_352, vertices_608, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_899), (false, vertices_781), (false, vertices_597), (false, vertices_453), (false, vertices_737), (true, vertices_26), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_50), (true, vertices_146), (true, vertices_530), (true, vertices_162), (true, vertices_546), (true, vertices_28), (true, vertices_308), (true, vertices_56), (true, vertices_152), (true, vertices_168), (true, vertices_296), (true, vertices_392), (true, vertices_112), (true, vertices_176), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 22 20 26 27 29 30 31 32
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_899) then 19 else
  if p.val = (false, vertices_781) then 21 else
  if p.val = (false, vertices_597) then 23 else
  if p.val = (false, vertices_453) then 24 else
  if p.val = (false, vertices_737) then 28 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_138) then 1 else
  if p.val = (true, vertices_266) then 2 else
  if p.val = (true, vertices_522) then 3 else
  if p.val = (true, vertices_50) then 4 else
  if p.val = (true, vertices_146) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_162) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_308) then 25 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_152) then 11 else
  if p.val = (true, vertices_168) then 12 else
  if p.val = (true, vertices_296) then 13 else
  if p.val = (true, vertices_392) then 14 else
  if p.val = (true, vertices_112) then 15 else
  if p.val = (true, vertices_176) then 16 else
  if p.val = (true, vertices_352) then 17 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_899), by decide +kernel⟩
  | 20 => Sum.inl 2
  | 21 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 22 => Sum.inl 1
  | 23 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_453), by decide +kernel⟩
  | 25 => Sum.inr ⟨(true, vertices_308), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 29 => Sum.inl 5
  | 30 => Sum.inl 6
  | 31 => Sum.inl 7
  | 32 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 2 4 5 6 7 488 168 2
cert_row_2 1 1 3 4 7 308
cert_row_4 2 0 1 2 3 8 542 26 1
cert_row_4 3 0 3 4 5 8 626 50 3
cert_rows
cert_pivot_2 6 7 1 0
cert_heightProof 4
cert_coverFacet 0 542
cert_cover_5 0 2 0 1 2 3 26 542 1
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 394
cert_cover_2 2 2 0 6 7 138 394 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 626
cert_cover_5 4 3 0 3 4 5 50 626 3
cert_coverFacet 5 178
cert_cover_2 5 3 0 4 6 50 178 3
cert_coverFacet 6 674
cert_cover_2 6 4 0 6 8 162 674 3
cert_coverFacet 7 316
cert_cover_5 7 1 1 2 3 4 28 316 3
cert_coverFacet 8 372
cert_cover_5 8 1 1 3 4 5 308 372 3
cert_coverFacet 9 184
cert_cover_2 9 3 2 4 6 56 184 3
cert_coverFacet 10 488
cert_cover_5 10 0 2 4 5 6 168 488 2
cert_coveringFacets_6
cert_coveringProof_3
cert_certificate 4 11
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0080

end
end BundlePart7

section BundlePart8
/- Source: ProjectionCertificates/R_m16e10q1_0081.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0081

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [775, 211, 323, 643, 301, 677, 481, 602, 690, 834, 60, 540, 844, 564, 440, 472, 67, 131, 259, 515, 37, 261, 517, 161, 289, 193, 321, 641, 82, 146, 530, 322, 578, 642, 770, 28, 44, 268, 524, 52, 532, 548, 772, 56, 88, 408, 536, 296, 328, 584, 176, 560, 208, 416, 672, 448, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_775, vertices_211, vertices_323, vertices_643, vertices_301, vertices_677, vertices_481, vertices_602, vertices_690, vertices_834, vertices_60, vertices_540, vertices_844, vertices_564, vertices_440, vertices_472] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_131, vertices_259, vertices_515, vertices_37, vertices_261, vertices_517, vertices_161, vertices_289, vertices_193, vertices_321, vertices_641, vertices_82, vertices_146, vertices_530, vertices_322, vertices_578, vertices_642, vertices_770, vertices_28, vertices_44, vertices_268, vertices_524, vertices_52, vertices_532, vertices_548, vertices_772, vertices_56, vertices_88, vertices_408, vertices_536, vertices_296, vertices_328, vertices_584, vertices_176, vertices_560, vertices_208, vertices_416, vertices_672, vertices_448, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_775), (false, vertices_211), (false, vertices_323), (false, vertices_643), (false, vertices_301), (false, vertices_677), (false, vertices_481), (true, vertices_530), (true, vertices_578), (true, vertices_28), (true, vertices_524), (true, vertices_52), (true, vertices_532), (true, vertices_56), (true, vertices_88), (true, vertices_408), (true, vertices_536), (true, vertices_328), (true, vertices_584), (true, vertices_176), (true, vertices_560), (true, vertices_832)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_775) then 17 else
  if p.val = (false, vertices_211) then 18 else
  if p.val = (false, vertices_323) then 0 else
  if p.val = (false, vertices_643) then 1 else
  if p.val = (false, vertices_301) then 20 else
  if p.val = (false, vertices_677) then 21 else
  if p.val = (false, vertices_481) then 26 else
  if p.val = (true, vertices_530) then 2 else
  if p.val = (true, vertices_578) then 3 else
  if p.val = (true, vertices_28) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_52) then 6 else
  if p.val = (true, vertices_532) then 7 else
  if p.val = (true, vertices_56) then 8 else
  if p.val = (true, vertices_88) then 9 else
  if p.val = (true, vertices_408) then 23 else
  if p.val = (true, vertices_536) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_560) then 14 else
  if p.val = (true, vertices_832) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_323), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_88), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_832), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_775), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(true, vertices_408), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 3 4 6 8 690 146 2
cert_row_2 1 2 3 6 7 408
cert_row_4 2 0 2 3 5 8 602 82 1
cert_row_4 3 1 2 5 7 8 844 268 2
cert_rows
cert_pivot_2 4 6 0 1
cert_heightProof 4
cert_coverFacet 0 602
cert_cover_5 0 2 0 2 3 5 82 602 1
cert_coverFacet 1 690
cert_cover_5 1 0 0 3 4 6 146 690 2
cert_coverFacet 2 834
cert_cover_2 2 5 0 7 8 322 834 3
cert_coverFacet 3 60
cert_cover_2 3 2 1 3 4 28 60 3
cert_coverFacet 4 540
cert_cover_2 4 2 1 3 8 28 540 3
cert_coverFacet 5 844
cert_cover_5 5 3 1 2 5 7 268 844 2
cert_coverFacet 6 564
cert_cover_2 6 3 1 4 8 52 564 3
cert_coverFacet 7 440
cert_cover_5 7 1 2 3 4 6 56 440 3
cert_coverFacet 8 472
cert_cover_5 8 1 2 3 5 6 88 472 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0081

end
end BundlePart8

section BundlePart9
/- Source: ProjectionCertificates/R_m16e10q1_0082.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0082

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [539, 557, 597, 229, 345, 361, 902, 154, 810, 394, 722, 420, 804, 708, 408, 496, 37, 69, 517, 25, 41, 329, 521, 81, 529, 97, 26, 138, 266, 522, 146, 530, 386, 642, 770, 164, 292, 548, 196, 580, 388, 644, 772, 152, 280, 296, 552, 392, 208, 336, 592, 400, 224, 352, 416, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_539, vertices_557, vertices_597, vertices_229, vertices_345, vertices_361, vertices_902, vertices_154, vertices_810, vertices_394, vertices_722, vertices_420, vertices_804, vertices_708, vertices_408, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_517, vertices_25, vertices_41, vertices_329, vertices_521, vertices_81, vertices_529, vertices_97, vertices_26, vertices_138, vertices_266, vertices_522, vertices_146, vertices_530, vertices_386, vertices_642, vertices_770, vertices_164, vertices_292, vertices_548, vertices_196, vertices_580, vertices_388, vertices_644, vertices_772, vertices_152, vertices_280, vertices_296, vertices_552, vertices_392, vertices_208, vertices_336, vertices_592, vertices_400, vertices_224, vertices_352, vertices_416, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_539), (false, vertices_557), (false, vertices_597), (false, vertices_229), (false, vertices_345), (false, vertices_361), (true, vertices_138), (true, vertices_266), (true, vertices_146), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_292), (true, vertices_388), (true, vertices_644), (true, vertices_772), (true, vertices_152), (true, vertices_392), (true, vertices_208), (true, vertices_400), (true, vertices_416), (true, vertices_800), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 23 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_539) then 18 else
  if p.val = (false, vertices_557) then 20 else
  if p.val = (false, vertices_597) then 21 else
  if p.val = (false, vertices_229) then 22 else
  if p.val = (false, vertices_345) then 24 else
  if p.val = (false, vertices_361) then 25 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_146) then 2 else
  if p.val = (true, vertices_386) then 3 else
  if p.val = (true, vertices_642) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_292) then 6 else
  if p.val = (true, vertices_388) then 7 else
  if p.val = (true, vertices_644) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_400) then 13 else
  if p.val = (true, vertices_416) then 14 else
  if p.val = (true, vertices_800) then 15 else
  if p.val = (true, vertices_704) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_539), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_597), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_229), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 8 902 386 1
cert_row_4 1 0 2 4 7 8 810 266 2
cert_row_4 2 0 3 5 6 8 722 146 2
cert_row_4 3 3 4 5 6 7 496 208 1
cert_rows
cert_pivot_2 1 2 0 3
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 0 0 1 6 7 386 902 1
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 810
cert_cover_5 2 1 0 2 4 7 266 810 2
cert_coverFacet 3 394
cert_cover_2 3 2 0 6 7 138 394 3
cert_coverFacet 4 722
cert_cover_5 4 2 0 3 5 6 146 722 2
cert_coverFacet 5 420
cert_cover_2 5 4 1 6 7 164 420 3
cert_coverFacet 6 804
cert_cover_2 6 4 1 7 8 292 804 3
cert_coverFacet 7 708
cert_cover_2 7 5 1 6 8 196 708 3
cert_coverFacet 8 408
cert_cover_2 8 3 2 6 7 152 408 3
cert_coverFacet 9 496
cert_cover_5 9 3 3 4 5 6 208 496 1
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0082

end
end BundlePart9

section BundlePart10
/- Source: ProjectionCertificates/R_m16e10q1_0083.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0083

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 421, 837, 809, 689, 590, 342, 406, 122, 154, 650, 568, 664, 360, 840, 496, 133, 261, 517, 161, 289, 545, 641, 769, 278, 70, 134, 518, 26, 74, 138, 522, 82, 146, 642, 324, 580, 388, 56, 152, 536, 104, 296, 552, 328, 584, 648, 776, 112, 176, 560, 336, 400, 656, 352, 416, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_421, vertices_837, vertices_809, vertices_689, vertices_590, vertices_342, vertices_406, vertices_122, vertices_154, vertices_650, vertices_568, vertices_664, vertices_360, vertices_840, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_133, vertices_261, vertices_517, vertices_161, vertices_289, vertices_545, vertices_641, vertices_769, vertices_278, vertices_70, vertices_134, vertices_518, vertices_26, vertices_74, vertices_138, vertices_522, vertices_82, vertices_146, vertices_642, vertices_324, vertices_580, vertices_388, vertices_56, vertices_152, vertices_536, vertices_104, vertices_296, vertices_552, vertices_328, vertices_584, vertices_648, vertices_776, vertices_112, vertices_176, vertices_560, vertices_336, vertices_400, vertices_656, vertices_352, vertices_416, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_421), (false, vertices_837), (false, vertices_809), (false, vertices_689), (true, vertices_278), (true, vertices_70), (true, vertices_26), (true, vertices_74), (true, vertices_138), (true, vertices_522), (true, vertices_82), (true, vertices_146), (true, vertices_56), (true, vertices_152), (true, vertices_536), (true, vertices_104), (true, vertices_328), (true, vertices_584), (true, vertices_648), (true, vertices_112), (true, vertices_336), (true, vertices_400), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 21 24 26 28 29 30 31 32
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 19 else
  if p.val = (false, vertices_421) then 22 else
  if p.val = (false, vertices_837) then 23 else
  if p.val = (false, vertices_809) then 25 else
  if p.val = (false, vertices_689) then 27 else
  if p.val = (true, vertices_278) then 20 else
  if p.val = (true, vertices_70) then 0 else
  if p.val = (true, vertices_26) then 1 else
  if p.val = (true, vertices_74) then 2 else
  if p.val = (true, vertices_138) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_146) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_536) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_328) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_648) then 13 else
  if p.val = (true, vertices_112) then 14 else
  if p.val = (true, vertices_336) then 15 else
  if p.val = (true, vertices_400) then 16 else
  if p.val = (true, vertices_352) then 17 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_328), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 20 => Sum.inr ⟨(true, vertices_278), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_421), by decide +kernel⟩
  | 23 => Sum.inr ⟨(false, vertices_837), by decide +kernel⟩
  | 24 => Sum.inl 2
  | 25 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inr ⟨(false, vertices_689), by decide +kernel⟩
  | 28 => Sum.inl 4
  | 29 => Sum.inl 5
  | 30 => Sum.inl 6
  | 31 => Sum.inl 7
  | 32 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 70 2
cert_row_2 1 0 1 3 7 278
cert_row_4 2 0 2 3 4 5 122 26 3
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 8 1 0 3
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 70 590 2
cert_coverFacet 1 342
cert_cover_5 1 1 0 1 3 5 278 342 3
cert_coverFacet 2 406
cert_cover_5 2 1 0 1 3 6 278 406 3
cert_coverFacet 3 122
cert_cover_5 3 2 0 2 3 4 26 122 3
cert_coverFacet 4 154
cert_cover_2 4 2 0 3 6 26 154 3
cert_coverFacet 5 650
cert_cover_2 5 2 0 6 8 138 650 3
cert_coverFacet 6 568
cert_cover_2 6 3 2 4 8 56 568 3
cert_coverFacet 7 664
cert_cover_2 7 3 2 6 8 152 664 3
cert_coverFacet 8 360
cert_cover_2 8 4 2 5 7 104 360 3
cert_coverFacet 9 840
cert_cover_2 9 5 2 7 8 328 840 3
cert_coverFacet 10 496
cert_cover_5 10 3 3 4 5 6 112 496 3
cert_coveringFacets_6
cert_coveringProof_3
cert_certificate 4 11
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0083

end
end BundlePart10

section BundlePart11
/- Source: ProjectionCertificates/R_m16e10q1_0084.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0084

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [171, 301, 341, 677, 709, 457, 598, 154, 794, 554, 210, 738, 820, 408, 808, 464, 37, 69, 645, 261, 41, 137, 265, 161, 193, 321, 26, 42, 138, 522, 82, 146, 530, 162, 546, 194, 578, 84, 276, 532, 292, 548, 580, 152, 280, 296, 552, 392, 776, 208, 336, 400, 784, 672, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_171, vertices_301, vertices_341, vertices_677, vertices_709, vertices_457, vertices_598, vertices_154, vertices_794, vertices_554, vertices_210, vertices_738, vertices_820, vertices_408, vertices_808, vertices_464] (by decide +kernel)
  polygons := literalFinset [vertices_37, vertices_69, vertices_645, vertices_261, vertices_41, vertices_137, vertices_265, vertices_161, vertices_193, vertices_321, vertices_26, vertices_42, vertices_138, vertices_522, vertices_82, vertices_146, vertices_530, vertices_162, vertices_546, vertices_194, vertices_578, vertices_84, vertices_276, vertices_532, vertices_292, vertices_548, vertices_580, vertices_152, vertices_280, vertices_296, vertices_552, vertices_392, vertices_776, vertices_208, vertices_336, vertices_400, vertices_784, vertices_672, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_171), (false, vertices_301), (false, vertices_341), (false, vertices_677), (false, vertices_709), (false, vertices_457), (true, vertices_26), (true, vertices_522), (true, vertices_82), (true, vertices_146), (true, vertices_530), (true, vertices_546), (true, vertices_194), (true, vertices_578), (true, vertices_532), (true, vertices_152), (true, vertices_280), (true, vertices_552), (true, vertices_776), (true, vertices_208), (true, vertices_400), (true, vertices_784), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 22 19 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_171) then 18 else
  if p.val = (false, vertices_301) then 20 else
  if p.val = (false, vertices_341) then 23 else
  if p.val = (false, vertices_677) then 24 else
  if p.val = (false, vertices_709) then 25 else
  if p.val = (false, vertices_457) then 21 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_522) then 1 else
  if p.val = (true, vertices_82) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_152) then 9 else
  if p.val = (true, vertices_280) then 10 else
  if p.val = (true, vertices_552) then 11 else
  if p.val = (true, vertices_776) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_400) then 14 else
  if p.val = (true, vertices_784) then 15 else
  if p.val = (true, vertices_800) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_171), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_301), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 22 => Sum.inl 1
  | 23 => Sum.inr ⟨(false, vertices_341), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_677), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 7 8 794 26 3
cert_row_4 1 0 4 5 6 8 738 162 2
cert_row_4 2 0 1 3 5 8 598 82 1
cert_row_4 3 1 3 4 7 8 820 276 2
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 598
cert_cover_5 0 2 0 1 3 5 82 598 1
cert_coverFacet 1 154
cert_cover_2 1 2 0 3 6 26 154 3
cert_coverFacet 2 794
cert_cover_5 2 0 0 2 3 7 26 794 3
cert_coverFacet 3 554
cert_cover_2 3 2 0 4 8 42 554 3
cert_coverFacet 4 210
cert_cover_2 4 3 0 5 6 82 210 3
cert_coverFacet 5 738
cert_cover_5 5 1 0 4 5 6 162 738 2
cert_coverFacet 6 820
cert_cover_5 6 3 1 3 4 7 276 820 2
cert_coverFacet 7 408
cert_cover_2 7 3 2 6 7 152 408 3
cert_coverFacet 8 808
cert_cover_2 8 4 2 7 8 296 808 3
cert_coverFacet 9 464
cert_cover_2 9 5 3 6 7 208 464 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0084

end
end BundlePart11

section BundlePart12
/- Source: ProjectionCertificates/R_m16e10q1_0085.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0085

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 541, 781, 213, 357, 625, 158, 794, 170, 298, 658, 738, 396, 452, 488, 720, 525, 21, 69, 261, 81, 529, 97, 289, 545, 769, 26, 42, 138, 266, 146, 530, 162, 290, 546, 642, 770, 28, 140, 268, 148, 196, 324, 388, 536, 168, 296, 392, 776, 208, 592, 656, 224, 352, 608, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_541, vertices_781, vertices_213, vertices_357, vertices_625, vertices_158, vertices_794, vertices_170, vertices_298, vertices_658, vertices_738, vertices_396, vertices_452, vertices_488, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_525, vertices_21, vertices_69, vertices_261, vertices_81, vertices_529, vertices_97, vertices_289, vertices_545, vertices_769, vertices_26, vertices_42, vertices_138, vertices_266, vertices_146, vertices_530, vertices_162, vertices_290, vertices_546, vertices_642, vertices_770, vertices_28, vertices_140, vertices_268, vertices_148, vertices_196, vertices_324, vertices_388, vertices_536, vertices_168, vertices_296, vertices_392, vertices_776, vertices_208, vertices_592, vertices_656, vertices_224, vertices_352, vertices_608, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_541), (false, vertices_781), (false, vertices_213), (false, vertices_357), (false, vertices_625), (true, vertices_26), (true, vertices_42), (true, vertices_138), (true, vertices_266), (true, vertices_146), (true, vertices_530), (true, vertices_162), (true, vertices_642), (true, vertices_140), (true, vertices_388), (true, vertices_168), (true, vertices_296), (true, vertices_392), (true, vertices_656), (true, vertices_224), (true, vertices_448), (true, vertices_704)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 22 19 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 18 else
  if p.val = (false, vertices_541) then 20 else
  if p.val = (false, vertices_781) then 21 else
  if p.val = (false, vertices_213) then 23 else
  if p.val = (false, vertices_357) then 24 else
  if p.val = (false, vertices_625) then 26 else
  if p.val = (true, vertices_26) then 0 else
  if p.val = (true, vertices_42) then 1 else
  if p.val = (true, vertices_138) then 2 else
  if p.val = (true, vertices_266) then 3 else
  if p.val = (true, vertices_146) then 4 else
  if p.val = (true, vertices_530) then 5 else
  if p.val = (true, vertices_162) then 6 else
  if p.val = (true, vertices_642) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_392) then 12 else
  if p.val = (true, vertices_656) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_448) then 15 else
  if p.val = (true, vertices_704) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_704), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 19 => Sum.inl 2
  | 20 => Sum.inr ⟨(false, vertices_541), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 22 => Sum.inl 1
  | 23 => Sum.inr ⟨(false, vertices_213), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_357), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 3 6 158 26 1
cert_row_4 1 0 2 3 7 8 794 26 3
cert_row_4 2 0 4 5 6 8 738 162 2
cert_row_4 3 2 4 5 6 7 488 168 2
cert_rows
cert_pivot_2 1 3 0 2
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 0 0 1 2 3 26 158 1
cert_coverFacet 1 794
cert_cover_5 1 1 0 2 3 7 26 794 3
cert_coverFacet 2 170
cert_cover_2 2 2 0 4 6 42 170 3
cert_coverFacet 3 298
cert_cover_2 3 2 0 4 7 42 298 3
cert_coverFacet 4 658
cert_cover_2 4 3 0 6 8 146 658 3
cert_coverFacet 5 738
cert_cover_5 5 2 0 4 5 6 162 738 2
cert_coverFacet 6 396
cert_cover_2 6 2 1 6 7 140 396 3
cert_coverFacet 7 452
cert_cover_2 7 5 1 6 7 196 452 3
cert_coverFacet 8 488
cert_cover_5 8 3 2 4 5 6 168 488 2
cert_coverFacet 9 720
cert_cover_2 9 5 3 6 8 208 720 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0085

end
end BundlePart12

section BundlePart13
/- Source: ProjectionCertificates/R_m16e10q1_0086.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0086

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [555, 179, 707, 589, 425, 457, 790, 306, 658, 802, 348, 812, 212, 660, 708, 496, 35, 131, 515, 41, 73, 393, 521, 161, 193, 577, 50, 146, 274, 530, 290, 546, 642, 770, 76, 268, 524, 84, 148, 276, 532, 196, 580, 644, 772, 296, 552, 328, 176, 304, 208, 336, 656, 416, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_555, vertices_179, vertices_707, vertices_589, vertices_425, vertices_457, vertices_790, vertices_306, vertices_658, vertices_802, vertices_348, vertices_812, vertices_212, vertices_660, vertices_708, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_515, vertices_41, vertices_73, vertices_393, vertices_521, vertices_161, vertices_193, vertices_577, vertices_50, vertices_146, vertices_274, vertices_530, vertices_290, vertices_546, vertices_642, vertices_770, vertices_76, vertices_268, vertices_524, vertices_84, vertices_148, vertices_276, vertices_532, vertices_196, vertices_580, vertices_644, vertices_772, vertices_296, vertices_552, vertices_328, vertices_176, vertices_304, vertices_208, vertices_336, vertices_656, vertices_416, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_555), (false, vertices_179), (false, vertices_707), (false, vertices_589), (false, vertices_425), (false, vertices_457), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_770), (true, vertices_268), (true, vertices_84), (true, vertices_148), (true, vertices_276), (true, vertices_532), (true, vertices_196), (true, vertices_644), (true, vertices_772), (true, vertices_304), (true, vertices_208), (true, vertices_336), (true, vertices_656), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 23 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_555) then 18 else
  if p.val = (false, vertices_179) then 19 else
  if p.val = (false, vertices_707) then 20 else
  if p.val = (false, vertices_589) then 22 else
  if p.val = (false, vertices_425) then 24 else
  if p.val = (false, vertices_457) then 25 else
  if p.val = (true, vertices_274) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_290) then 2 else
  if p.val = (true, vertices_770) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_84) then 5 else
  if p.val = (true, vertices_148) then 6 else
  if p.val = (true, vertices_276) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_196) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_656) then 15 else
  if p.val = (true, vertices_800) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_196), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_555), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_457), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 7 8 790 274 1
cert_row_4 1 1 2 4 7 8 812 268 2
cert_row_4 2 1 2 3 5 7 348 76 2
cert_row_4 3 3 4 5 6 7 496 176 2
cert_rows
cert_pivot_2 0 8 1 3
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 0 0 1 3 7 274 790 1
cert_coverFacet 1 306
cert_cover_2 1 3 0 4 7 50 306 3
cert_coverFacet 2 658
cert_cover_2 2 3 0 6 8 146 658 3
cert_coverFacet 3 802
cert_cover_2 3 4 0 7 8 290 802 3
cert_coverFacet 4 348
cert_cover_5 4 2 1 2 3 5 76 348 2
cert_coverFacet 5 812
cert_cover_5 5 1 1 2 4 7 268 812 2
cert_coverFacet 6 212
cert_cover_2 6 3 1 5 6 84 212 3
cert_coverFacet 7 660
cert_cover_2 7 3 1 6 8 148 660 3
cert_coverFacet 8 708
cert_cover_2 8 5 1 6 8 196 708 3
cert_coverFacet 9 496
cert_cover_5 9 3 3 4 5 6 176 496 2
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0086

end
end BundlePart13

section BundlePart14
/- Source: ProjectionCertificates/R_m16e10q1_0087.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0087

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [659, 781, 409, 713, 817, 590, 118, 806, 562, 210, 706, 236, 428, 368, 464, 480, 137, 265, 521, 145, 273, 529, 641, 769, 38, 70, 518, 50, 82, 146, 530, 546, 194, 578, 642, 172, 76, 268, 524, 100, 292, 772, 200, 584, 392, 112, 304, 560, 208, 336, 400, 224, 352, 416, 800, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_659, vertices_781, vertices_409, vertices_713, vertices_817, vertices_590, vertices_118, vertices_806, vertices_562, vertices_210, vertices_706, vertices_236, vertices_428, vertices_368, vertices_464, vertices_480] (by decide +kernel)
  polygons := literalFinset [vertices_137, vertices_265, vertices_521, vertices_145, vertices_273, vertices_529, vertices_641, vertices_769, vertices_38, vertices_70, vertices_518, vertices_50, vertices_82, vertices_146, vertices_530, vertices_546, vertices_194, vertices_578, vertices_642, vertices_172, vertices_76, vertices_268, vertices_524, vertices_100, vertices_292, vertices_772, vertices_200, vertices_584, vertices_392, vertices_112, vertices_304, vertices_560, vertices_208, vertices_336, vertices_400, vertices_224, vertices_352, vertices_416, vertices_800, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_659), (false, vertices_781), (false, vertices_409), (false, vertices_713), (false, vertices_817), (true, vertices_38), (true, vertices_70), (true, vertices_518), (true, vertices_50), (true, vertices_82), (true, vertices_546), (true, vertices_194), (true, vertices_578), (true, vertices_172), (true, vertices_76), (true, vertices_100), (true, vertices_292), (true, vertices_112), (true, vertices_208), (true, vertices_336), (true, vertices_224), (true, vertices_352), (true, vertices_416), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 18 20 23 26 28 29 30 31 32
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_659) then 19 else
  if p.val = (false, vertices_781) then 21 else
  if p.val = (false, vertices_409) then 24 else
  if p.val = (false, vertices_713) then 25 else
  if p.val = (false, vertices_817) then 27 else
  if p.val = (true, vertices_38) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_50) then 3 else
  if p.val = (true, vertices_82) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_194) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_172) then 22 else
  if p.val = (true, vertices_76) then 8 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_112) then 11 else
  if p.val = (true, vertices_208) then 12 else
  if p.val = (true, vertices_336) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_352) then 15 else
  if p.val = (true, vertices_416) then 16 else
  if p.val = (true, vertices_448) then 17 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_194), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 17 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 18 => Sum.inl 0
  | 19 => Sum.inr ⟨(false, vertices_659), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_781), by decide +kernel⟩
  | 22 => Sum.inr ⟨(true, vertices_172), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inr ⟨(false, vertices_817), by decide +kernel⟩
  | 28 => Sum.inl 4
  | 29 => Sum.inl 5
  | 30 => Sum.inl 6
  | 31 => Sum.inl 7
  | 32 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 1 2 4 6 172
cert_row_4 1 0 1 2 5 8 590 70 2
cert_row_4 2 0 1 3 4 5 118 38 2
cert_row_4 3 0 1 4 7 8 806 38 3
cert_rows
cert_pivot_2 6 2 3 0
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 1 0 1 2 5 70 590 2
cert_coverFacet 1 118
cert_cover_5 1 2 0 1 3 4 38 118 2
cert_coverFacet 2 806
cert_cover_5 2 3 0 1 4 7 38 806 3
cert_coverFacet 3 562
cert_cover_2 3 3 0 4 8 50 562 3
cert_coverFacet 4 210
cert_cover_2 4 3 0 5 6 82 210 3
cert_coverFacet 5 706
cert_cover_2 5 5 0 6 8 194 706 3
cert_coverFacet 6 236
cert_cover_5 6 0 1 2 4 5 172 236 3
cert_coverFacet 7 428
cert_cover_5 7 0 1 2 4 7 172 428 3
cert_coverFacet 8 368
cert_cover_2 8 4 3 5 7 112 368 3
cert_coverFacet 9 464
cert_cover_2 9 5 3 6 7 208 464 3
cert_coverFacet 10 480
cert_cover_2 10 5 4 6 7 224 480 3
cert_coveringFacets_6
cert_coveringProof_3
cert_certificate 4 11
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0087

end
end BundlePart14

section BundlePart15
/- Source: ProjectionCertificates/R_m16e10q1_0088.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0088

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [179, 547, 707, 333, 805, 581, 481, 790, 666, 306, 802, 284, 540, 716, 248, 376, 35, 131, 515, 69, 261, 517, 161, 289, 545, 193, 321, 577, 50, 146, 274, 530, 290, 546, 642, 770, 28, 76, 268, 524, 276, 532, 580, 772, 120, 152, 280, 536, 200, 328, 648, 176, 304, 224, 352, 800, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_179, vertices_547, vertices_707, vertices_333, vertices_805, vertices_581, vertices_481, vertices_790, vertices_666, vertices_306, vertices_802, vertices_284, vertices_540, vertices_716, vertices_248, vertices_376] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_131, vertices_515, vertices_69, vertices_261, vertices_517, vertices_161, vertices_289, vertices_545, vertices_193, vertices_321, vertices_577, vertices_50, vertices_146, vertices_274, vertices_530, vertices_290, vertices_546, vertices_642, vertices_770, vertices_28, vertices_76, vertices_268, vertices_524, vertices_276, vertices_532, vertices_580, vertices_772, vertices_120, vertices_152, vertices_280, vertices_536, vertices_200, vertices_328, vertices_648, vertices_176, vertices_304, vertices_224, vertices_352, vertices_800, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_179), (false, vertices_547), (false, vertices_707), (false, vertices_333), (false, vertices_805), (false, vertices_581), (false, vertices_481), (true, vertices_274), (true, vertices_530), (true, vertices_290), (true, vertices_770), (true, vertices_28), (true, vertices_524), (true, vertices_276), (true, vertices_532), (true, vertices_120), (true, vertices_152), (true, vertices_280), (true, vertices_536), (true, vertices_200), (true, vertices_648), (true, vertices_304)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_179) then 17 else
  if p.val = (false, vertices_547) then 0 else
  if p.val = (false, vertices_707) then 18 else
  if p.val = (false, vertices_333) then 20 else
  if p.val = (false, vertices_805) then 21 else
  if p.val = (false, vertices_581) then 1 else
  if p.val = (false, vertices_481) then 26 else
  if p.val = (true, vertices_274) then 2 else
  if p.val = (true, vertices_530) then 3 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_770) then 5 else
  if p.val = (true, vertices_28) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_276) then 8 else
  if p.val = (true, vertices_532) then 9 else
  if p.val = (true, vertices_120) then 23 else
  if p.val = (true, vertices_152) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_200) then 13 else
  if p.val = (true, vertices_648) then 14 else
  if p.val = (true, vertices_304) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_547), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_581), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_179), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_707), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(true, vertices_120), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 2 3 4 5 120
cert_row_4 1 0 1 3 7 8 790 274 1
cert_row_4 2 0 2 3 6 8 666 146 1
cert_row_4 3 1 2 5 6 8 716 76 3
cert_rows
cert_pivot_2 4 7 0 1
cert_heightProof 4
cert_coverFacet 0 790
cert_cover_5 0 1 0 1 3 7 274 790 1
cert_coverFacet 1 666
cert_cover_5 1 2 0 2 3 6 146 666 1
cert_coverFacet 2 306
cert_cover_2 2 3 0 4 7 50 306 3
cert_coverFacet 3 802
cert_cover_2 3 4 0 7 8 290 802 3
cert_coverFacet 4 284
cert_cover_2 4 2 1 3 7 28 284 3
cert_coverFacet 5 540
cert_cover_2 5 2 1 3 8 28 540 3
cert_coverFacet 6 716
cert_cover_5 6 3 1 2 5 6 76 716 3
cert_coverFacet 7 248
cert_cover_5 7 0 2 3 4 6 120 248 3
cert_coverFacet 8 376
cert_cover_5 8 0 2 3 4 7 120 376 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0088

end
end BundlePart15

section BundlePart16
/- Source: ProjectionCertificates/R_m16e10q1_0089.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0089

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [779, 307, 611, 589, 233, 425, 902, 562, 402, 658, 220, 396, 780, 628, 660, 496, 35, 259, 515, 169, 73, 265, 521, 97, 289, 577, 50, 146, 274, 530, 546, 386, 642, 770, 76, 140, 268, 524, 84, 148, 532, 580, 388, 644, 772, 200, 392, 776, 112, 304, 560, 208, 400, 656, 224, 608, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_779, vertices_307, vertices_611, vertices_589, vertices_233, vertices_425, vertices_902, vertices_562, vertices_402, vertices_658, vertices_220, vertices_396, vertices_780, vertices_628, vertices_660, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_35, vertices_259, vertices_515, vertices_169, vertices_73, vertices_265, vertices_521, vertices_97, vertices_289, vertices_577, vertices_50, vertices_146, vertices_274, vertices_530, vertices_546, vertices_386, vertices_642, vertices_770, vertices_76, vertices_140, vertices_268, vertices_524, vertices_84, vertices_148, vertices_532, vertices_580, vertices_388, vertices_644, vertices_772, vertices_200, vertices_392, vertices_776, vertices_112, vertices_304, vertices_560, vertices_208, vertices_400, vertices_656, vertices_224, vertices_608, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_779), (false, vertices_307), (false, vertices_611), (false, vertices_589), (false, vertices_233), (false, vertices_425), (true, vertices_146), (true, vertices_530), (true, vertices_386), (true, vertices_642), (true, vertices_140), (true, vertices_268), (true, vertices_84), (true, vertices_148), (true, vertices_532), (true, vertices_388), (true, vertices_644), (true, vertices_772), (true, vertices_112), (true, vertices_560), (true, vertices_208), (true, vertices_400), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 21 23 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_779) then 18 else
  if p.val = (false, vertices_307) then 19 else
  if p.val = (false, vertices_611) then 20 else
  if p.val = (false, vertices_589) then 22 else
  if p.val = (false, vertices_233) then 24 else
  if p.val = (false, vertices_425) then 25 else
  if p.val = (true, vertices_146) then 0 else
  if p.val = (true, vertices_530) then 1 else
  if p.val = (true, vertices_386) then 2 else
  if p.val = (true, vertices_642) then 3 else
  if p.val = (true, vertices_140) then 4 else
  if p.val = (true, vertices_268) then 5 else
  if p.val = (true, vertices_84) then 6 else
  if p.val = (true, vertices_148) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_388) then 9 else
  if p.val = (true, vertices_644) then 10 else
  if p.val = (true, vertices_772) then 11 else
  if p.val = (true, vertices_112) then 12 else
  if p.val = (true, vertices_560) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_400) then 15 else
  if p.val = (true, vertices_656) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_388), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 20 => Sum.inr ⟨(false, vertices_611), by decide +kernel⟩
  | 21 => Sum.inl 1
  | 22 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_233), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_425), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 6 7 8 902 386 1
cert_row_4 1 1 2 3 5 6 220 76 2
cert_row_4 2 1 3 4 5 8 628 84 2
cert_row_4 3 3 4 5 6 7 496 112 3
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 902
cert_cover_5 0 0 0 1 6 7 386 902 1
cert_coverFacet 1 562
cert_cover_2 1 3 0 4 8 50 562 3
cert_coverFacet 2 402
cert_cover_2 2 3 0 6 7 146 402 3
cert_coverFacet 3 658
cert_cover_2 3 3 0 6 8 146 658 3
cert_coverFacet 4 220
cert_cover_5 4 1 1 2 3 5 76 220 2
cert_coverFacet 5 396
cert_cover_2 5 2 1 6 7 140 396 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 628
cert_cover_5 7 2 1 3 4 5 84 628 2
cert_coverFacet 8 660
cert_cover_2 8 3 1 6 8 148 660 3
cert_coverFacet 9 496
cert_cover_5 9 3 3 4 5 6 112 496 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0089

end
end BundlePart16

section BundlePart17
/- Source: ProjectionCertificates/R_m16e10q1_0090.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0090

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 405, 533, 345, 625, 481, 673, 158, 526, 410, 362, 554, 930, 92, 620, 596, 21, 133, 517, 81, 273, 529, 97, 161, 545, 321, 385, 641, 14, 134, 518, 154, 42, 266, 522, 290, 546, 386, 642, 28, 76, 524, 84, 148, 532, 580, 88, 280, 104, 552, 328, 592, 400, 352, 608, 416, 672]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_405, vertices_533, vertices_345, vertices_625, vertices_481, vertices_673, vertices_158, vertices_526, vertices_410, vertices_362, vertices_554, vertices_930, vertices_92, vertices_620, vertices_596] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_133, vertices_517, vertices_81, vertices_273, vertices_529, vertices_97, vertices_161, vertices_545, vertices_321, vertices_385, vertices_641, vertices_14, vertices_134, vertices_518, vertices_154, vertices_42, vertices_266, vertices_522, vertices_290, vertices_546, vertices_386, vertices_642, vertices_28, vertices_76, vertices_524, vertices_84, vertices_148, vertices_532, vertices_580, vertices_88, vertices_280, vertices_104, vertices_552, vertices_328, vertices_592, vertices_400, vertices_352, vertices_608, vertices_416, vertices_672] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_405), (false, vertices_533), (false, vertices_345), (false, vertices_625), (false, vertices_481), (false, vertices_673), (true, vertices_14), (true, vertices_154), (true, vertices_42), (true, vertices_266), (true, vertices_522), (true, vertices_290), (true, vertices_546), (true, vertices_386), (true, vertices_28), (true, vertices_76), (true, vertices_524), (true, vertices_84), (true, vertices_580), (true, vertices_104), (true, vertices_552)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 21 23 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 17 else
  if p.val = (false, vertices_405) then 20 else
  if p.val = (false, vertices_533) then 0 else
  if p.val = (false, vertices_345) then 22 else
  if p.val = (false, vertices_625) then 24 else
  if p.val = (false, vertices_481) then 26 else
  if p.val = (false, vertices_673) then 1 else
  if p.val = (true, vertices_14) then 2 else
  if p.val = (true, vertices_154) then 18 else
  if p.val = (true, vertices_42) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_522) then 5 else
  if p.val = (true, vertices_290) then 6 else
  if p.val = (true, vertices_546) then 7 else
  if p.val = (true, vertices_386) then 8 else
  if p.val = (true, vertices_28) then 9 else
  if p.val = (true, vertices_76) then 10 else
  if p.val = (true, vertices_524) then 11 else
  if p.val = (true, vertices_84) then 12 else
  if p.val = (true, vertices_580) then 13 else
  if p.val = (true, vertices_104) then 14 else
  if p.val = (true, vertices_552) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_533), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_673), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_42), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_76), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_580), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 18 => Sum.inr ⟨(true, vertices_154), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 21 => Sum.inl 2
  | 22 => Sum.inr ⟨(false, vertices_345), by decide +kernel⟩
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 25 => Sum.inl 4
  | 26 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 3 6 154
cert_row_4 1 0 4 6 7 8 930 290 2
cert_row_4 2 0 2 4 5 7 362 42 3
cert_row_4 3 1 2 4 5 8 620 76 2
cert_rows
cert_pivot_2 3 6 0 1
cert_heightProof 4
cert_coverFacet 0 158
cert_cover_5 0 0 0 1 2 3 14 158 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 410
cert_cover_5 2 0 0 2 3 7 154 410 3
cert_coverFacet 3 362
cert_cover_5 3 2 0 2 4 5 42 362 3
cert_coverFacet 4 554
cert_cover_2 4 2 0 4 8 42 554 3
cert_coverFacet 5 930
cert_cover_5 5 1 0 4 6 7 290 930 2
cert_coverFacet 6 92
cert_cover_2 6 2 1 3 5 28 92 3
cert_coverFacet 7 620
cert_cover_5 7 3 1 2 4 5 76 620 2
cert_coverFacet 8 596
cert_cover_2 8 3 1 5 8 84 596 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0090

end
end BundlePart17

section BundlePart18
/- Source: ProjectionCertificates/R_m16e10q1_0091.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0091

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 779, 211, 339, 361, 713, 182, 278, 774, 572, 284, 780, 740, 312, 616, 496, 83, 131, 259, 515, 73, 265, 521, 193, 321, 641, 22, 134, 262, 518, 146, 274, 770, 28, 268, 524, 52, 276, 164, 548, 644, 772, 56, 280, 104, 296, 552, 584, 776, 176, 304, 208, 336, 224, 352, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_779, vertices_211, vertices_339, vertices_361, vertices_713, vertices_182, vertices_278, vertices_774, vertices_572, vertices_284, vertices_780, vertices_740, vertices_312, vertices_616, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_83, vertices_131, vertices_259, vertices_515, vertices_73, vertices_265, vertices_521, vertices_193, vertices_321, vertices_641, vertices_22, vertices_134, vertices_262, vertices_518, vertices_146, vertices_274, vertices_770, vertices_28, vertices_268, vertices_524, vertices_52, vertices_276, vertices_164, vertices_548, vertices_644, vertices_772, vertices_56, vertices_280, vertices_104, vertices_296, vertices_552, vertices_584, vertices_776, vertices_176, vertices_304, vertices_208, vertices_336, vertices_224, vertices_352, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_779), (false, vertices_211), (false, vertices_339), (false, vertices_361), (false, vertices_713), (true, vertices_22), (true, vertices_262), (true, vertices_28), (true, vertices_268), (true, vertices_524), (true, vertices_52), (true, vertices_276), (true, vertices_164), (true, vertices_548), (true, vertices_772), (true, vertices_56), (true, vertices_280), (true, vertices_552), (true, vertices_176), (true, vertices_304), (true, vertices_224), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 17 23 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 18 else
  if p.val = (false, vertices_779) then 20 else
  if p.val = (false, vertices_211) then 21 else
  if p.val = (false, vertices_339) then 22 else
  if p.val = (false, vertices_361) then 24 else
  if p.val = (false, vertices_713) then 25 else
  if p.val = (true, vertices_22) then 0 else
  if p.val = (true, vertices_262) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_52) then 5 else
  if p.val = (true, vertices_276) then 6 else
  if p.val = (true, vertices_164) then 7 else
  if p.val = (true, vertices_548) then 8 else
  if p.val = (true, vertices_772) then 9 else
  if p.val = (true, vertices_56) then 10 else
  if p.val = (true, vertices_280) then 11 else
  if p.val = (true, vertices_552) then 12 else
  if p.val = (true, vertices_176) then 13 else
  if p.val = (true, vertices_304) then 14 else
  if p.val = (true, vertices_224) then 15 else
  if p.val = (true, vertices_608) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_176), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 17 => Sum.inl 1
  | 18 => Sum.inr ⟨(false, vertices_647), by decide +kernel⟩
  | 19 => Sum.inl 0
  | 20 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_211), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_713), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 4 6 182 22 3
cert_row_4 1 1 2 3 4 8 572 28 3
cert_row_4 2 1 4 5 6 8 740 164 2
cert_row_4 3 3 4 5 6 7 496 176 2
cert_rows
cert_pivot_2 0 2 1 3
cert_heightProof 4
cert_coverFacet 0 182
cert_cover_5 0 0 0 1 3 4 22 182 3
cert_coverFacet 1 278
cert_cover_2 1 1 0 3 7 22 278 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 572
cert_cover_5 3 1 1 2 3 4 28 572 3
cert_coverFacet 4 284
cert_cover_2 4 2 1 3 7 28 284 3
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 740
cert_cover_5 6 2 1 4 5 6 164 740 2
cert_coverFacet 7 312
cert_cover_2 7 3 2 4 7 56 312 3
cert_coverFacet 8 616
cert_cover_2 8 4 2 5 8 104 616 3
cert_coverFacet 9 496
cert_cover_5 9 3 3 4 5 6 176 496 2
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0091

end
end BundlePart18

section BundlePart19
/- Source: ProjectionCertificates/R_m16e10q1_0092.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0092

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [339, 173, 565, 405, 625, 481, 662, 602, 362, 778, 402, 898, 620, 652, 424, 904, 21, 37, 133, 561, 81, 273, 97, 161, 321, 385, 74, 266, 522, 82, 146, 274, 530, 322, 386, 642, 770, 44, 140, 524, 148, 532, 548, 644, 104, 168, 296, 584, 392, 648, 776, 592, 400, 352, 608, 416, 896]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_339, vertices_173, vertices_565, vertices_405, vertices_625, vertices_481, vertices_662, vertices_602, vertices_362, vertices_778, vertices_402, vertices_898, vertices_620, vertices_652, vertices_424, vertices_904] (by decide +kernel)
  polygons := literalFinset [vertices_21, vertices_37, vertices_133, vertices_561, vertices_81, vertices_273, vertices_97, vertices_161, vertices_321, vertices_385, vertices_74, vertices_266, vertices_522, vertices_82, vertices_146, vertices_274, vertices_530, vertices_322, vertices_386, vertices_642, vertices_770, vertices_44, vertices_140, vertices_524, vertices_148, vertices_532, vertices_548, vertices_644, vertices_104, vertices_168, vertices_296, vertices_584, vertices_392, vertices_648, vertices_776, vertices_592, vertices_400, vertices_352, vertices_608, vertices_416, vertices_896] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_339), (false, vertices_173), (false, vertices_565), (false, vertices_405), (false, vertices_625), (false, vertices_481), (true, vertices_74), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_530), (true, vertices_386), (true, vertices_642), (true, vertices_770), (true, vertices_524), (true, vertices_644), (true, vertices_104), (true, vertices_296), (true, vertices_584), (true, vertices_392), (true, vertices_648), (true, vertices_776), (true, vertices_896)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 23 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_339) then 18 else
  if p.val = (false, vertices_173) then 20 else
  if p.val = (false, vertices_565) then 24 else
  if p.val = (false, vertices_405) then 21 else
  if p.val = (false, vertices_625) then 25 else
  if p.val = (false, vertices_481) then 27 else
  if p.val = (true, vertices_74) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_642) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_524) then 8 else
  if p.val = (true, vertices_644) then 9 else
  if p.val = (true, vertices_104) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_584) then 12 else
  if p.val = (true, vertices_392) then 13 else
  if p.val = (true, vertices_648) then 14 else
  if p.val = (true, vertices_776) then 15 else
  if p.val = (true, vertices_896) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_644), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_584), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_896), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_339), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_173), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_405), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inl 3
  | 24 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 6 8 662 146 1
cert_row_4 1 0 2 3 5 8 602 74 2
cert_row_4 2 0 2 4 5 7 362 74 2
cert_row_4 3 1 2 4 5 8 620 44 3
cert_rows
cert_pivot_2 6 3 0 1
cert_heightProof 4
cert_coverFacet 0 662
cert_cover_5 0 0 0 1 3 6 146 662 1
cert_coverFacet 1 602
cert_cover_5 1 1 0 2 3 5 74 602 2
cert_coverFacet 2 362
cert_cover_5 2 2 0 2 4 5 74 362 2
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 402
cert_cover_2 4 3 0 6 7 146 402 3
cert_coverFacet 5 898
cert_cover_2 5 6 0 7 8 386 898 3
cert_coverFacet 6 620
cert_cover_5 6 3 1 2 4 5 44 620 3
cert_coverFacet 7 652
cert_cover_2 7 2 1 6 8 140 652 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coverFacet 9 904
cert_cover_2 9 6 2 7 8 392 904 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0092

end
end BundlePart19

section BundlePart20
/- Source: ProjectionCertificates/R_m16e10q1_0093.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0093

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [395, 589, 217, 777, 433, 849, 110, 270, 566, 774, 234, 930, 780, 244, 596, 816, 73, 137, 265, 521, 81, 145, 273, 577, 385, 769, 14, 38, 262, 518, 106, 138, 266, 162, 546, 386, 770, 76, 268, 524, 52, 84, 532, 100, 580, 772, 200, 776, 176, 304, 560, 208, 592, 784, 224, 416, 800]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_395, vertices_589, vertices_217, vertices_777, vertices_433, vertices_849, vertices_110, vertices_270, vertices_566, vertices_774, vertices_234, vertices_930, vertices_780, vertices_244, vertices_596, vertices_816] (by decide +kernel)
  polygons := literalFinset [vertices_73, vertices_137, vertices_265, vertices_521, vertices_81, vertices_145, vertices_273, vertices_577, vertices_385, vertices_769, vertices_14, vertices_38, vertices_262, vertices_518, vertices_106, vertices_138, vertices_266, vertices_162, vertices_546, vertices_386, vertices_770, vertices_76, vertices_268, vertices_524, vertices_52, vertices_84, vertices_532, vertices_100, vertices_580, vertices_772, vertices_200, vertices_776, vertices_176, vertices_304, vertices_560, vertices_208, vertices_592, vertices_784, vertices_224, vertices_416, vertices_800] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_395), (false, vertices_589), (false, vertices_217), (false, vertices_777), (false, vertices_433), (false, vertices_849), (true, vertices_14), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_106), (true, vertices_162), (true, vertices_546), (true, vertices_770), (true, vertices_268), (true, vertices_52), (true, vertices_84), (true, vertices_532), (true, vertices_100), (true, vertices_772), (true, vertices_560), (true, vertices_224), (true, vertices_800)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 24 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_395) then 18 else
  if p.val = (false, vertices_589) then 21 else
  if p.val = (false, vertices_217) then 23 else
  if p.val = (false, vertices_777) then 0 else
  if p.val = (false, vertices_433) then 25 else
  if p.val = (false, vertices_849) then 26 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_106) then 19 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_546) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_268) then 8 else
  if p.val = (true, vertices_52) then 9 else
  if p.val = (true, vertices_84) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_100) then 12 else
  if p.val = (true, vertices_772) then 13 else
  if p.val = (true, vertices_560) then 14 else
  if p.val = (true, vertices_224) then 15 else
  if p.val = (true, vertices_800) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_777), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_800), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_395), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_106), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_589), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_433), by decide +kernel⟩
  | 26 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 2 4 5 106
cert_row_4 1 0 4 6 7 8 930 162 3
cert_row_4 2 0 1 3 4 8 566 38 2
cert_row_4 3 1 3 4 5 6 244 52 3
cert_rows
cert_pivot_2 2 7 0 1
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 0 0 1 2 4 14 110 3
cert_coverFacet 1 270
cert_cover_2 1 1 0 2 7 14 270 3
cert_coverFacet 2 566
cert_cover_5 2 2 0 1 3 4 38 566 2
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 234
cert_cover_5 4 0 0 2 4 6 106 234 3
cert_coverFacet 5 930
cert_cover_5 5 1 0 4 6 7 162 930 3
cert_coverFacet 6 780
cert_cover_2 6 2 1 7 8 268 780 3
cert_coverFacet 7 244
cert_cover_5 7 3 1 3 4 5 52 244 3
cert_coverFacet 8 596
cert_cover_2 8 3 1 5 8 84 596 3
cert_coverFacet 9 816
cert_cover_2 9 4 3 7 8 304 816 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0093

end
end BundlePart20

section BundlePart21
/- Source: ProjectionCertificates/R_m16e10q1_0094.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0094

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [647, 779, 179, 275, 569, 281, 737, 214, 342, 774, 364, 716, 780, 312, 616, 496, 19, 131, 259, 515, 25, 265, 521, 49, 273, 161, 545, 641, 86, 134, 262, 518, 146, 274, 770, 76, 268, 524, 196, 324, 644, 772, 56, 280, 104, 296, 552, 584, 776, 176, 304, 208, 336, 224, 352, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_647, vertices_779, vertices_179, vertices_275, vertices_569, vertices_281, vertices_737, vertices_214, vertices_342, vertices_774, vertices_364, vertices_716, vertices_780, vertices_312, vertices_616, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_19, vertices_131, vertices_259, vertices_515, vertices_25, vertices_265, vertices_521, vertices_49, vertices_273, vertices_161, vertices_545, vertices_641, vertices_86, vertices_134, vertices_262, vertices_518, vertices_146, vertices_274, vertices_770, vertices_76, vertices_268, vertices_524, vertices_196, vertices_324, vertices_644, vertices_772, vertices_56, vertices_280, vertices_104, vertices_296, vertices_552, vertices_584, vertices_776, vertices_176, vertices_304, vertices_208, vertices_336, vertices_224, vertices_352, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_647), (false, vertices_779), (false, vertices_179), (false, vertices_275), (false, vertices_569), (false, vertices_281), (false, vertices_737), (true, vertices_86), (true, vertices_262), (true, vertices_76), (true, vertices_268), (true, vertices_524), (true, vertices_196), (true, vertices_324), (true, vertices_772), (true, vertices_104), (true, vertices_296), (true, vertices_584), (true, vertices_304), (true, vertices_208), (true, vertices_336), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 19 16 22 24 25 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_647) then 17 else
  if p.val = (false, vertices_779) then 20 else
  if p.val = (false, vertices_179) then 21 else
  if p.val = (false, vertices_275) then 0 else
  if p.val = (false, vertices_569) then 23 else
  if p.val = (false, vertices_281) then 1 else
  if p.val = (false, vertices_737) then 26 else
  if p.val = (true, vertices_86) then 18 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_76) then 3 else
  if p.val = (true, vertices_268) then 4 else
  if p.val = (true, vertices_524) then 5 else
  if p.val = (true, vertices_196) then 6 else
  if p.val = (true, vertices_324) then 7 else
  if p.val = (true, vertices_772) then 8 else
  if p.val = (true, vertices_104) then 9 else
  if p.val = (true, vertices_296) then 10 else
  if p.val = (true, vertices_584) then 11 else
  if p.val = (true, vertices_304) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_352) then 15 else
  0
cert_priority
cert_nodeAtPriority_24 0 275 1 281 262 76 268 524 196 324 772 104 296 584 304 208 336 352 647 86 779 179 569 737
cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 1 3 5 86
cert_row_4 1 1 2 5 6 8 716 76 3
cert_row_4 2 1 2 4 5 7 364 76 2
cert_row_4 3 3 4 5 6 7 496 176 2
cert_rows
cert_pivot_2 0 8 1 3
cert_heightProof 4
cert_coverFacet 0 214
cert_cover_5 0 0 0 1 3 6 86 214 3
cert_coverFacet 1 342
cert_cover_5 1 0 0 1 3 7 86 342 3
cert_coverFacet 2 774
cert_cover_2 2 1 0 7 8 262 774 3
cert_coverFacet 3 364
cert_cover_5 3 2 1 2 4 5 76 364 2
cert_coverFacet 4 716
cert_cover_5 4 1 1 2 5 6 76 716 3
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 312
cert_cover_2 6 3 2 4 7 56 312 3
cert_coverFacet 7 616
cert_cover_2 7 4 2 5 8 104 616 3
cert_coverFacet 8 496
cert_cover_5 8 3 3 4 5 6 176 496 2
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0094

end
end BundlePart21

section BundlePart22
/- Source: ProjectionCertificates/R_m16e10q1_0095.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0095

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [299, 157, 557, 709, 409, 929, 30, 526, 534, 346, 554, 626, 482, 468, 596, 736, 13, 133, 517, 153, 41, 265, 289, 545, 385, 641, 14, 22, 518, 26, 42, 266, 522, 82, 530, 98, 290, 546, 322, 28, 524, 84, 148, 532, 196, 580, 280, 552, 336, 592, 400, 224, 608, 416, 672, 448, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_299, vertices_157, vertices_557, vertices_709, vertices_409, vertices_929, vertices_30, vertices_526, vertices_534, vertices_346, vertices_554, vertices_626, vertices_482, vertices_468, vertices_596, vertices_736] (by decide +kernel)
  polygons := literalFinset [vertices_13, vertices_133, vertices_517, vertices_153, vertices_41, vertices_265, vertices_289, vertices_545, vertices_385, vertices_641, vertices_14, vertices_22, vertices_518, vertices_26, vertices_42, vertices_266, vertices_522, vertices_82, vertices_530, vertices_98, vertices_290, vertices_546, vertices_322, vertices_28, vertices_524, vertices_84, vertices_148, vertices_532, vertices_196, vertices_580, vertices_280, vertices_552, vertices_336, vertices_592, vertices_400, vertices_224, vertices_608, vertices_416, vertices_672, vertices_448, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_299), (false, vertices_157), (false, vertices_557), (false, vertices_709), (false, vertices_409), (false, vertices_929), (true, vertices_14), (true, vertices_22), (true, vertices_518), (true, vertices_26), (true, vertices_522), (true, vertices_82), (true, vertices_530), (true, vertices_98), (true, vertices_546), (true, vertices_322), (true, vertices_84), (true, vertices_532), (true, vertices_336), (true, vertices_592), (true, vertices_224), (true, vertices_608), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_299) then 18 else
  if p.val = (false, vertices_157) then 23 else
  if p.val = (false, vertices_557) then 20 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_409) then 24 else
  if p.val = (false, vertices_929) then 27 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_518) then 2 else
  if p.val = (true, vertices_26) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_82) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_98) then 7 else
  if p.val = (true, vertices_546) then 8 else
  if p.val = (true, vertices_322) then 9 else
  if p.val = (true, vertices_84) then 10 else
  if p.val = (true, vertices_532) then 11 else
  if p.val = (true, vertices_336) then 12 else
  if p.val = (true, vertices_592) then 13 else
  if p.val = (true, vertices_224) then 14 else
  if p.val = (true, vertices_608) then 15 else
  if p.val = (true, vertices_448) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_26), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_82), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_98), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_322), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_299), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_557), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_157), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_929), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 5 7 346 26 3
cert_row_4 1 0 3 4 5 8 626 82 2
cert_row_4 2 0 4 5 6 7 482 98 3
cert_row_4 3 1 3 5 6 7 468 84 3
cert_rows
cert_pivot_2 2 8 0 1
cert_heightProof 4
cert_coverFacet 0 30
cert_cover_2 0 1 0 2 3 14 30 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 534
cert_cover_2 2 1 0 3 8 22 534 3
cert_coverFacet 3 346
cert_cover_5 3 0 0 2 3 5 26 346 3
cert_coverFacet 4 554
cert_cover_2 4 2 0 4 8 42 554 3
cert_coverFacet 5 626
cert_cover_5 5 1 0 3 4 5 82 626 2
cert_coverFacet 6 482
cert_cover_5 6 2 0 4 5 6 98 482 3
cert_coverFacet 7 468
cert_cover_5 7 3 1 3 5 6 84 468 3
cert_coverFacet 8 596
cert_cover_2 8 3 1 5 8 84 596 3
cert_coverFacet 9 736
cert_cover_2 9 5 4 6 8 224 736 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0095

end
end BundlePart22

section BundlePart23
/- Source: ProjectionCertificates/R_m16e10q1_0096.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0096

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [355, 181, 665, 305, 849, 737, 110, 526, 310, 774, 714, 834, 412, 236, 780, 792, 49, 145, 273, 529, 97, 161, 289, 321, 577, 641, 14, 38, 262, 518, 74, 522, 98, 290, 322, 578, 770, 108, 140, 268, 524, 52, 148, 276, 164, 772, 152, 280, 536, 200, 648, 776, 304, 784, 224, 704, 832]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_355, vertices_181, vertices_665, vertices_305, vertices_849, vertices_737, vertices_110, vertices_526, vertices_310, vertices_774, vertices_714, vertices_834, vertices_412, vertices_236, vertices_780, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_49, vertices_145, vertices_273, vertices_529, vertices_97, vertices_161, vertices_289, vertices_321, vertices_577, vertices_641, vertices_14, vertices_38, vertices_262, vertices_518, vertices_74, vertices_522, vertices_98, vertices_290, vertices_322, vertices_578, vertices_770, vertices_108, vertices_140, vertices_268, vertices_524, vertices_52, vertices_148, vertices_276, vertices_164, vertices_772, vertices_152, vertices_280, vertices_536, vertices_200, vertices_648, vertices_776, vertices_304, vertices_784, vertices_224, vertices_704, vertices_832] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_355), (false, vertices_181), (false, vertices_665), (false, vertices_305), (false, vertices_849), (false, vertices_737), (true, vertices_14), (true, vertices_38), (true, vertices_262), (true, vertices_518), (true, vertices_74), (true, vertices_522), (true, vertices_578), (true, vertices_770), (true, vertices_108), (true, vertices_140), (true, vertices_268), (true, vertices_524), (true, vertices_276), (true, vertices_772), (true, vertices_280), (true, vertices_200), (true, vertices_776)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 24 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_355) then 18 else
  if p.val = (false, vertices_181) then 20 else
  if p.val = (false, vertices_665) then 23 else
  if p.val = (false, vertices_305) then 0 else
  if p.val = (false, vertices_849) then 25 else
  if p.val = (false, vertices_737) then 27 else
  if p.val = (true, vertices_14) then 1 else
  if p.val = (true, vertices_38) then 2 else
  if p.val = (true, vertices_262) then 3 else
  if p.val = (true, vertices_518) then 4 else
  if p.val = (true, vertices_74) then 5 else
  if p.val = (true, vertices_522) then 6 else
  if p.val = (true, vertices_578) then 7 else
  if p.val = (true, vertices_770) then 8 else
  if p.val = (true, vertices_108) then 21 else
  if p.val = (true, vertices_140) then 9 else
  if p.val = (true, vertices_268) then 10 else
  if p.val = (true, vertices_524) then 11 else
  if p.val = (true, vertices_276) then 12 else
  if p.val = (true, vertices_772) then 13 else
  if p.val = (true, vertices_280) then 14 else
  if p.val = (true, vertices_200) then 15 else
  if p.val = (true, vertices_776) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_305), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_74), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_200), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_355), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_181), by decide +kernel⟩
  | 21 => Sum.inr ⟨(true, vertices_108), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_665), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(false, vertices_849), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_737), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 5 6 8 714 74 3
cert_row_2 1 1 2 4 5 108
cert_row_4 2 0 1 3 4 7 310 38 2
cert_row_4 3 1 2 3 6 7 412 140 2
cert_rows
cert_pivot_2 8 5 0 1
cert_heightProof 4
cert_coverFacet 0 110
cert_cover_5 0 1 0 1 2 4 14 110 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 310
cert_cover_5 2 2 0 1 3 4 38 310 2
cert_coverFacet 3 774
cert_cover_2 3 1 0 7 8 262 774 3
cert_coverFacet 4 714
cert_cover_5 4 0 0 2 5 6 74 714 3
cert_coverFacet 5 834
cert_cover_2 5 5 0 7 8 322 834 3
cert_coverFacet 6 412
cert_cover_5 6 3 1 2 3 6 140 412 2
cert_coverFacet 7 236
cert_cover_5 7 1 1 2 4 6 108 236 3
cert_coverFacet 8 780
cert_cover_2 8 2 1 7 8 268 780 3
cert_coverFacet 9 792
cert_cover_2 9 3 2 7 8 280 792 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0096

end
end BundlePart23

section BundlePart24
/- Source: ProjectionCertificates/R_m16e10q1_0097.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0097

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [803, 451, 643, 333, 653, 773, 217, 566, 666, 434, 60, 540, 108, 868, 120, 496, 131, 259, 515, 13, 261, 517, 73, 137, 193, 321, 641, 769, 50, 146, 530, 290, 546, 386, 642, 28, 44, 76, 524, 52, 532, 100, 548, 324, 772, 56, 88, 152, 536, 104, 648, 112, 432, 208, 352, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_803, vertices_451, vertices_643, vertices_333, vertices_653, vertices_773, vertices_217, vertices_566, vertices_666, vertices_434, vertices_60, vertices_540, vertices_108, vertices_868, vertices_120, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_131, vertices_259, vertices_515, vertices_13, vertices_261, vertices_517, vertices_73, vertices_137, vertices_193, vertices_321, vertices_641, vertices_769, vertices_50, vertices_146, vertices_530, vertices_290, vertices_546, vertices_386, vertices_642, vertices_28, vertices_44, vertices_76, vertices_524, vertices_52, vertices_532, vertices_100, vertices_548, vertices_324, vertices_772, vertices_56, vertices_88, vertices_152, vertices_536, vertices_104, vertices_648, vertices_112, vertices_432, vertices_208, vertices_352, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_803), (false, vertices_451), (false, vertices_643), (false, vertices_333), (false, vertices_653), (false, vertices_773), (false, vertices_217), (true, vertices_50), (true, vertices_146), (true, vertices_530), (true, vertices_28), (true, vertices_44), (true, vertices_52), (true, vertices_532), (true, vertices_100), (true, vertices_548), (true, vertices_56), (true, vertices_536), (true, vertices_104), (true, vertices_112), (true, vertices_432), (true, vertices_352)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 16 19 22 24 26 27 28 29 30
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_803) then 17 else
  if p.val = (false, vertices_451) then 18 else
  if p.val = (false, vertices_643) then 0 else
  if p.val = (false, vertices_333) then 20 else
  if p.val = (false, vertices_653) then 21 else
  if p.val = (false, vertices_773) then 1 else
  if p.val = (false, vertices_217) then 23 else
  if p.val = (true, vertices_50) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_28) then 5 else
  if p.val = (true, vertices_44) then 6 else
  if p.val = (true, vertices_52) then 7 else
  if p.val = (true, vertices_532) then 8 else
  if p.val = (true, vertices_100) then 9 else
  if p.val = (true, vertices_548) then 10 else
  if p.val = (true, vertices_56) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_104) then 13 else
  if p.val = (true, vertices_112) then 14 else
  if p.val = (true, vertices_432) then 25 else
  if p.val = (true, vertices_352) then 15 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_643), by decide +kernel⟩
  | 1 => Sum.inr ⟨(false, vertices_773), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_50), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_100), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_104), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_112), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_352), by decide +kernel⟩
  | 16 => Sum.inl 0
  | 17 => Sum.inr ⟨(false, vertices_803), by decide +kernel⟩
  | 18 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_653), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_217), by decide +kernel⟩
  | 24 => Sum.inl 3
  | 25 => Sum.inr ⟨(true, vertices_432), by decide +kernel⟩
  | 26 => Sum.inl 4
  | 27 => Sum.inl 5
  | 28 => Sum.inl 6
  | 29 => Sum.inl 7
  | 30 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 3 6 8 666 146 1
cert_row_2 1 3 4 6 7 432
cert_row_4 2 0 1 3 4 8 566 50 1
cert_row_4 3 1 4 5 7 8 868 100 3
cert_rows
cert_pivot_2 2 6 0 1
cert_heightProof 4
cert_coverFacet 0 566
cert_cover_5 0 2 0 1 3 4 50 566 1
cert_coverFacet 1 666
cert_cover_5 1 0 0 2 3 6 146 666 1
cert_coverFacet 2 434
cert_cover_5 2 1 0 3 4 6 50 434 3
cert_coverFacet 3 60
cert_cover_2 3 2 1 3 4 28 60 3
cert_coverFacet 4 540
cert_cover_2 4 2 1 3 8 28 540 3
cert_coverFacet 5 108
cert_cover_2 5 2 1 4 5 44 108 3
cert_coverFacet 6 868
cert_cover_5 6 3 1 4 5 7 100 868 3
cert_coverFacet 7 120
cert_cover_2 7 3 2 4 5 56 120 3
cert_coverFacet 8 496
cert_cover_5 8 1 3 4 5 6 112 496 3
cert_coveringFacets_2
cert_coveringProof_4
cert_certificate 4 9
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0097

end
end BundlePart24

section BundlePart25
/- Source: ProjectionCertificates/R_m16e10q1_0098.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0098

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [307, 333, 789, 709, 361, 625, 782, 666, 394, 242, 786, 418, 236, 652, 424, 720, 69, 261, 517, 329, 49, 273, 529, 97, 289, 577, 138, 266, 522, 50, 146, 274, 530, 162, 290, 386, 770, 76, 140, 268, 524, 196, 644, 772, 104, 168, 296, 392, 648, 112, 208, 592, 656, 784, 224, 416, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_307, vertices_333, vertices_789, vertices_709, vertices_361, vertices_625, vertices_782, vertices_666, vertices_394, vertices_242, vertices_786, vertices_418, vertices_236, vertices_652, vertices_424, vertices_720] (by decide +kernel)
  polygons := literalFinset [vertices_69, vertices_261, vertices_517, vertices_329, vertices_49, vertices_273, vertices_529, vertices_97, vertices_289, vertices_577, vertices_138, vertices_266, vertices_522, vertices_50, vertices_146, vertices_274, vertices_530, vertices_162, vertices_290, vertices_386, vertices_770, vertices_76, vertices_140, vertices_268, vertices_524, vertices_196, vertices_644, vertices_772, vertices_104, vertices_168, vertices_296, vertices_392, vertices_648, vertices_112, vertices_208, vertices_592, vertices_656, vertices_784, vertices_224, vertices_416, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_307), (false, vertices_333), (false, vertices_789), (false, vertices_709), (false, vertices_361), (false, vertices_625), (true, vertices_138), (true, vertices_266), (true, vertices_522), (true, vertices_146), (true, vertices_530), (true, vertices_162), (true, vertices_386), (true, vertices_770), (true, vertices_140), (true, vertices_524), (true, vertices_168), (true, vertices_392), (true, vertices_648), (true, vertices_208), (true, vertices_656), (true, vertices_224), (true, vertices_416)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 19 22 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_307) then 18 else
  if p.val = (false, vertices_333) then 23 else
  if p.val = (false, vertices_789) then 20 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_361) then 24 else
  if p.val = (false, vertices_625) then 26 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_266) then 1 else
  if p.val = (true, vertices_522) then 2 else
  if p.val = (true, vertices_146) then 3 else
  if p.val = (true, vertices_530) then 4 else
  if p.val = (true, vertices_162) then 5 else
  if p.val = (true, vertices_386) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_140) then 8 else
  if p.val = (true, vertices_524) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_392) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_208) then 13 else
  if p.val = (true, vertices_656) then 14 else
  if p.val = (true, vertices_224) then 15 else
  if p.val = (true, vertices_416) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_146), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_162), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_140), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_392), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_224), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_307), by decide +kernel⟩
  | 19 => Sum.inl 1
  | 20 => Sum.inr ⟨(false, vertices_789), by decide +kernel⟩
  | 21 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_333), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_625), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 7 8 782 266 1
cert_row_4 1 0 2 3 6 8 666 138 2
cert_row_4 2 0 3 4 5 6 242 50 3
cert_row_4 3 1 2 4 5 6 236 76 2
cert_rows
cert_pivot_2 7 8 0 1
cert_heightProof 4
cert_coverFacet 0 782
cert_cover_5 0 0 0 1 2 7 266 782 1
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
cert_coverFacet 6 236
cert_cover_5 6 3 1 2 4 5 76 236 2
cert_coverFacet 7 652
cert_cover_2 7 2 1 6 8 140 652 3
cert_coverFacet 8 424
cert_cover_2 8 4 2 6 7 168 424 3
cert_coverFacet 9 720
cert_cover_2 9 5 3 6 8 208 720 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0098

end
end BundlePart25

section BundlePart26
/- Source: ProjectionCertificates/R_m16e10q1_0099.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0099

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [331, 709, 313, 681, 585, 481, 590, 566, 214, 778, 466, 786, 436, 676, 568, 792, 41, 73, 265, 521, 161, 289, 193, 321, 577, 641, 22, 70, 518, 74, 266, 522, 210, 274, 530, 322, 770, 52, 148, 164, 548, 196, 580, 644, 56, 280, 536, 552, 584, 776, 304, 560, 400, 784, 416, 672, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_331, vertices_709, vertices_313, vertices_681, vertices_585, vertices_481, vertices_590, vertices_566, vertices_214, vertices_778, vertices_466, vertices_786, vertices_436, vertices_676, vertices_568, vertices_792] (by decide +kernel)
  polygons := literalFinset [vertices_41, vertices_73, vertices_265, vertices_521, vertices_161, vertices_289, vertices_193, vertices_321, vertices_577, vertices_641, vertices_22, vertices_70, vertices_518, vertices_74, vertices_266, vertices_522, vertices_210, vertices_274, vertices_530, vertices_322, vertices_770, vertices_52, vertices_148, vertices_164, vertices_548, vertices_196, vertices_580, vertices_644, vertices_56, vertices_280, vertices_536, vertices_552, vertices_584, vertices_776, vertices_304, vertices_560, vertices_400, vertices_784, vertices_416, vertices_672, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_331), (false, vertices_709), (false, vertices_313), (false, vertices_681), (false, vertices_585), (false, vertices_481), (true, vertices_22), (true, vertices_70), (true, vertices_518), (true, vertices_522), (true, vertices_210), (true, vertices_274), (true, vertices_530), (true, vertices_770), (true, vertices_52), (true, vertices_148), (true, vertices_164), (true, vertices_548), (true, vertices_536), (true, vertices_776), (true, vertices_560), (true, vertices_400), (true, vertices_784)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 25 26 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_331) then 18 else
  if p.val = (false, vertices_709) then 21 else
  if p.val = (false, vertices_313) then 23 else
  if p.val = (false, vertices_681) then 24 else
  if p.val = (false, vertices_585) then 0 else
  if p.val = (false, vertices_481) then 27 else
  if p.val = (true, vertices_22) then 1 else
  if p.val = (true, vertices_70) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_522) then 4 else
  if p.val = (true, vertices_210) then 19 else
  if p.val = (true, vertices_274) then 5 else
  if p.val = (true, vertices_530) then 6 else
  if p.val = (true, vertices_770) then 7 else
  if p.val = (true, vertices_52) then 8 else
  if p.val = (true, vertices_148) then 9 else
  if p.val = (true, vertices_164) then 10 else
  if p.val = (true, vertices_548) then 11 else
  if p.val = (true, vertices_536) then 12 else
  if p.val = (true, vertices_776) then 13 else
  if p.val = (true, vertices_560) then 14 else
  if p.val = (true, vertices_400) then 15 else
  if p.val = (true, vertices_784) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_585), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_22), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_522), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_274), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_530), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_770), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_148), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_164), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_548), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_536), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_776), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_560), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_400), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_784), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_331), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_210), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_709), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_313), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_681), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inl 4
  | 27 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 2 5 8 590 70 2
cert_row_2 1 0 3 5 6 210
cert_row_4 2 0 1 3 4 8 566 22 3
cert_row_4 3 1 3 4 6 7 436 52 3
cert_rows
cert_pivot_2 2 5 0 1
cert_heightProof 4
cert_coverFacet 0 590
cert_cover_5 0 0 0 1 2 5 70 590 2
cert_coverFacet 1 566
cert_cover_5 1 2 0 1 3 4 22 566 3
cert_coverFacet 2 214
cert_cover_5 2 1 0 1 3 5 22 214 3
cert_coverFacet 3 778
cert_cover_2 3 2 0 7 8 266 778 3
cert_coverFacet 4 466
cert_cover_5 4 1 0 3 5 7 210 466 3
cert_coverFacet 5 786
cert_cover_2 5 3 0 7 8 274 786 3
cert_coverFacet 6 436
cert_cover_5 6 3 1 3 4 6 52 436 3
cert_coverFacet 7 676
cert_cover_2 7 4 1 6 8 164 676 3
cert_coverFacet 8 568
cert_cover_2 8 3 2 4 8 56 568 3
cert_coverFacet 9 792
cert_cover_2 9 3 2 7 8 280 792 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0099

end
end BundlePart26

section BundlePart27
/- Source: ProjectionCertificates/R_m16e10q1_0100.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0100

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [583, 779, 451, 117, 805, 481, 426, 650, 722, 668, 284, 780, 308, 596, 248, 312, 67, 259, 515, 37, 69, 517, 97, 289, 449, 769, 138, 266, 522, 194, 578, 386, 642, 28, 268, 524, 52, 84, 276, 532, 292, 580, 772, 56, 152, 280, 168, 296, 648, 776, 112, 304, 208, 592, 656, 224, 416]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_583, vertices_779, vertices_451, vertices_117, vertices_805, vertices_481, vertices_426, vertices_650, vertices_722, vertices_668, vertices_284, vertices_780, vertices_308, vertices_596, vertices_248, vertices_312] (by decide +kernel)
  polygons := literalFinset [vertices_67, vertices_259, vertices_515, vertices_37, vertices_69, vertices_517, vertices_97, vertices_289, vertices_449, vertices_769, vertices_138, vertices_266, vertices_522, vertices_194, vertices_578, vertices_386, vertices_642, vertices_28, vertices_268, vertices_524, vertices_52, vertices_84, vertices_276, vertices_532, vertices_292, vertices_580, vertices_772, vertices_56, vertices_152, vertices_280, vertices_168, vertices_296, vertices_648, vertices_776, vertices_112, vertices_304, vertices_208, vertices_592, vertices_656, vertices_224, vertices_416] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_583), (false, vertices_779), (false, vertices_451), (false, vertices_117), (false, vertices_805), (false, vertices_481), (true, vertices_138), (true, vertices_642), (true, vertices_28), (true, vertices_268), (true, vertices_524), (true, vertices_276), (true, vertices_532), (true, vertices_56), (true, vertices_152), (true, vertices_280), (true, vertices_168), (true, vertices_296), (true, vertices_648), (true, vertices_304), (true, vertices_208), (true, vertices_592), (true, vertices_656)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 23 24 25 26 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_583) then 18 else
  if p.val = (false, vertices_779) then 19 else
  if p.val = (false, vertices_451) then 27 else
  if p.val = (false, vertices_117) then 21 else
  if p.val = (false, vertices_805) then 22 else
  if p.val = (false, vertices_481) then 28 else
  if p.val = (true, vertices_138) then 0 else
  if p.val = (true, vertices_642) then 1 else
  if p.val = (true, vertices_28) then 2 else
  if p.val = (true, vertices_268) then 3 else
  if p.val = (true, vertices_524) then 4 else
  if p.val = (true, vertices_276) then 5 else
  if p.val = (true, vertices_532) then 6 else
  if p.val = (true, vertices_56) then 7 else
  if p.val = (true, vertices_152) then 8 else
  if p.val = (true, vertices_280) then 9 else
  if p.val = (true, vertices_168) then 10 else
  if p.val = (true, vertices_296) then 11 else
  if p.val = (true, vertices_648) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_208) then 14 else
  if p.val = (true, vertices_592) then 15 else
  if p.val = (true, vertices_656) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_138), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_642), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_532), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_56), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_152), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_280), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_168), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_296), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_648), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_208), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_592), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_656), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_583), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_779), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_117), by decide +kernel⟩
  | 22 => Sum.inr ⟨(false, vertices_805), by decide +kernel⟩
  | 23 => Sum.inl 2
  | 24 => Sum.inl 3
  | 25 => Sum.inl 4
  | 26 => Sum.inl 5
  | 27 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 28 => Sum.inr ⟨(false, vertices_481), by decide +kernel⟩
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 2 4 6 7 426 138 2
cert_row_4 1 0 3 5 6 8 722 194 1
cert_row_4 2 1 2 3 6 8 668 28 3
cert_row_4 3 2 3 4 5 6 248 56 3
cert_rows
cert_pivot_2 7 0 1 2
cert_heightProof 4
cert_coverFacet 0 426
cert_cover_5 0 0 0 2 4 6 138 426 2
cert_coverFacet 1 650
cert_cover_2 1 2 0 6 8 138 650 3
cert_coverFacet 2 722
cert_cover_5 2 1 0 3 5 6 194 722 1
cert_coverFacet 3 668
cert_cover_5 3 2 1 2 3 6 28 668 3
cert_coverFacet 4 284
cert_cover_2 4 2 1 3 7 28 284 3
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 308
cert_cover_2 6 3 1 4 7 52 308 3
cert_coverFacet 7 596
cert_cover_2 7 3 1 5 8 84 596 3
cert_coverFacet 8 248
cert_cover_5 8 3 2 3 4 5 56 248 3
cert_coverFacet 9 312
cert_cover_2 9 3 2 4 7 56 312 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0100

end
end BundlePart27

section BundlePart28
/- Source: ProjectionCertificates/R_m16e10q1_0101.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0101

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [451, 661, 601, 409, 361, 705, 558, 182, 710, 434, 866, 284, 540, 300, 308, 616, 25, 73, 265, 145, 529, 193, 321, 577, 385, 641, 38, 134, 518, 178, 290, 546, 194, 322, 578, 386, 28, 44, 268, 524, 52, 148, 276, 532, 292, 644, 280, 536, 104, 296, 552, 584, 304, 400, 352, 608, 704]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_451, vertices_661, vertices_601, vertices_409, vertices_361, vertices_705, vertices_558, vertices_182, vertices_710, vertices_434, vertices_866, vertices_284, vertices_540, vertices_300, vertices_308, vertices_616] (by decide +kernel)
  polygons := literalFinset [vertices_25, vertices_73, vertices_265, vertices_145, vertices_529, vertices_193, vertices_321, vertices_577, vertices_385, vertices_641, vertices_38, vertices_134, vertices_518, vertices_178, vertices_290, vertices_546, vertices_194, vertices_322, vertices_578, vertices_386, vertices_28, vertices_44, vertices_268, vertices_524, vertices_52, vertices_148, vertices_276, vertices_532, vertices_292, vertices_644, vertices_280, vertices_536, vertices_104, vertices_296, vertices_552, vertices_584, vertices_304, vertices_400, vertices_352, vertices_608, vertices_704] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_451), (false, vertices_661), (false, vertices_601), (false, vertices_409), (false, vertices_361), (false, vertices_705), (true, vertices_38), (true, vertices_134), (true, vertices_518), (true, vertices_178), (true, vertices_290), (true, vertices_546), (true, vertices_578), (true, vertices_28), (true, vertices_44), (true, vertices_268), (true, vertices_524), (true, vertices_52), (true, vertices_276), (true, vertices_292), (true, vertices_552), (true, vertices_304), (true, vertices_608)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 26 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_451) then 18 else
  if p.val = (false, vertices_661) then 21 else
  if p.val = (false, vertices_601) then 23 else
  if p.val = (false, vertices_409) then 24 else
  if p.val = (false, vertices_361) then 25 else
  if p.val = (false, vertices_705) then 0 else
  if p.val = (true, vertices_38) then 1 else
  if p.val = (true, vertices_134) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_178) then 19 else
  if p.val = (true, vertices_290) then 4 else
  if p.val = (true, vertices_546) then 5 else
  if p.val = (true, vertices_578) then 6 else
  if p.val = (true, vertices_28) then 7 else
  if p.val = (true, vertices_44) then 8 else
  if p.val = (true, vertices_268) then 9 else
  if p.val = (true, vertices_524) then 10 else
  if p.val = (true, vertices_52) then 11 else
  if p.val = (true, vertices_276) then 12 else
  if p.val = (true, vertices_292) then 13 else
  if p.val = (true, vertices_552) then 14 else
  if p.val = (true, vertices_304) then 15 else
  if p.val = (true, vertices_608) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(false, vertices_705), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_38), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_134), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_290), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_546), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_578), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_28), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_44), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_52), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_552), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_608), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_451), by decide +kernel⟩
  | 19 => Sum.inr ⟨(true, vertices_178), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_661), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_601), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_409), by decide +kernel⟩
  | 25 => Sum.inr ⟨(false, vertices_361), by decide +kernel⟩
  | 26 => Sum.inl 3
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_2 0 0 3 4 6 178
cert_row_4 1 0 1 2 4 8 558 38 2
cert_row_4 2 0 1 5 6 8 710 134 2
cert_row_4 3 0 4 5 7 8 866 290 2
cert_rows
cert_pivot_2 3 2 1 0
cert_heightProof 4
cert_coverFacet 0 558
cert_cover_5 0 1 0 1 2 4 38 558 2
cert_coverFacet 1 182
cert_cover_5 1 0 0 1 3 4 38 182 2
cert_coverFacet 2 710
cert_cover_5 2 2 0 1 5 6 134 710 2
cert_coverFacet 3 434
cert_cover_5 3 0 0 3 4 7 178 434 3
cert_coverFacet 4 866
cert_cover_5 4 3 0 4 5 7 290 866 2
cert_coverFacet 5 284
cert_cover_2 5 2 1 3 7 28 284 3
cert_coverFacet 6 540
cert_cover_2 6 2 1 3 8 28 540 3
cert_coverFacet 7 300
cert_cover_2 7 2 1 4 7 44 300 3
cert_coverFacet 8 308
cert_cover_2 8 3 1 4 7 52 308 3
cert_coverFacet 9 616
cert_cover_2 9 4 2 5 8 104 616 3
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0101

end
end BundlePart28

section BundlePart29
/- Source: ProjectionCertificates/R_m16e10q1_0102.lean -/





section

/-! Literal finite certificate from the supplement. Prepared, not yet kernel checked. -/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0102

open FiniteProjection
set_option maxRecDepth 10000

-- Normalized finite-set data.
projection_vertex_sets [203, 587, 565, 185, 809, 721, 270, 526, 598, 454, 426, 780, 308, 340, 804, 496, 75, 41, 137, 521, 49, 145, 529, 545, 193, 577, 14, 70, 262, 518, 138, 266, 522, 194, 578, 386, 268, 524, 52, 84, 276, 532, 292, 548, 324, 772, 168, 296, 776, 176, 304, 208, 336, 592, 416, 800, 448]

noncomputable def boundary : Boundary 9 where
  facets := literalFinset [vertices_203, vertices_587, vertices_565, vertices_185, vertices_809, vertices_721, vertices_270, vertices_526, vertices_598, vertices_454, vertices_426, vertices_780, vertices_308, vertices_340, vertices_804, vertices_496] (by decide +kernel)
  polygons := literalFinset [vertices_75, vertices_41, vertices_137, vertices_521, vertices_49, vertices_145, vertices_529, vertices_545, vertices_193, vertices_577, vertices_14, vertices_70, vertices_262, vertices_518, vertices_138, vertices_266, vertices_522, vertices_194, vertices_578, vertices_386, vertices_268, vertices_524, vertices_52, vertices_84, vertices_276, vertices_532, vertices_292, vertices_548, vertices_324, vertices_772, vertices_168, vertices_296, vertices_776, vertices_176, vertices_304, vertices_208, vertices_336, vertices_592, vertices_416, vertices_800, vertices_448] (by decide +kernel)
  planeCache := literalFinset [(false, vertices_203), (false, vertices_587), (false, vertices_565), (false, vertices_185), (false, vertices_809), (false, vertices_721), (true, vertices_14), (true, vertices_70), (true, vertices_262), (true, vertices_518), (true, vertices_266), (true, vertices_386), (true, vertices_268), (true, vertices_524), (true, vertices_84), (true, vertices_276), (true, vertices_292), (true, vertices_324), (true, vertices_772), (true, vertices_304), (true, vertices_336), (true, vertices_416), (true, vertices_448)] (by decide +kernel)
  planeCache_correct := by decide +kernel

cert_pointPriority 17 20 22 25 27 28 29 30 31
noncomputable def planePriority (p : PlaneNode boundary) : ℕ :=
  if p.val = (false, vertices_203) then 18 else
  if p.val = (false, vertices_587) then 19 else
  if p.val = (false, vertices_565) then 21 else
  if p.val = (false, vertices_185) then 23 else
  if p.val = (false, vertices_809) then 24 else
  if p.val = (false, vertices_721) then 26 else
  if p.val = (true, vertices_14) then 0 else
  if p.val = (true, vertices_70) then 1 else
  if p.val = (true, vertices_262) then 2 else
  if p.val = (true, vertices_518) then 3 else
  if p.val = (true, vertices_266) then 4 else
  if p.val = (true, vertices_386) then 5 else
  if p.val = (true, vertices_268) then 6 else
  if p.val = (true, vertices_524) then 7 else
  if p.val = (true, vertices_84) then 8 else
  if p.val = (true, vertices_276) then 9 else
  if p.val = (true, vertices_292) then 10 else
  if p.val = (true, vertices_324) then 11 else
  if p.val = (true, vertices_772) then 12 else
  if p.val = (true, vertices_304) then 13 else
  if p.val = (true, vertices_336) then 14 else
  if p.val = (true, vertices_416) then 15 else
  if p.val = (true, vertices_448) then 16 else
  0
cert_priority
noncomputable def nodeAtPriority : ℕ → Node boundary
  | 0 => Sum.inr ⟨(true, vertices_14), by decide +kernel⟩
  | 1 => Sum.inr ⟨(true, vertices_70), by decide +kernel⟩
  | 2 => Sum.inr ⟨(true, vertices_262), by decide +kernel⟩
  | 3 => Sum.inr ⟨(true, vertices_518), by decide +kernel⟩
  | 4 => Sum.inr ⟨(true, vertices_266), by decide +kernel⟩
  | 5 => Sum.inr ⟨(true, vertices_386), by decide +kernel⟩
  | 6 => Sum.inr ⟨(true, vertices_268), by decide +kernel⟩
  | 7 => Sum.inr ⟨(true, vertices_524), by decide +kernel⟩
  | 8 => Sum.inr ⟨(true, vertices_84), by decide +kernel⟩
  | 9 => Sum.inr ⟨(true, vertices_276), by decide +kernel⟩
  | 10 => Sum.inr ⟨(true, vertices_292), by decide +kernel⟩
  | 11 => Sum.inr ⟨(true, vertices_324), by decide +kernel⟩
  | 12 => Sum.inr ⟨(true, vertices_772), by decide +kernel⟩
  | 13 => Sum.inr ⟨(true, vertices_304), by decide +kernel⟩
  | 14 => Sum.inr ⟨(true, vertices_336), by decide +kernel⟩
  | 15 => Sum.inr ⟨(true, vertices_416), by decide +kernel⟩
  | 16 => Sum.inr ⟨(true, vertices_448), by decide +kernel⟩
  | 17 => Sum.inl 0
  | 18 => Sum.inr ⟨(false, vertices_203), by decide +kernel⟩
  | 19 => Sum.inr ⟨(false, vertices_587), by decide +kernel⟩
  | 20 => Sum.inl 1
  | 21 => Sum.inr ⟨(false, vertices_565), by decide +kernel⟩
  | 22 => Sum.inl 2
  | 23 => Sum.inr ⟨(false, vertices_185), by decide +kernel⟩
  | 24 => Sum.inr ⟨(false, vertices_809), by decide +kernel⟩
  | 25 => Sum.inl 3
  | 26 => Sum.inr ⟨(false, vertices_721), by decide +kernel⟩
  | 27 => Sum.inl 4
  | 28 => Sum.inl 5
  | 29 => Sum.inl 6
  | 30 => Sum.inl 7
  | 31 => Sum.inl 8
  | _ => Sum.inl 0

cert_priority_injective
cert_incidenceProof
cert_row_4 0 0 1 3 5 8 598 70 2
cert_row_4 1 0 1 5 6 7 454 70 3
cert_row_4 2 0 2 4 6 7 426 138 2
cert_row_4 3 3 4 5 6 7 496 176 2
cert_rows
cert_pivot_2 8 1 0 3
cert_heightProof 4
cert_coverFacet 0 270
cert_cover_2 0 1 0 2 7 14 270 3
cert_coverFacet 1 526
cert_cover_2 1 1 0 2 8 14 526 3
cert_coverFacet 2 598
cert_cover_5 2 0 0 1 3 5 70 598 2
cert_coverFacet 3 454
cert_cover_5 3 1 0 1 5 6 70 454 3
cert_coverFacet 4 426
cert_cover_5 4 2 0 2 4 6 138 426 2
cert_coverFacet 5 780
cert_cover_2 5 2 1 7 8 268 780 3
cert_coverFacet 6 308
cert_cover_2 6 3 1 4 7 52 308 3
cert_coverFacet 7 340
cert_cover_2 7 3 1 5 7 84 340 3
cert_coverFacet 8 804
cert_cover_2 8 4 1 7 8 292 804 3
cert_coverFacet 9 496
cert_cover_5 9 3 3 4 5 6 176 496 2
cert_coveringFacets_5
cert_coveringProof
cert_certificate 4 10
end Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0102

end
end BundlePart29

-- Public target certificates; internal witness data stays private.
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

public theorem projection_3963 : Certifies 3963 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0073.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3964 : Certifies 3964 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0074.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3965 : Certifies 3965 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0075.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3966 : Certifies 3966 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0076.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3967 : Certifies 3967 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0077.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3968 : Certifies 3968 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0078.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3969 : Certifies 3969 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0079.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3970 : Certifies 3970 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0080.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3971 : Certifies 3971 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0081.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3972 : Certifies 3972 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0082.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3973 : Certifies 3973 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0083.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3974 : Certifies 3974 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0084.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3975 : Certifies 3975 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0085.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3976 : Certifies 3976 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0086.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3977 : Certifies 3977 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0087.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3978 : Certifies 3978 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0088.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3979 : Certifies 3979 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0089.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3980 : Certifies 3980 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0090.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3981 : Certifies 3981 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0091.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3982 : Certifies 3982 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0092.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3983 : Certifies 3983 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0093.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3984 : Certifies 3984 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0094.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3985 : Certifies 3985 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0095.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3986 : Certifies 3986 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0096.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3987 : Certifies 3987 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0097.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3988 : Certifies 3988 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0098.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3989 : Certifies 3989 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0099.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3990 : Certifies 3990 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0100.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3991 : Certifies 3991 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0101.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem projection_3992 : Certifies 3992 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_m16e10q1_0102.certificate
  apply Boundary.ext_faces <;> decide +kernel

public theorem certified_B131 (j : Fin 30) :
    Certifies (3963 + j.val) := by
  fin_cases j
  · exact projection_3963
  · exact projection_3964
  · exact projection_3965
  · exact projection_3966
  · exact projection_3967
  · exact projection_3968
  · exact projection_3969
  · exact projection_3970
  · exact projection_3971
  · exact projection_3972
  · exact projection_3973
  · exact projection_3974
  · exact projection_3975
  · exact projection_3976
  · exact projection_3977
  · exact projection_3978
  · exact projection_3979
  · exact projection_3980
  · exact projection_3981
  · exact projection_3982
  · exact projection_3983
  · exact projection_3984
  · exact projection_3985
  · exact projection_3986
  · exact projection_3987
  · exact projection_3988
  · exact projection_3989
  · exact projection_3990
  · exact projection_3991
  · exact projection_3992

end Nonrational.TerminalVerification
-- Explicit facial frame witnesses, with lexical vector tracking.
